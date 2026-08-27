import {
    cloneTTCoreSessionSnapshot,
    cloneTTDefinitionSlot,
    createTTCoreSessionSnapshot,
    type TTCoreSessionSnapshot
} from "./core-session-snapshot.js";

export type TTProcessChannel = "core" | "assist";

type TTProcessSessionResponse = {
    ok?: boolean;
    sessionId?: string;
    generation?: number;
    protocolVersion?: number;
    error?: string;
    code?: string;
};

type TTProcessRpcResponse<T> = {
    ok: boolean;
    result?: T;
    error?: string;
    operationError?: boolean;
    generation?: number;
    code?: string;
};

type TTProcessMode = "undecided" | "process" | "worker";

type TTProcessConfiguration = {
    /**
     * The core portion of recovery state. It is kept as an owned session
     * snapshot rather than a config JSON string plus a second definitions
     * array, so restores cannot accidentally replay stale embedded configs.
     */
    snapshot: TTCoreSessionSnapshot;
    generation: number | null;
    /** Proof tactics are intentionally separate from the shared definition state. */
    assistStart: string | null;
    revision: number;
};

const SESSION_TIMEOUT = 20_000;
const MAX_TIMER = 2_147_000_000;

/** The local server did not expose the process API, so clients may use Web Workers. */
export class TTProcessUnavailableError extends Error { }

/** An active process failed. Repeating the same check on the UI thread is unsafe. */
export class TTProcessExecutionError extends Error {
    readonly preventSynchronousFallback = true;
    readonly code?: string;
    readonly operationError?: boolean;

    constructor(message: string, options: { code?: string, operationError?: boolean } = {}) {
        super(message);
        this.name = "TTProcessExecutionError";
        this.code = options.code;
        this.operationError = options.operationError;
    }
}

export function isTTProcessUnavailableError(error: unknown): error is TTProcessUnavailableError {
    return error instanceof TTProcessUnavailableError;
}

/**
 * One browser page owns one Node process session. Core and proof-assistant
 * clients share it so a server restart invalidates both views at once.
 */
export class TTProcessTransport {
    private mode: TTProcessMode = "undecided";
    private sessionId: string | null = null;
    private serverGeneration: number | null = null;
    private anticipatedServerGeneration: number | null = null;
    private visibleGeneration = 1;
    private sessionPromise: Promise<void> | null = null;
    private sessionPromiseEpoch: number | null = null;
    private resetPromise: Promise<void> = Promise.resolve();
    private recoveryPromise: Promise<void> | null = null;
    private recoveryEpoch: number | null = null;
    private replayPromise: Promise<void> | null = null;
    private replayEpoch: number | null = null;
    private lifecycleEpoch = 0;
    private readonly configurations = new Map<TTProcessChannel, TTProcessConfiguration>();
    private readonly channelQueues: Record<TTProcessChannel, Promise<void>> = {
        core: Promise.resolve(),
        assist: Promise.resolve()
    };
    private readonly channelEpochs: Record<TTProcessChannel, number> = {
        core: 0,
        assist: 0
    };
    private readonly pending = new Set<AbortController>();

    constructor() {
        if (typeof window !== "undefined" && typeof window.addEventListener === "function") {
            window.addEventListener("pagehide", () => this.disposePageSession());
        }
    }

    get generation() {
        return this.visibleGeneration;
    }

    get processSelected() {
        return this.mode === "process";
    }

    get workerFallbackSelected() {
        return this.mode === "worker";
    }

    /** Update the local recovery snapshot after a Worker-committed definition. */
    rememberDefinition(channel: TTProcessChannel, index: number, definition: unknown) {
        const state = this.configurations.get(channel);
        if (!state) return;
        this.rememberDefinitionState(state, index, definition, false);
    }

    private rememberDefinitionState(
        state: TTProcessConfiguration,
        index: number,
        definition: unknown,
        forceTruncate: boolean
    ) {
        const target = Math.max(0, Math.floor(index));
        const stored = definition === null || definition === undefined
            ? null
            : cloneTTDefinitionSlot(definition as TTCoreSessionSnapshot["definitions"][number]);
        const previous = state.snapshot.definitions[target];
        if (forceTruncate || stored !== null || previous !== null && previous !== undefined) {
            state.snapshot.definitions.length = target + 1;
        } else if (state.snapshot.definitions.length <= target) {
            state.snapshot.definitions.length = target + 1;
        }
        state.snapshot.definitions[target] = stored;
        state.snapshot.loadedThrough = target + 1;
        state.revision++;
    }

    request<T>(channel: TTProcessChannel, request: object, timeout?: number): Promise<T> {
        const channelEpoch = this.channelEpochs[channel];
        const lifecycleEpoch = this.lifecycleEpoch;
        const queued = this.channelQueues[channel]
            .catch(() => { })
            .then(() => {
                this.assertRequestCurrent(channel, channelEpoch, lifecycleEpoch);
                return this.requestInOrder<T>(channel, request, timeout, channelEpoch, lifecycleEpoch);
            });
        this.channelQueues[channel] = queued.then(() => undefined, () => undefined);
        return queued;
    }

    private async requestInOrder<T>(
        channel: TTProcessChannel,
        request: object,
        timeout: number | undefined,
        channelEpoch: number,
        lifecycleEpoch: number
    ): Promise<T> {
        // A configure request is the authoritative snapshot for a channel. It
        // is recorded only after it succeeds, so a failed first configure does
        // not poison a later recovery with a half-built state.
        const isConfiguration = requestKind(request) === "configure";
        const assertCurrent = () => this.assertRequestCurrent(channel, channelEpoch, lifecycleEpoch);
        let recovered = false;
        while (true) {
            try {
                assertCurrent();
                await this.ensureSession(lifecycleEpoch);
                assertCurrent();
                if (this.mode !== "process" || !this.sessionId) {
                    throw new TTProcessUnavailableError("Type-theory process API unavailable");
                }
                await this.resetPromise;
                assertCurrent();
                if (!this.sessionId) {
                    await this.ensureSession(lifecycleEpoch);
                    assertCurrent();
                }
                if (!this.sessionId) throw new TTProcessExecutionError("Type-theory process session unavailable");

                // Rebuild a restarted child before the first non-configure
                // operation. The current configure call itself is the rebuild
                // for its channel and must not be preceded by an old snapshot.
                await this.ensureConfigured(isConfiguration ? channel : undefined, lifecycleEpoch, assertCurrent);
                assertCurrent();
                const result = await this.requestOnce<T>(channel, request, timeout);
                assertCurrent();
                this.rememberSuccessfulRequest(channel, request, result);
                return result;
            } catch (error) {
                // A request timeout deliberately resets the remote process so
                // later queued work is cancelled. The request which caused
                // that reset must still surface its timeout to the UI; calling
                // assertCurrent first would replace it with queue-cancelled.
                if (error instanceof TTProcessExecutionError && error.code === "TT_PROCESS_TIMEOUT") {
                    throw error;
                }
                assertCurrent();
                if (recovered || !this.shouldRecover(error)) throw error;
                recovered = true;
                await this.recoverSession(error, lifecycleEpoch, assertCurrent);
                assertCurrent();
            }
        }
    }

    private async requestOnce<T>(channel: TTProcessChannel, request: object, timeout?: number): Promise<T> {
        if (this.mode !== "process" || !this.sessionId) {
            throw new TTProcessUnavailableError("Type-theory process API unavailable");
        }

        const sessionId = this.sessionId;
        const controller = new AbortController();
        this.pending.add(controller);
        let timer: number | undefined;
        if (Number.isFinite(timeout)) {
            const wallTimeout = Math.min(Math.max(Number(timeout) + 750, 750), MAX_TIMER);
            timer = setTimeout(() => {
                const error = new TTProcessExecutionError("Type-theory process timed out", {
                    code: "TT_PROCESS_TIMEOUT"
                });
                controller.abort(error);
                this.reset(error);
            }, wallTimeout);
        }

        try {
            let body: string;
            try {
                body = JSON.stringify({
                    sessionId,
                    generation: this.serverGeneration ?? undefined,
                    channel,
                    request,
                    timeout
                });
            } catch (error) {
                throw new TTProcessExecutionError(
                    `Unable to serialize type-theory request: ${error instanceof Error ? error.message : String(error)}`,
                    { code: "TT_PROCESS_SERIALIZE_FAILED" }
                );
            }
            const response = await fetch("/api/tt/rpc", {
                method: "POST",
                headers: { "Content-Type": "application/json" },
                body,
                cache: "no-store",
                signal: controller.signal
            });
            const result = await this.readJson<TTProcessRpcResponse<T>>(response);
            this.adoptServerGeneration(result?.generation);
            if (!response.ok || !result || result.ok !== true) {
                const executionError = new TTProcessExecutionError(
                    result?.error || `Type-theory process request failed (${response.status})`,
                    { code: result?.code, operationError: result?.operationError }
                );
                if (result?.code === "TT_PROCESS_SESSION_NOT_FOUND") {
                    this.failSession(executionError, controller);
                }
                throw executionError;
            }
            return result.result as T;
        } catch (error) {
            if (error instanceof TTProcessExecutionError) throw error;
            if (controller.signal.aborted && controller.signal.reason instanceof Error) {
                throw controller.signal.reason;
            }
            const executionError = new TTProcessExecutionError(
                error instanceof Error ? error.message : String(error),
                { code: "TT_PROCESS_CONNECTION_FAILED" }
            );
            this.failSession(executionError, controller);
            throw executionError;
        } finally {
            this.pending.delete(controller);
            if (timer !== undefined) clearTimeout(timer);
        }
    }

    private shouldRecover(error: unknown) {
        if (!(error instanceof TTProcessExecutionError)) return false;
        switch (error.code) {
            case "TT_PROCESS_SESSION_NOT_FOUND":
            case "TT_PROCESS_GENERATION_CHANGED":
            case "TT_PROCESS_CONNECTION_FAILED":
            case "TT_PROCESS_SESSION_FAILED":
            case "TT_PROCESS_EXITED":
            case "TT_PROCESS_IPC_FAILED":
                return true;
            default:
                return false;
        }
    }

    private async recoverSession(
        error: TTProcessExecutionError,
        lifecycleEpoch: number,
        assertCurrent: () => void
    ) {
        if (this.recoveryPromise && this.recoveryEpoch !== lifecycleEpoch) {
            try {
                await this.recoveryPromise;
            } catch {
                // The stale recovery belongs to an invalidated lifecycle.
            }
            assertCurrent();
        }
        if (!this.recoveryPromise) {
            this.recoveryEpoch = lifecycleEpoch;
            const recovery = this.recoverSessionNow(error, lifecycleEpoch, assertCurrent);
            const tracked = recovery.finally(() => {
                if (this.recoveryPromise !== tracked) return;
                this.recoveryPromise = null;
                this.recoveryEpoch = null;
            });
            this.recoveryPromise = tracked;
        }
        await this.recoveryPromise;
        assertCurrent();
    }

    private async recoverSessionNow(
        error: TTProcessExecutionError,
        lifecycleEpoch: number,
        assertCurrent: () => void
    ) {
        assertCurrent();
        // A generation change means the server still owns the session but the
        // child state was lost. Reuse that session for process-level failures;
        // a missing/unreachable server session must be recreated instead.
        const canReuseSession = !!this.sessionId && (
            error.code === "TT_PROCESS_GENERATION_CHANGED"
            || error.code === "TT_PROCESS_EXITED"
            || error.code === "TT_PROCESS_IPC_FAILED"
        );
        if (canReuseSession) this.invalidateConfigurations();
        else this.forgetSession();
        await this.ensureSession(lifecycleEpoch);
        assertCurrent();
        await this.ensureConfigured(undefined, lifecycleEpoch, assertCurrent);
        assertCurrent();
    }

    private async ensureConfigured(
        skipChannel: TTProcessChannel | undefined,
        lifecycleEpoch: number,
        assertCurrent: () => void
    ) {
        assertCurrent();
        if (this.serverGeneration === null || !this.configurations.size) return;
        const pending = [...this.configurations.entries()].filter(([channel, state]) =>
            channel !== skipChannel && state.generation !== this.serverGeneration
        );
        if (!pending.length) return;
        if (this.replayPromise) {
            if (this.replayEpoch === lifecycleEpoch) {
                await this.replayPromise;
                assertCurrent();
                return;
            }
            try {
                await this.replayPromise;
            } catch {
                // The stale replay belongs to an invalidated lifecycle.
            }
            assertCurrent();
            return this.ensureConfigured(skipChannel, lifecycleEpoch, assertCurrent);
        }
        this.replayEpoch = lifecycleEpoch;
        const replay = (async () => {
            // Use a fixed snapshot of the map so a concurrent configure can
            // replace a state without mutating the replay sequence in flight.
            for (const [channel, state] of pending) {
                assertCurrent();
                const revision = state.revision;
                const snapshot = cloneTTCoreSessionSnapshot(state.snapshot);
                const configuration = {
                    kind: "configure",
                    config: snapshot.config,
                    definitions: snapshot.definitions,
                    loadedThrough: snapshot.loadedThrough
                };
                await this.requestOnce(channel, configuration);
                assertCurrent();
                if (channel === "assist" && state.assistStart) {
                    await this.requestOnce(channel, parseReplayRequest(state.assistStart));
                    assertCurrent();
                }
                // A local commit may race recovery (for example a validation
                // response arriving while a child is restarting). Leave that
                // channel dirty so the next request replays the newer snapshot.
                state.generation = state.revision === revision ? this.serverGeneration : null;
            }
        })();
        const tracked = replay.finally(() => {
            if (this.replayPromise !== tracked) return;
            this.replayPromise = null;
            this.replayEpoch = null;
        });
        this.replayPromise = tracked;
        await tracked;
        assertCurrent();
    }

    private rememberSuccessfulRequest(channel: TTProcessChannel, request: object, result: unknown) {
        const kind = requestKind(request);
        if (kind === "configure") {
            const configuration = request as {
                config: TTCoreSessionSnapshot["config"];
                definitions?: TTCoreSessionSnapshot["definitions"];
                loadedThrough?: unknown;
            };
            const definitions = Array.isArray(configuration.definitions)
                ? configuration.definitions
                : undefined;
            this.configurations.set(channel, {
                snapshot: createTTCoreSessionSnapshot(
                    configuration.config,
                    definitions,
                    configuration.loadedThrough as number | undefined
                ),
                generation: this.serverGeneration,
                assistStart: null,
                revision: 1
            });
            return;
        }

        const state = this.configurations.get(channel);
        if (!state) return;
        if (kind === "truncate") {
            const start = Number((request as { startIndex?: unknown }).startIndex);
            if (Number.isFinite(start)) {
                state.snapshot.definitions.length = Math.min(
                    state.snapshot.definitions.length,
                    Math.max(0, Math.floor(start))
                );
                state.snapshot.loadedThrough = Math.min(
                    state.snapshot.loadedThrough,
                    state.snapshot.definitions.length
                );
                state.revision++;
            }
            return;
        }
        if (kind === "set-definition") {
            const mutation = request as { index?: unknown, definition?: unknown };
            if (Number.isFinite(Number(mutation.index))) {
                this.rememberDefinition(channel, Number(mutation.index), mutation.definition);
            }
            return;
        }
        if (channel === "core" && kind === "validate") {
            const mutation = request as { index?: unknown, ast?: { type?: unknown } };
            if (Number.isFinite(Number(mutation.index))) {
                this.rememberDefinitionState(
                    state,
                    Number(mutation.index),
                    null,
                    mutation.ast?.type === ":="
                );
            }
            return;
        }
        if (channel !== "assist") return;
        if (kind === "start") {
            state.assistStart = serializeReplayRequest(request);
            state.revision++;
            return;
        }
        if (kind === "clear" || kind === "qed") {
            state.assistStart = null;
            state.revision++;
            return;
        }
        if ((kind === "apply" || kind === "undo") && state.assistStart) {
            const history = (result as { history?: unknown })?.history;
            if (!Array.isArray(history) || !history.every(command => typeof command === "string")) return;
            const start = parseReplayRequest(state.assistStart) as { history?: string[] };
            start.history = history.slice();
            state.assistStart = serializeReplayRequest(start);
            state.revision++;
        }
    }

    /** Invalidate both channels immediately, then restart the remote process. */
    reset(reason: Error = new Error("Type-theory process session reset")) {
        const executionError = reason instanceof TTProcessExecutionError
            ? reason
            : new TTProcessExecutionError(reason.message, { code: "TT_PROCESS_RESET" });
        this.visibleGeneration++;
        this.cancelQueuedRequests(executionError);
        if (this.serverGeneration !== null) {
            this.anticipatedServerGeneration = this.serverGeneration + 1;
        }

        if (this.mode !== "process" || !this.sessionId) return;
        const sessionId = this.sessionId;
        const generation = this.serverGeneration;
        this.resetPromise = this.resetPromise.catch(() => { }).then(async () => {
            try {
                const response = await fetch("/api/tt/reset", {
                    method: "POST",
                    headers: { "Content-Type": "application/json" },
                    body: JSON.stringify({ sessionId, generation }),
                    cache: "no-store"
                });
                const result = await this.readJson<TTProcessRpcResponse<void>>(response);
                this.adoptServerGeneration(result?.generation);
                if (!response.ok || !result || result.ok !== true) {
                    if (result?.code === "TT_PROCESS_SESSION_NOT_FOUND") this.forgetSession();
                    throw new Error(result?.error || "Unable to reset type-theory process");
                }
            } catch (error) {
                console.warn("Unable to reset type-theory process", error);
            }
        });
    }

    private async ensureSession(lifecycleEpoch: number) {
        this.assertLifecycleCurrent(lifecycleEpoch);
        if (this.mode === "worker") {
            throw new TTProcessUnavailableError("Type-theory process API unavailable");
        }
        if (this.sessionId) return;
        if (!this.sessionPromise || this.sessionPromiseEpoch !== lifecycleEpoch) {
            const initialProbe = this.mode === "undecided";
            this.sessionPromiseEpoch = lifecycleEpoch;
            const creation = this.createSession(initialProbe, lifecycleEpoch);
            const tracked = creation.finally(() => {
                if (this.sessionPromise !== tracked) return;
                this.sessionPromise = null;
                this.sessionPromiseEpoch = null;
            });
            this.sessionPromise = tracked;
        }
        await this.sessionPromise;
        this.assertLifecycleCurrent(lifecycleEpoch);
    }

    private async createSession(initialProbe: boolean, lifecycleEpoch: number) {
        this.assertLifecycleCurrent(lifecycleEpoch);
        const controller = new AbortController();
        const timer = setTimeout(() => controller.abort(), SESSION_TIMEOUT);
        try {
            const response = await fetch("/api/tt/session", {
                method: "POST",
                headers: { "Content-Type": "application/json" },
                body: "{}",
                cache: "no-store",
                signal: controller.signal
            });
            const result = await this.readJson<TTProcessSessionResponse>(response);
            if (lifecycleEpoch !== this.lifecycleEpoch) {
                if (result?.sessionId) await this.disposeCreatedSession(result.sessionId);
                this.assertLifecycleCurrent(lifecycleEpoch);
            }
            if (!response.ok || !result?.sessionId || result.ok === false) {
                const message = result?.error || `Type-theory process API unavailable (${response.status})`;
                const recognizedProcessApi = result?.code?.startsWith("TT_PROCESS_")
                    || Number.isFinite(Number(result?.protocolVersion));
                if (initialProbe && (!recognizedProcessApi || result?.code === "TT_PROCESS_LOCAL_ONLY")) {
                    this.mode = "worker";
                    throw new TTProcessUnavailableError(message);
                }
                this.mode = "process";
                throw new TTProcessExecutionError(message, { code: result?.code });
            }
            this.mode = "process";
            this.sessionId = result.sessionId;
            this.adoptServerGeneration(result.generation);
        } catch (error) {
            this.assertLifecycleCurrent(lifecycleEpoch);
            if (error instanceof TTProcessUnavailableError || error instanceof TTProcessExecutionError) {
                throw error;
            }
            if (initialProbe) {
                this.mode = "worker";
                throw new TTProcessUnavailableError(
                    error instanceof Error ? error.message : "Type-theory process API unavailable"
                );
            }
            throw new TTProcessExecutionError(
                error instanceof Error ? error.message : String(error),
                { code: "TT_PROCESS_SESSION_FAILED" }
            );
        } finally {
            clearTimeout(timer);
        }
    }

    private async disposeCreatedSession(sessionId: string) {
        const body = JSON.stringify({ sessionId });
        try {
            if (typeof navigator !== "undefined" && typeof navigator.sendBeacon === "function") {
                const sent = navigator.sendBeacon(
                    "/api/tt/dispose",
                    new Blob([body], { type: "application/json" })
                );
                if (sent) return;
            }
            await fetch("/api/tt/dispose", {
                method: "POST",
                headers: { "Content-Type": "application/json" },
                body,
                cache: "no-store",
                keepalive: true
            });
        } catch {
            // The server also expires abandoned sessions; disposal is best effort.
        }
    }

    private adoptServerGeneration(generation: unknown) {
        if (!Number.isFinite(Number(generation))) return;
        const next = Number(generation);
        if (this.serverGeneration !== null && this.serverGeneration !== next) {
            if (this.anticipatedServerGeneration === next) {
                this.anticipatedServerGeneration = null;
            } else {
                this.visibleGeneration++;
            }
        }
        this.serverGeneration = next;
    }

    private forgetSession() {
        if (!this.sessionId && this.serverGeneration === null) return;
        this.sessionId = null;
        this.serverGeneration = null;
        this.anticipatedServerGeneration = null;
        this.invalidateConfigurations();
        this.visibleGeneration++;
    }

    private invalidateConfigurations() {
        for (const state of this.configurations.values()) state.generation = null;
    }

    private failSession(error: TTProcessExecutionError, current: AbortController) {
        this.forgetSession();
        for (const controller of this.pending) {
            if (controller !== current) controller.abort(error);
        }
    }

    private cancelQueuedRequests(error: TTProcessExecutionError) {
        this.lifecycleEpoch++;
        this.channelEpochs.core++;
        this.channelEpochs.assist++;
        for (const controller of this.pending) controller.abort(error);
        this.pending.clear();
    }

    private assertRequestCurrent(
        channel: TTProcessChannel,
        channelEpoch: number,
        lifecycleEpoch: number
    ) {
        if (channelEpoch !== this.channelEpochs[channel] || lifecycleEpoch !== this.lifecycleEpoch) {
            throw new TTProcessExecutionError("Type-theory process request was cancelled", {
                code: "TT_PROCESS_QUEUE_CANCELLED"
            });
        }
    }

    private assertLifecycleCurrent(lifecycleEpoch: number) {
        if (lifecycleEpoch !== this.lifecycleEpoch) {
            throw new TTProcessExecutionError("Type-theory process request was cancelled", {
                code: "TT_PROCESS_QUEUE_CANCELLED"
            });
        }
    }

    private disposePageSession() {
        const sessionId = this.sessionId;
        this.cancelQueuedRequests(new TTProcessExecutionError(
            "Type-theory process page session was disposed",
            { code: "TT_PROCESS_PAGE_DISPOSED" }
        ));
        if (sessionId && typeof navigator !== "undefined" && typeof navigator.sendBeacon === "function") {
            const body = new Blob([JSON.stringify({ sessionId })], { type: "application/json" });
            navigator.sendBeacon("/api/tt/dispose", body);
        }
        this.forgetSession();
    }

    private async readJson<T>(response: Response): Promise<T | null> {
        try {
            return await response.json() as T;
        } catch {
            return null;
        }
    }
}

let pageTransport: TTProcessTransport | null = null;

export function getTTProcessTransport() {
    return pageTransport ??= new TTProcessTransport();
}

function requestKind(request: object) {
    const kind = (request as { kind?: unknown }).kind;
    return typeof kind === "string" ? kind : "";
}

function serializeReplayRequest(request: object) {
    return JSON.stringify(request);
}

function parseReplayRequest(request: string): object {
    return JSON.parse(request) as object;
}
