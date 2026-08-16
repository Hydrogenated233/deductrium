const SESSION_TIMEOUT = 20_000;
const MAX_TIMER = 2_147_000_000;
/** The local server did not expose the process API, so clients may use Web Workers. */
export class TTProcessUnavailableError extends Error {
}
/** An active process failed. Repeating the same check on the UI thread is unsafe. */
export class TTProcessExecutionError extends Error {
    preventSynchronousFallback = true;
    code;
    operationError;
    constructor(message, options = {}) {
        super(message);
        this.name = "TTProcessExecutionError";
        this.code = options.code;
        this.operationError = options.operationError;
    }
}
export function isTTProcessUnavailableError(error) {
    return error instanceof TTProcessUnavailableError;
}
/**
 * One browser page owns one Node process session. Core and proof-assistant
 * clients share it so a server restart invalidates both views at once.
 */
export class TTProcessTransport {
    mode = "undecided";
    sessionId = null;
    serverGeneration = null;
    anticipatedServerGeneration = null;
    visibleGeneration = 1;
    sessionPromise = null;
    resetPromise = Promise.resolve();
    recoveryPromise = null;
    replayPromise = null;
    configurations = new Map();
    channelQueues = {
        core: Promise.resolve(),
        assist: Promise.resolve()
    };
    channelEpochs = {
        core: 0,
        assist: 0
    };
    pending = new Set();
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
    rememberDefinition(channel, index, definition) {
        const state = this.configurations.get(channel);
        if (!state)
            return;
        this.rememberDefinitionState(state, index, definition, false);
    }
    rememberDefinitionState(state, index, definition, forceTruncate) {
        const target = Math.max(0, Math.floor(index));
        const stored = definition === null || definition === undefined
            ? null
            : JSON.stringify(definition);
        const previous = state.definitions[target];
        if (forceTruncate || stored !== null || previous !== null && previous !== undefined) {
            state.definitions.length = target + 1;
        }
        else if (state.definitions.length <= target) {
            state.definitions.length = target + 1;
        }
        state.definitions[target] = stored;
        state.revision++;
    }
    request(channel, request, timeout) {
        const epoch = this.channelEpochs[channel];
        const queued = this.channelQueues[channel]
            .catch(() => { })
            .then(() => {
            if (epoch !== this.channelEpochs[channel]) {
                throw new TTProcessExecutionError("Type-theory process request was cancelled", {
                    code: "TT_PROCESS_QUEUE_CANCELLED"
                });
            }
            return this.requestInOrder(channel, request, timeout);
        });
        this.channelQueues[channel] = queued.then(() => undefined, () => undefined);
        return queued;
    }
    async requestInOrder(channel, request, timeout) {
        // A configure request is the authoritative snapshot for a channel. It
        // is recorded only after it succeeds, so a failed first configure does
        // not poison a later recovery with a half-built state.
        const isConfiguration = requestKind(request) === "configure";
        let recovered = false;
        while (true) {
            try {
                await this.ensureSession();
                if (this.mode !== "process" || !this.sessionId) {
                    throw new TTProcessUnavailableError("Type-theory process API unavailable");
                }
                await this.resetPromise;
                if (!this.sessionId)
                    await this.ensureSession();
                if (!this.sessionId)
                    throw new TTProcessExecutionError("Type-theory process session unavailable");
                // Rebuild a restarted child before the first non-configure
                // operation. The current configure call itself is the rebuild
                // for its channel and must not be preceded by an old snapshot.
                await this.ensureConfigured(isConfiguration ? channel : undefined);
                const result = await this.requestOnce(channel, request, timeout);
                this.rememberSuccessfulRequest(channel, request, result);
                return result;
            }
            catch (error) {
                if (recovered || !this.shouldRecover(error))
                    throw error;
                recovered = true;
                await this.recoverSession(error);
            }
        }
    }
    async requestOnce(channel, request, timeout) {
        if (this.mode !== "process" || !this.sessionId) {
            throw new TTProcessUnavailableError("Type-theory process API unavailable");
        }
        const sessionId = this.sessionId;
        const controller = new AbortController();
        this.pending.add(controller);
        let timer;
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
            let body;
            try {
                body = JSON.stringify({
                    sessionId,
                    generation: this.serverGeneration ?? undefined,
                    channel,
                    request,
                    timeout
                });
            }
            catch (error) {
                throw new TTProcessExecutionError(`Unable to serialize type-theory request: ${error instanceof Error ? error.message : String(error)}`, { code: "TT_PROCESS_SERIALIZE_FAILED" });
            }
            const response = await fetch("/api/tt/rpc", {
                method: "POST",
                headers: { "Content-Type": "application/json" },
                body,
                cache: "no-store",
                signal: controller.signal
            });
            const result = await this.readJson(response);
            this.adoptServerGeneration(result?.generation);
            if (!response.ok || !result || result.ok !== true) {
                const executionError = new TTProcessExecutionError(result?.error || `Type-theory process request failed (${response.status})`, { code: result?.code, operationError: result?.operationError });
                if (result?.code === "TT_PROCESS_SESSION_NOT_FOUND") {
                    this.failSession(executionError, controller);
                }
                throw executionError;
            }
            return result.result;
        }
        catch (error) {
            if (error instanceof TTProcessExecutionError)
                throw error;
            if (controller.signal.aborted && controller.signal.reason instanceof Error) {
                throw controller.signal.reason;
            }
            const executionError = new TTProcessExecutionError(error instanceof Error ? error.message : String(error), { code: "TT_PROCESS_CONNECTION_FAILED" });
            this.failSession(executionError, controller);
            throw executionError;
        }
        finally {
            this.pending.delete(controller);
            if (timer !== undefined)
                clearTimeout(timer);
        }
    }
    shouldRecover(error) {
        if (!(error instanceof TTProcessExecutionError))
            return false;
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
    async recoverSession(error) {
        if (!this.recoveryPromise) {
            this.recoveryPromise = this.recoverSessionNow(error).finally(() => {
                this.recoveryPromise = null;
            });
        }
        await this.recoveryPromise;
    }
    async recoverSessionNow(error) {
        // A generation change means the server still owns the session but the
        // child state was lost. Reuse that session for process-level failures;
        // a missing/unreachable server session must be recreated instead.
        const canReuseSession = !!this.sessionId && (error.code === "TT_PROCESS_GENERATION_CHANGED"
            || error.code === "TT_PROCESS_EXITED"
            || error.code === "TT_PROCESS_IPC_FAILED");
        if (canReuseSession)
            this.invalidateConfigurations();
        else
            this.forgetSession();
        await this.ensureSession();
        await this.ensureConfigured();
    }
    async ensureConfigured(skipChannel) {
        if (this.serverGeneration === null || !this.configurations.size)
            return;
        const pending = [...this.configurations.entries()].filter(([channel, state]) => channel !== skipChannel && state.generation !== this.serverGeneration);
        if (!pending.length)
            return;
        if (this.replayPromise) {
            await this.replayPromise;
            return;
        }
        this.replayPromise = (async () => {
            // Use a fixed snapshot of the map so a concurrent configure can
            // replace a state without mutating the replay sequence in flight.
            for (const [channel, state] of pending) {
                const revision = state.revision;
                const configuration = parseReplayRequest(state.request);
                configuration.definitions = state.definitions.map(definition => definition === null ? null : JSON.parse(definition));
                await this.requestOnce(channel, configuration);
                if (channel === "assist" && state.assistStart) {
                    await this.requestOnce(channel, parseReplayRequest(state.assistStart));
                }
                // A local commit may race recovery (for example a validation
                // response arriving while a child is restarting). Leave that
                // channel dirty so the next request replays the newer snapshot.
                state.generation = state.revision === revision ? this.serverGeneration : null;
            }
        })().finally(() => {
            this.replayPromise = null;
        });
        await this.replayPromise;
    }
    rememberSuccessfulRequest(channel, request, result) {
        const kind = requestKind(request);
        if (kind === "configure") {
            const configuration = request;
            const definitions = Array.isArray(configuration.definitions)
                ? configuration.definitions
                : [];
            const replayRequest = { ...configuration, definitions: [] };
            this.configurations.set(channel, {
                request: serializeReplayRequest(replayRequest),
                generation: this.serverGeneration,
                definitions: definitions.map(definition => definition === null || definition === undefined ? null : JSON.stringify(definition)),
                assistStart: null,
                revision: 1
            });
            return;
        }
        const state = this.configurations.get(channel);
        if (!state)
            return;
        if (kind === "truncate") {
            const start = Number(request.startIndex);
            if (Number.isFinite(start)) {
                state.definitions.length = Math.min(state.definitions.length, Math.max(0, Math.floor(start)));
                state.revision++;
            }
            return;
        }
        if (kind === "set-definition") {
            const mutation = request;
            if (Number.isFinite(Number(mutation.index))) {
                this.rememberDefinition(channel, Number(mutation.index), mutation.definition);
            }
            return;
        }
        if (channel === "core" && kind === "validate") {
            const mutation = request;
            if (Number.isFinite(Number(mutation.index))) {
                this.rememberDefinitionState(state, Number(mutation.index), null, mutation.ast?.type === ":=");
            }
            return;
        }
        if (channel !== "assist")
            return;
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
            const history = result?.history;
            if (!Array.isArray(history) || !history.every(command => typeof command === "string"))
                return;
            const start = parseReplayRequest(state.assistStart);
            start.history = history.slice();
            state.assistStart = serializeReplayRequest(start);
            state.revision++;
        }
    }
    /** Invalidate both channels immediately, then restart the remote process. */
    reset(reason = new Error("Type-theory process session reset")) {
        const executionError = reason instanceof TTProcessExecutionError
            ? reason
            : new TTProcessExecutionError(reason.message, { code: "TT_PROCESS_RESET" });
        this.visibleGeneration++;
        this.cancelQueuedRequests(executionError);
        if (this.serverGeneration !== null) {
            this.anticipatedServerGeneration = this.serverGeneration + 1;
        }
        if (this.mode !== "process" || !this.sessionId)
            return;
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
                const result = await this.readJson(response);
                this.adoptServerGeneration(result?.generation);
                if (!response.ok || !result || result.ok !== true) {
                    if (result?.code === "TT_PROCESS_SESSION_NOT_FOUND")
                        this.forgetSession();
                    throw new Error(result?.error || "Unable to reset type-theory process");
                }
            }
            catch (error) {
                console.warn("Unable to reset type-theory process", error);
            }
        });
    }
    async ensureSession() {
        if (this.mode === "worker") {
            throw new TTProcessUnavailableError("Type-theory process API unavailable");
        }
        if (this.sessionId)
            return;
        if (!this.sessionPromise) {
            const initialProbe = this.mode === "undecided";
            this.sessionPromise = this.createSession(initialProbe).finally(() => {
                this.sessionPromise = null;
            });
        }
        await this.sessionPromise;
    }
    async createSession(initialProbe) {
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
            const result = await this.readJson(response);
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
        }
        catch (error) {
            if (error instanceof TTProcessUnavailableError || error instanceof TTProcessExecutionError) {
                throw error;
            }
            if (initialProbe) {
                this.mode = "worker";
                throw new TTProcessUnavailableError(error instanceof Error ? error.message : "Type-theory process API unavailable");
            }
            throw new TTProcessExecutionError(error instanceof Error ? error.message : String(error), { code: "TT_PROCESS_SESSION_FAILED" });
        }
        finally {
            clearTimeout(timer);
        }
    }
    adoptServerGeneration(generation) {
        if (!Number.isFinite(Number(generation)))
            return;
        const next = Number(generation);
        if (this.serverGeneration !== null && this.serverGeneration !== next) {
            if (this.anticipatedServerGeneration === next) {
                this.anticipatedServerGeneration = null;
            }
            else {
                this.visibleGeneration++;
            }
        }
        this.serverGeneration = next;
    }
    forgetSession() {
        if (!this.sessionId && this.serverGeneration === null)
            return;
        this.sessionId = null;
        this.serverGeneration = null;
        this.anticipatedServerGeneration = null;
        this.invalidateConfigurations();
        this.visibleGeneration++;
    }
    invalidateConfigurations() {
        for (const state of this.configurations.values())
            state.generation = null;
    }
    failSession(error, current) {
        this.forgetSession();
        for (const controller of this.pending) {
            if (controller !== current)
                controller.abort(error);
        }
    }
    cancelQueuedRequests(error) {
        this.channelEpochs.core++;
        this.channelEpochs.assist++;
        for (const controller of this.pending)
            controller.abort(error);
        this.pending.clear();
    }
    disposePageSession() {
        const sessionId = this.sessionId;
        this.cancelQueuedRequests(new TTProcessExecutionError("Type-theory process page session was disposed", { code: "TT_PROCESS_PAGE_DISPOSED" }));
        if (sessionId && typeof navigator !== "undefined" && typeof navigator.sendBeacon === "function") {
            const body = new Blob([JSON.stringify({ sessionId })], { type: "application/json" });
            navigator.sendBeacon("/api/tt/dispose", body);
        }
        this.forgetSession();
    }
    async readJson(response) {
        try {
            return await response.json();
        }
        catch {
            return null;
        }
    }
}
let pageTransport = null;
export function getTTProcessTransport() {
    return pageTransport ??= new TTProcessTransport();
}
function requestKind(request) {
    const kind = request.kind;
    return typeof kind === "string" ? kind : "";
}
function serializeReplayRequest(request) {
    return JSON.stringify(request);
}
function parseReplayRequest(request) {
    return JSON.parse(request);
}
//# sourceMappingURL=process-transport.js.map