import {
    SandboxEnvironment,
    SandboxEnvironmentOptions,
    SandboxSave,
    SandboxValidationResult,
    SandboxCheckResult
} from "./sandbox.js";

export type SandboxWorkerRequest =
    | { id: number; kind: "load"; save: SandboxSave; options?: SandboxEnvironmentOptions }
    | { id: number; kind: "validate"; save: SandboxSave; options?: SandboxEnvironmentOptions }
    | { id: number; kind: "check"; source: string; options?: SandboxEnvironmentOptions }
    | { id: number; kind: "cancel"; requestId: number };

export type SandboxWorkerCancelResult = {
    cancelled: true;
    requestId: number;
};

function optionsKey(options: SandboxEnvironmentOptions | undefined) {
    return JSON.stringify({
        systemRuleIds: options?.systemRuleIds ?? null,
        semanticResourceScale: options?.semanticResourceScale ?? null,
        validationMaxDeclarations: options?.validationMaxDeclarations ?? null,
        validationMaxSourceChars: options?.validationMaxSourceChars ?? null,
        validationMaxNodes: options?.validationMaxNodes ?? null,
        validationMaxSteps: options?.validationMaxSteps ?? null,
        validationTimeoutMs: options?.validationTimeoutMs ?? null
    });
}

/** Stateful request owner shared by the browser Worker and deterministic Node tests. */
export class SandboxWorkerSession {
    private environment = new SandboxEnvironment();
    private environmentOptionsKey = optionsKey(undefined);
    private loaded = false;
    private readonly cancelledRequests = new Set<number>();

    cancel(requestId: number): SandboxWorkerCancelResult {
        const id = Number(requestId);
        if (Number.isFinite(id)) this.cancelledRequests.add(id);
        return { cancelled: true, requestId: id };
    }

    handle(request: SandboxWorkerRequest): SandboxValidationResult | SandboxCheckResult | SandboxWorkerCancelResult {
        if (request.kind === "cancel") return this.cancel(request.requestId);
        if (this.cancelledRequests.has(request.id)) {
            this.cancelledRequests.delete(request.id);
            throw new Error("沙盒验证已取消");
        }
        const current = this.getEnvironment(request.options);
        if (request.kind === "load" || request.kind === "validate") {
            try {
                const result = current.load(request.save, {
                    shouldCancel: () => this.cancelledRequests.has(request.id)
                });
                const publishedResult = result.status === "invalid"
                    ? {
                        ...result,
                        // The synchronous environment keeps its valid prefix
                        // for diagnostics, but a Worker result is a bridge
                        // publication boundary and must never carry it out.
                        bridge: {
                            axioms: [],
                            inductives: [],
                            definitions: [],
                            order: []
                        }
                    }
                    : result;
                // An invalid result is not a usable saved session, but keep a
                // fresh empty prelude environment available to direct callers
                // so `check` returns an explicit failure instead of exposing a
                // stale prefix. The browser client separately remains not-ready
                // until a complete `ok` validation result is received.
                this.loaded = result.status === "ok" || result.status === "invalid";
                if (result.status !== "ok") {
                    // Validation may have installed a prefix before it noticed
                    // cancellation or a budget limit.  Discard that partial
                    // Core instead of allowing a later request to reuse it.
                    this.environment = new SandboxEnvironment(request.options);
                    this.environmentOptionsKey = optionsKey(request.options);
                }
                return publishedResult;
            } catch (error) {
                // A malformed save or an unexpected validation exception must
                // not leave the previous environment addressable by a later
                // check request.  Keep the worker alive so the caller can
                // recover by supplying a fresh valid save.
                this.loaded = false;
                this.environment = new SandboxEnvironment(request.options);
                this.environmentOptionsKey = optionsKey(request.options);
                throw error;
            } finally {
                this.cancelledRequests.delete(request.id);
            }
        }
        if (!this.loaded) {
            throw new Error("沙盒 Worker 尚未加载存档，请先加载或校验");
        }
        return current.check(request.source);
    }

    private getEnvironment(options: SandboxEnvironmentOptions | undefined) {
        const key = optionsKey(options);
        if (key !== this.environmentOptionsKey) {
            this.environment = new SandboxEnvironment(options);
            this.environmentOptionsKey = key;
            this.loaded = false;
        }
        return this.environment;
    }
}

const session = new SandboxWorkerSession();

if (typeof globalThis.addEventListener === "function"
    && typeof globalThis.postMessage === "function") {
    globalThis.addEventListener("message", (event: MessageEvent<SandboxWorkerRequest>) => {
        const request = event.data;
        try {
            const result = session.handle(request);
            globalThis.postMessage({ id: request.id, ok: true, result });
        } catch (error) {
            globalThis.postMessage({ id: request.id, ok: false, error: String(error) });
        }
    });
}
