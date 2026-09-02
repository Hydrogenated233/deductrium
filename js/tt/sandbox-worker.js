import { SandboxEnvironment } from "./sandbox.js";
function optionsKey(options) {
    return JSON.stringify({
        systemRuleIds: options?.systemRuleIds ?? null,
        semanticResourceScale: options?.semanticResourceScale ?? null,
        validationMaxDeclarations: options?.validationMaxDeclarations ?? null,
        validationMaxNodes: options?.validationMaxNodes ?? null,
        validationMaxSteps: options?.validationMaxSteps ?? null,
        validationTimeoutMs: options?.validationTimeoutMs ?? null
    });
}
/** Stateful request owner shared by the browser Worker and deterministic Node tests. */
export class SandboxWorkerSession {
    environment = new SandboxEnvironment();
    environmentOptionsKey = optionsKey(undefined);
    loaded = false;
    cancelledRequests = new Set();
    cancel(requestId) {
        const id = Number(requestId);
        if (Number.isFinite(id))
            this.cancelledRequests.add(id);
        return { cancelled: true, requestId: id };
    }
    handle(request) {
        if (request.kind === "cancel")
            return this.cancel(request.requestId);
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
                this.loaded = result.status !== "cancelled" && result.status !== "budget-exhausted";
                return result;
            }
            finally {
                this.cancelledRequests.delete(request.id);
            }
        }
        if (!this.loaded) {
            throw new Error("沙盒 Worker 尚未加载存档，请先加载或校验");
        }
        return current.check(request.source);
    }
    getEnvironment(options) {
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
    globalThis.addEventListener("message", (event) => {
        const request = event.data;
        try {
            const result = session.handle(request);
            globalThis.postMessage({ id: request.id, ok: true, result });
        }
        catch (error) {
            globalThis.postMessage({ id: request.id, ok: false, error: String(error) });
        }
    });
}
//# sourceMappingURL=sandbox-worker.js.map