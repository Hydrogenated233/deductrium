import { SandboxEnvironment } from "./sandbox.js";
function optionsKey(options) {
    return JSON.stringify(options?.systemRuleIds ?? null);
}
/** Stateful request owner shared by the browser Worker and deterministic Node tests. */
export class SandboxWorkerSession {
    environment = new SandboxEnvironment();
    environmentOptionsKey = optionsKey(undefined);
    loaded = false;
    handle(request) {
        const current = this.getEnvironment(request.options);
        if (request.kind === "load" || request.kind === "validate") {
            const result = current.load(request.save);
            this.loaded = true;
            return result;
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