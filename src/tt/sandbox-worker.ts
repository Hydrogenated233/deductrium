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
    | { id: number; kind: "check"; source: string; options?: SandboxEnvironmentOptions };

function optionsKey(options: SandboxEnvironmentOptions | undefined) {
    return JSON.stringify(options?.systemRuleIds ?? null);
}

/** Stateful request owner shared by the browser Worker and deterministic Node tests. */
export class SandboxWorkerSession {
    private environment = new SandboxEnvironment();
    private environmentOptionsKey = optionsKey(undefined);
    private loaded = false;

    handle(request: SandboxWorkerRequest): SandboxValidationResult | SandboxCheckResult {
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
