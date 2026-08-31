import {
    SandboxCheckResult,
    SandboxEnvironmentOptions,
    SandboxSave,
    SandboxValidationResult
} from "./sandbox.js";

type SandboxRequest =
    | { kind: "load"; save: SandboxSave; options?: SandboxEnvironmentOptions }
    | { kind: "validate"; save: SandboxSave; options?: SandboxEnvironmentOptions }
    | { kind: "check"; source: string; options?: SandboxEnvironmentOptions };

type WorkerResponse =
    | { id: number; ok: true; result?: SandboxValidationResult | SandboxCheckResult }
    | { id: number; ok: false; error: string };

/** Dedicated browser worker client for the isolated type-theory sandbox. */
export class SandboxWorkerClient {
    private readonly options: SandboxEnvironmentOptions;
    private worker: Worker | null = null;
    private nextId = 1;
    private pending = new Map<number, { resolve: (value: any) => void; reject: (error: Error) => void }>();
    private sessionReady = false;
    private sessionSaveKey = "";

    constructor(options: SandboxEnvironmentOptions = {}) {
        this.options = {
            ...options,
            systemRuleIds: options.systemRuleIds ? [...options.systemRuleIds] : undefined
        };
    }

    async load(save: SandboxSave) {
        const result = await this.request<SandboxValidationResult>({ kind: "load", save, options: this.options });
        this.sessionReady = true;
        this.sessionSaveKey = sandboxSaveKey(save);
        return result;
    }

    async validate(save: SandboxSave) {
        const result = await this.request<SandboxValidationResult>({ kind: "validate", save, options: this.options });
        this.sessionReady = true;
        this.sessionSaveKey = sandboxSaveKey(save);
        return result;
    }

    check(source: string): Promise<SandboxCheckResult>;
    check(save: SandboxSave, source: string): Promise<SandboxCheckResult>;
    async check(saveOrSource: SandboxSave | string, maybeSource?: string) {
        const save = typeof saveOrSource === "string" ? undefined : saveOrSource;
        const source = typeof saveOrSource === "string" ? saveOrSource : String(maybeSource ?? "");
        this.ensureWorker();
        if (!this.sessionReady) {
            if (!save) throw new Error("沙盒 Worker 尚未加载存档，请先加载或校验");
            // Recovery after Worker termination/crash is explicit and happens
            // once for the new Worker, rather than before every check.
            await this.load(save);
        } else if (save && sandboxSaveKey(save) !== this.sessionSaveKey) {
            throw new Error("沙盒存档已变更，请先校验后再检查表达式");
        }
        return this.request<SandboxCheckResult>({ kind: "check", source, options: this.options });
    }

    terminate() {
        this.worker?.terminate();
        this.worker = null;
        this.sessionReady = false;
        this.rejectAll(new Error("沙盒 Worker 已终止"));
    }

    private request<T>(message: SandboxRequest): Promise<T> {
        const worker = this.ensureWorker();
        const id = this.nextId++;
        return new Promise<T>((resolve, reject) => {
            this.pending.set(id, { resolve, reject });
            try {
                worker.postMessage({ id, ...message });
            } catch (error) {
                this.pending.delete(id);
                reject(error instanceof Error ? error : new Error(String(error)));
            }
        });
    }

    private ensureWorker() {
        if (this.worker) return this.worker;
        if (typeof Worker === "undefined") throw new Error("沙盒 Worker 不可用");
        const worker = new Worker(new URL("./sandbox-worker.js", import.meta.url), { type: "module" });
        this.worker = worker;
        this.sessionReady = false;
        worker.addEventListener("message", (event: MessageEvent<WorkerResponse>) => {
            const pending = this.pending.get(event.data.id);
            if (!pending) return;
            this.pending.delete(event.data.id);
            if (event.data.ok) pending.resolve(event.data.result);
            else pending.reject(new Error("error" in event.data ? event.data.error : "沙盒 Worker 失败"));
        });
        worker.addEventListener("error", event => {
            this.worker = null;
            this.sessionReady = false;
            this.rejectAll(new Error(event.message || "沙盒 Worker 失败"));
        });
        return worker;
    }

    private rejectAll(error: Error) {
        for (const pending of this.pending.values()) pending.reject(error);
        this.pending.clear();
    }
}

function sandboxSaveKey(save: SandboxSave) {
    return JSON.stringify({
        version: save.version,
        declarations: save.declarations.map(declaration => ({
            id: declaration.id,
            source: declaration.source,
            enabled: declaration.enabled,
            folderId: declaration.folderId
        })),
        folders: (save.folders ?? []).map(folder => ({
            id: folder.id,
            length: folder.length,
            disabled: folder.disabled
        })),
        order: save.order ?? []
    });
}
