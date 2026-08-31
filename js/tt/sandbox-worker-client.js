/** Dedicated browser worker client for the isolated type-theory sandbox. */
export class SandboxWorkerClient {
    options;
    worker = null;
    nextId = 1;
    pending = new Map();
    sessionReady = false;
    sessionSaveKey = "";
    constructor(options = {}) {
        this.options = {
            ...options,
            systemRuleIds: options.systemRuleIds ? [...options.systemRuleIds] : undefined
        };
    }
    async load(save) {
        const result = await this.request({ kind: "load", save, options: this.options });
        this.sessionReady = true;
        this.sessionSaveKey = sandboxSaveKey(save);
        return result;
    }
    async validate(save) {
        const result = await this.request({ kind: "validate", save, options: this.options });
        this.sessionReady = true;
        this.sessionSaveKey = sandboxSaveKey(save);
        return result;
    }
    async check(saveOrSource, maybeSource) {
        const save = typeof saveOrSource === "string" ? undefined : saveOrSource;
        const source = typeof saveOrSource === "string" ? saveOrSource : String(maybeSource ?? "");
        this.ensureWorker();
        if (!this.sessionReady) {
            if (!save)
                throw new Error("沙盒 Worker 尚未加载存档，请先加载或校验");
            // Recovery after Worker termination/crash is explicit and happens
            // once for the new Worker, rather than before every check.
            await this.load(save);
        }
        else if (save && sandboxSaveKey(save) !== this.sessionSaveKey) {
            throw new Error("沙盒存档已变更，请先校验后再检查表达式");
        }
        return this.request({ kind: "check", source, options: this.options });
    }
    terminate() {
        this.worker?.terminate();
        this.worker = null;
        this.sessionReady = false;
        this.rejectAll(new Error("沙盒 Worker 已终止"));
    }
    request(message) {
        const worker = this.ensureWorker();
        const id = this.nextId++;
        return new Promise((resolve, reject) => {
            this.pending.set(id, { resolve, reject });
            try {
                worker.postMessage({ id, ...message });
            }
            catch (error) {
                this.pending.delete(id);
                reject(error instanceof Error ? error : new Error(String(error)));
            }
        });
    }
    ensureWorker() {
        if (this.worker)
            return this.worker;
        if (typeof Worker === "undefined")
            throw new Error("沙盒 Worker 不可用");
        const worker = new Worker(new URL("./sandbox-worker.js", import.meta.url), { type: "module" });
        this.worker = worker;
        this.sessionReady = false;
        worker.addEventListener("message", (event) => {
            const pending = this.pending.get(event.data.id);
            if (!pending)
                return;
            this.pending.delete(event.data.id);
            if (event.data.ok)
                pending.resolve(event.data.result);
            else
                pending.reject(new Error("error" in event.data ? event.data.error : "沙盒 Worker 失败"));
        });
        worker.addEventListener("error", event => {
            this.worker = null;
            this.sessionReady = false;
            this.rejectAll(new Error(event.message || "沙盒 Worker 失败"));
        });
        return worker;
    }
    rejectAll(error) {
        for (const pending of this.pending.values())
            pending.reject(error);
        this.pending.clear();
    }
}
function sandboxSaveKey(save) {
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
//# sourceMappingURL=sandbox-worker-client.js.map