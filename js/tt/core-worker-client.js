/** Promise API for the dedicated type-theory Worker. */
export class TTCoreWorkerClient {
    worker;
    nextId = 1;
    disposed = false;
    workerGeneration = 0;
    pending = new Map();
    constructor() {
        this.createWorker();
    }
    createWorker() {
        const worker = new Worker(new URL("./core-worker.js", import.meta.url), { type: "module" });
        this.worker = worker;
        this.workerGeneration++;
        worker.addEventListener("message", (event) => {
            const response = event.data;
            const pending = this.pending.get(response.id);
            if (!pending)
                return;
            this.pending.delete(response.id);
            if (pending.timer)
                clearTimeout(pending.timer);
            if (response.ok)
                pending.resolve(response.result);
            else
                pending.reject(new Error("error" in response ? response.error : "Type-theory worker failed"));
        });
        worker.addEventListener("error", event => {
            if (worker !== this.worker)
                return;
            this.restart(new Error(event.message || "Type-theory worker failed"));
        });
    }
    get generation() {
        return this.workerGeneration;
    }
    configure(config, definitions = []) {
        return this.request({ kind: "configure", config, definitions });
    }
    truncate(startIndex) {
        return this.request({ kind: "truncate", startIndex });
    }
    setDefinition(index, definition) {
        return this.request({ kind: "set-definition", index, definition });
    }
    check(input, context = []) {
        return this.request({ kind: "check", input, context });
    }
    checkAst(ast, context = []) {
        return this.request({ kind: "check", ast, context });
    }
    validate(index, ast, context = [], timeout) {
        return this.request({ kind: "validate", index, ast, context }, timeout);
    }
    terminate() {
        this.disposed = true;
        this.worker.terminate();
        this.rejectAll(new Error("Type-theory worker terminated"));
    }
    /** Drop an in-flight validation chain and start with a fresh session. */
    reset() {
        this.restart(new Error("Type-theory worker session reset"));
    }
    request(message, timeout) {
        const id = this.nextId++;
        return new Promise((resolve, reject) => {
            const pending = { resolve, reject, timer: undefined };
            if (Number.isFinite(timeout)) {
                const wallTimeout = Math.min(Math.max(timeout + 250, 250), 2_147_000_000);
                pending.timer = window.setTimeout(() => {
                    if (!this.pending.has(id))
                        return;
                    this.restart(new Error("Type-theory worker timed out"));
                }, wallTimeout);
            }
            this.pending.set(id, pending);
            try {
                this.worker.postMessage({ id, ...message });
            }
            catch (error) {
                this.pending.delete(id);
                if (pending.timer)
                    clearTimeout(pending.timer);
                reject(error);
            }
        });
    }
    restart(error) {
        this.worker?.terminate();
        this.rejectAll(error);
        if (!this.disposed)
            this.createWorker();
    }
    rejectAll(error) {
        for (const pending of this.pending.values()) {
            if (pending.timer)
                clearTimeout(pending.timer);
            pending.reject(error);
        }
        this.pending.clear();
    }
}
//# sourceMappingURL=core-worker-client.js.map