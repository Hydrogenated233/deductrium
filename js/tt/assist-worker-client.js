export class TTAssistWorkerClient {
    worker;
    nextId = 1;
    disposed = false;
    workerGeneration = 0;
    pending = new Map();
    constructor() {
        this.createWorker();
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
    start(target, options, history = [], timeout) {
        return this.request({ kind: "start", target, options, history }, timeout);
    }
    apply(command, timeout) {
        return this.request({ kind: "apply", command }, timeout);
    }
    undo(timeout) {
        return this.request({ kind: "undo" }, timeout);
    }
    qed(timeout) {
        return this.request({ kind: "qed" }, timeout);
    }
    clear() {
        return this.request({ kind: "clear" });
    }
    terminate() {
        this.disposed = true;
        this.worker.terminate();
        this.rejectAll(new Error("Proof-assistant worker terminated"));
    }
    createWorker() {
        const worker = new Worker(new URL("./assist-worker.js", import.meta.url), { type: "module" });
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
            else {
                const error = new Error("error" in response ? response.error : "Proof-assistant worker failed");
                if ("operationError" in response && response.operationError)
                    error.operationError = true;
                pending.reject(error);
            }
        });
        worker.addEventListener("error", event => {
            if (worker !== this.worker)
                return;
            this.restart(new Error(event.message || "Proof-assistant worker failed"));
        });
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
                    this.restart(new Error("Proof-assistant worker timed out"));
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
//# sourceMappingURL=assist-worker-client.js.map