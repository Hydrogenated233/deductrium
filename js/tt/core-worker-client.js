import { getTTProcessTransport, isTTProcessUnavailableError } from "./process-transport.js";
/** Promise API for the isolated type-theory process or Web Worker fallback. */
export class TTCoreWorkerClient {
    worker = null;
    nextId = 1;
    disposed = false;
    workerGeneration = 1;
    processTransport = getTTProcessTransport();
    pending = new Map();
    get generation() {
        return this.processTransport.workerFallbackSelected
            ? this.workerGeneration
            : this.processTransport.generation;
    }
    configure(config, definitions, loadedThrough) {
        return this.request({ kind: "configure", config, definitions, loadedThrough });
    }
    truncate(startIndex) {
        return this.request({ kind: "truncate", startIndex });
    }
    setDefinition(index, definition) {
        return this.request({ kind: "set-definition", index, definition });
    }
    /** Keep the process recovery snapshot aligned with a committed validate result. */
    rememberDefinition(index, definition) {
        this.processTransport.rememberDefinition("core", index, definition);
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
        this.worker?.terminate();
        this.worker = null;
        this.rejectAll(new Error("Type-theory worker terminated"));
    }
    /** Drop an in-flight validation chain and start with a fresh shared session. */
    reset() {
        if (this.processTransport.workerFallbackSelected) {
            this.restartWorker(new Error("Type-theory worker session reset"));
            return;
        }
        this.processTransport.reset(new Error("Type-theory process session reset"));
    }
    async request(message, timeout) {
        if (this.disposed)
            throw new Error("Type-theory worker terminated");
        try {
            return await this.processTransport.request("core", message, timeout);
        }
        catch (error) {
            if (!isTTProcessUnavailableError(error))
                throw error;
            return this.requestWorker(message, timeout);
        }
    }
    requestWorker(message, timeout) {
        const worker = this.ensureWorker();
        const id = this.nextId++;
        return new Promise((resolve, reject) => {
            const pending = { resolve, reject, timer: undefined };
            if (Number.isFinite(timeout)) {
                const wallTimeout = Math.min(Math.max(Number(timeout) + 250, 250), 2_147_000_000);
                pending.timer = window.setTimeout(() => {
                    if (!this.pending.has(id))
                        return;
                    this.restartWorker(new Error("Type-theory worker timed out"));
                }, wallTimeout);
            }
            this.pending.set(id, pending);
            try {
                worker.postMessage({ id, ...message });
            }
            catch (error) {
                this.pending.delete(id);
                if (pending.timer)
                    clearTimeout(pending.timer);
                reject(error);
            }
        });
    }
    ensureWorker() {
        if (this.worker)
            return this.worker;
        if (typeof Worker === "undefined")
            throw new Error("Type-theory worker unavailable");
        const worker = new Worker(new URL("./core-worker.js", import.meta.url), { type: "module" });
        this.worker = worker;
        this.workerGeneration = Math.max(this.workerGeneration, this.processTransport.generation);
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
            this.restartWorker(new Error(event.message || "Type-theory worker failed"));
        });
        return worker;
    }
    restartWorker(error) {
        this.worker?.terminate();
        this.worker = null;
        this.workerGeneration++;
        this.rejectAll(error);
        if (!this.disposed && this.processTransport.workerFallbackSelected)
            this.ensureWorker();
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