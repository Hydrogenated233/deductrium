import { AST } from "./astparser.js";
import {
    TTAssistOptions,
    TTAssistQedResult,
    TTAssistSnapshot
} from "./assist-engine.js";
import { TTCoreConfig } from "./engine.js";
import { TTDefinitionSlot } from "./core-session.js";
import { getTTProcessTransport, isTTProcessUnavailableError } from "./process-transport.js";

type WorkerResponse =
    | { id: number, ok: true, result?: TTAssistSnapshot | TTAssistQedResult }
    | { id: number, ok: false, error: string, operationError?: boolean };

export class TTAssistWorkerClient {
    private worker: Worker | null = null;
    private nextId = 1;
    private disposed = false;
    private workerGeneration = 1;
    private readonly processTransport = getTTProcessTransport();
    private readonly pending = new Map<number, {
        resolve: (value: any) => void,
        reject: (reason: Error) => void,
        timer?: number
    }>();

    get generation() {
        return this.processTransport.workerFallbackSelected
            ? this.workerGeneration
            : this.processTransport.generation;
    }

    configure(config: TTCoreConfig, definitions?: TTDefinitionSlot[], loadedThrough?: number) {
        return this.request<void>({ kind: "configure", config, definitions, loadedThrough });
    }

    truncate(startIndex: number) {
        return this.request<void>({ kind: "truncate", startIndex });
    }

    setDefinition(index: number, definition: TTDefinitionSlot) {
        return this.request<void>({ kind: "set-definition", index, definition });
    }

    start(target: AST | string, options: TTAssistOptions, history: string[] = [], timeout?: number) {
        return this.request<TTAssistSnapshot>({ kind: "start", target, options, history }, timeout);
    }

    apply(command: string, timeout?: number) {
        return this.request<TTAssistSnapshot>({ kind: "apply", command }, timeout);
    }

    undo(timeout?: number) {
        return this.request<TTAssistSnapshot>({ kind: "undo" }, timeout);
    }

    qed(timeout?: number) {
        return this.request<TTAssistQedResult>({ kind: "qed" }, timeout);
    }

    clear() {
        return this.request<void>({ kind: "clear" });
    }

    terminate() {
        this.disposed = true;
        this.worker?.terminate();
        this.worker = null;
        this.rejectAll(new Error("Proof-assistant worker terminated"));
    }

    private async request<T>(message: object, timeout?: number): Promise<T> {
        if (this.disposed) throw new Error("Proof-assistant worker terminated");
        try {
            return await this.processTransport.request<T>("assist", message, timeout);
        } catch (error) {
            if (!isTTProcessUnavailableError(error)) throw error;
            return this.requestWorker<T>(message, timeout);
        }
    }

    private requestWorker<T>(message: object, timeout?: number): Promise<T> {
        const worker = this.ensureWorker();
        const id = this.nextId++;
        return new Promise<T>((resolve, reject) => {
            const pending = { resolve, reject, timer: undefined as number };
            if (Number.isFinite(timeout)) {
                const wallTimeout = Math.min(Math.max(Number(timeout) + 250, 250), 2_147_000_000);
                pending.timer = window.setTimeout(() => {
                    if (!this.pending.has(id)) return;
                    this.restartWorker(new Error("Proof-assistant worker timed out"));
                }, wallTimeout);
            }
            this.pending.set(id, pending);
            try {
                worker.postMessage({ id, ...message });
            } catch (error) {
                this.pending.delete(id);
                if (pending.timer) clearTimeout(pending.timer);
                reject(error);
            }
        });
    }

    private ensureWorker() {
        if (this.worker) return this.worker;
        if (typeof Worker === "undefined") throw new Error("Proof-assistant worker unavailable");
        const worker = new Worker(new URL("./assist-worker.js", import.meta.url), { type: "module" });
        this.worker = worker;
        this.workerGeneration = Math.max(this.workerGeneration, this.processTransport.generation);
        worker.addEventListener("message", (event: MessageEvent<WorkerResponse>) => {
            const response = event.data;
            const pending = this.pending.get(response.id);
            if (!pending) return;
            this.pending.delete(response.id);
            if (pending.timer) clearTimeout(pending.timer);
            if (response.ok) pending.resolve(response.result);
            else {
                const error = new Error("error" in response ? response.error : "Proof-assistant worker failed");
                if ("operationError" in response && response.operationError) (error as any).operationError = true;
                pending.reject(error);
            }
        });
        worker.addEventListener("error", event => {
            if (worker !== this.worker) return;
            this.restartWorker(new Error(event.message || "Proof-assistant worker failed"));
        });
        return worker;
    }

    private restartWorker(error: Error) {
        this.worker?.terminate();
        this.worker = null;
        this.workerGeneration++;
        this.rejectAll(error);
        if (!this.disposed && this.processTransport.workerFallbackSelected) this.ensureWorker();
    }

    private rejectAll(error: Error) {
        for (const pending of this.pending.values()) {
            if (pending.timer) clearTimeout(pending.timer);
            pending.reject(error);
        }
        this.pending.clear();
    }
}
