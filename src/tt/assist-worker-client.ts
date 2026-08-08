import { AST } from "./astparser.js";
import {
    TTAssistOptions,
    TTAssistQedResult,
    TTAssistSnapshot
} from "./assist-engine.js";
import { TTCoreConfig } from "./engine.js";
import { TTDefinitionSlot } from "./core-session.js";

type WorkerResponse =
    | { id: number, ok: true, result?: TTAssistSnapshot | TTAssistQedResult }
    | { id: number, ok: false, error: string, operationError?: boolean };

export class TTAssistWorkerClient {
    private worker: Worker;
    private nextId = 1;
    private disposed = false;
    private workerGeneration = 0;
    private readonly pending = new Map<number, {
        resolve: (value: any) => void,
        reject: (reason: Error) => void,
        timer?: number
    }>();

    constructor() {
        this.createWorker();
    }

    get generation() {
        return this.workerGeneration;
    }

    configure(config: TTCoreConfig, definitions: TTDefinitionSlot[] = []) {
        return this.request<void>({ kind: "configure", config, definitions });
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
        this.worker.terminate();
        this.rejectAll(new Error("Proof-assistant worker terminated"));
    }

    private createWorker() {
        const worker = new Worker(new URL("./assist-worker.js", import.meta.url), { type: "module" });
        this.worker = worker;
        this.workerGeneration++;
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
            this.restart(new Error(event.message || "Proof-assistant worker failed"));
        });
    }

    private request<T>(message: object, timeout?: number): Promise<T> {
        const id = this.nextId++;
        return new Promise<T>((resolve, reject) => {
            const pending = { resolve, reject, timer: undefined as number };
            if (Number.isFinite(timeout)) {
                const wallTimeout = Math.min(Math.max(timeout + 250, 250), 2_147_000_000);
                pending.timer = window.setTimeout(() => {
                    if (!this.pending.has(id)) return;
                    this.restart(new Error("Proof-assistant worker timed out"));
                }, wallTimeout);
            }
            this.pending.set(id, pending);
            try {
                this.worker.postMessage({ id, ...message });
            } catch (error) {
                this.pending.delete(id);
                if (pending.timer) clearTimeout(pending.timer);
                reject(error);
            }
        });
    }

    private restart(error: Error) {
        this.worker?.terminate();
        this.rejectAll(error);
        if (!this.disposed) this.createWorker();
    }

    private rejectAll(error: Error) {
        for (const pending of this.pending.values()) {
            if (pending.timer) clearTimeout(pending.timer);
            pending.reject(error);
        }
        this.pending.clear();
    }
}
