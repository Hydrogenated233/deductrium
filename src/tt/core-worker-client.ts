import { AST } from "./astparser.js";
import { Context } from "./core.js";
import { TTCoreCheckResult, TTCoreConfig } from "./engine.js";
import { TTDefinitionSlot } from "./core-session.js";

type WorkerResponse =
    | { id: number, ok: true, result?: TTCoreCheckResult }
    | { id: number, ok: false, error: string };

/** Promise API for the dedicated type-theory Worker. */
export class TTCoreWorkerClient {
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

    private createWorker() {
        const worker = new Worker(new URL("./core-worker.js", import.meta.url), { type: "module" });
        this.worker = worker;
        this.workerGeneration++;
        worker.addEventListener("message", (event: MessageEvent<WorkerResponse>) => {
            const response = event.data;
            const pending = this.pending.get(response.id);
            if (!pending) return;
            this.pending.delete(response.id);
            if (pending.timer) clearTimeout(pending.timer);
            if (response.ok) pending.resolve(response.result);
            else pending.reject(new Error("error" in response ? response.error : "Type-theory worker failed"));
        });
        worker.addEventListener("error", event => {
            if (worker !== this.worker) return;
            this.restart(new Error(event.message || "Type-theory worker failed"));
        });
    }

    get generation() {
        return this.workerGeneration;
    }

    configure(config: TTCoreConfig, definitions: TTDefinitionSlot[] = []): Promise<void> {
        return this.request<void>({ kind: "configure", config, definitions });
    }

    truncate(startIndex: number): Promise<void> {
        return this.request<void>({ kind: "truncate", startIndex });
    }

    setDefinition(index: number, definition: TTDefinitionSlot): Promise<void> {
        return this.request<void>({ kind: "set-definition", index, definition });
    }

    check(input: string, context: Context = []): Promise<TTCoreCheckResult> {
        return this.request<TTCoreCheckResult>({ kind: "check", input, context });
    }

    checkAst(ast: AST, context: Context = []): Promise<TTCoreCheckResult> {
        return this.request<TTCoreCheckResult>({ kind: "check", ast, context });
    }

    validate(index: number, ast: AST, context: Context = [], timeout?: number): Promise<TTCoreCheckResult> {
        return this.request<TTCoreCheckResult>({ kind: "validate", index, ast, context }, timeout);
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

    private request<T>(message: object, timeout?: number): Promise<T> {
        const id = this.nextId++;
        return new Promise<T>((resolve, reject) => {
            const pending = { resolve, reject, timer: undefined as number };
            if (Number.isFinite(timeout)) {
                const wallTimeout = Math.min(Math.max(timeout + 250, 250), 2_147_000_000);
                pending.timer = window.setTimeout(() => {
                    if (!this.pending.has(id)) return;
                    this.restart(new Error("Type-theory worker timed out"));
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
