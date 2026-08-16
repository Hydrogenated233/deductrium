import { AST } from "./astparser.js";
import { Context } from "./core.js";
import { TTCoreCheckResult, TTCoreConfig } from "./engine.js";
import { TTDefinitionSlot } from "./core-session.js";
import { getTTProcessTransport, isTTProcessUnavailableError } from "./process-transport.js";

type WorkerResponse =
    | { id: number, ok: true, result?: TTCoreCheckResult }
    | { id: number, ok: false, error: string };

/** Promise API for the isolated type-theory process or Web Worker fallback. */
export class TTCoreWorkerClient {
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

    configure(config: TTCoreConfig, definitions: TTDefinitionSlot[] = []): Promise<void> {
        return this.request<void>({ kind: "configure", config, definitions });
    }

    truncate(startIndex: number): Promise<void> {
        return this.request<void>({ kind: "truncate", startIndex });
    }

    setDefinition(index: number, definition: TTDefinitionSlot): Promise<void> {
        return this.request<void>({ kind: "set-definition", index, definition });
    }

    /** Keep the process recovery snapshot aligned with a committed validate result. */
    rememberDefinition(index: number, definition: TTDefinitionSlot) {
        this.processTransport.rememberDefinition("core", index, definition);
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

    private async request<T>(message: object, timeout?: number): Promise<T> {
        if (this.disposed) throw new Error("Type-theory worker terminated");
        try {
            return await this.processTransport.request<T>("core", message, timeout);
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
                    this.restartWorker(new Error("Type-theory worker timed out"));
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
        if (typeof Worker === "undefined") throw new Error("Type-theory worker unavailable");
        const worker = new Worker(new URL("./core-worker.js", import.meta.url), { type: "module" });
        this.worker = worker;
        this.workerGeneration = Math.max(this.workerGeneration, this.processTransport.generation);
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
            this.restartWorker(new Error(event.message || "Type-theory worker failed"));
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
