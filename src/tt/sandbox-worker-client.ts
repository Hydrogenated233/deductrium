import {
    SandboxCheckResult,
    SandboxEnvironmentOptions,
    SandboxSave,
    sandboxValidationSemanticsKey,
    SandboxValidationResult
} from "./sandbox.js";

type SandboxRequest =
    | { kind: "load"; save: SandboxSave; options?: SandboxEnvironmentOptions }
    | { kind: "validate"; save: SandboxSave; options?: SandboxEnvironmentOptions }
    | { kind: "check"; source: string; options?: SandboxEnvironmentOptions };

type WorkerResponse =
    | { id: number; ok: true; result?: SandboxValidationResult | SandboxCheckResult }
    | { id: number; ok: false; error: string };

export class SandboxWorkerCancelledError extends Error {
    constructor(message = "沙盒验证已取消") {
        super(message);
        this.name = "SandboxWorkerCancelledError";
    }
}

export type SandboxWorkerRequestHandle<T> = {
    requestId: number;
    promise: Promise<T>;
    cancel: () => boolean;
};

type PendingRequest = {
    resolve: (value: any) => void;
    reject: (error: Error) => void;
};

/** Dedicated browser worker client for the isolated type-theory sandbox. */
export class SandboxWorkerClient {
    private readonly options: SandboxEnvironmentOptions;
    private worker: Worker | null = null;
    private nextId = 1;
    private pending = new Map<number, PendingRequest>();
    private sessionReady = false;
    private sessionSaveKey = "";

    constructor(options: SandboxEnvironmentOptions = {}) {
        this.options = {
            ...options,
            systemRuleIds: options.systemRuleIds ? [...options.systemRuleIds] : undefined
        };
    }

    async load(save: SandboxSave, signal?: AbortSignal) {
        const task = this.requestTask<SandboxValidationResult>({ kind: "load", save, options: this.options });
        let result: SandboxValidationResult;
        try {
            result = await this.awaitWithSignal(task, signal);
        } catch (error) {
            this.invalidateSession();
            throw error;
        }
        this.rememberValidationResult(result, save);
        return result;
    }

    async validate(save: SandboxSave, signal?: AbortSignal) {
        const task = this.requestTask<SandboxValidationResult>({ kind: "validate", save, options: this.options });
        let result: SandboxValidationResult;
        try {
            result = await this.awaitWithSignal(task, signal);
        } catch (error) {
            this.invalidateSession();
            throw error;
        }
        this.rememberValidationResult(result, save);
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
            const restored = await this.load(save);
            if (!this.sessionReady) {
                throw new Error(restored.error ?? "沙盒 Worker 校验未完成");
            }
        } else if (save && sandboxValidationSemanticsKey(save) !== this.sessionSaveKey) {
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

    /** Cancel one in-flight request and restart the worker to discard partial state. */
    cancel(requestId: number): boolean {
        const pending = this.pending.get(requestId);
        if (!pending) return false;
        this.pending.delete(requestId);
        const worker = this.worker;
        // Best effort protocol notification lets a non-browser session record
        // the cancellation; termination is the authoritative fallback because
        // a synchronous validation cannot service another message mid-call.
        try {
            worker?.postMessage({ id: this.nextId++, kind: "cancel", requestId });
        } catch { }
        worker?.terminate();
        this.worker = null;
        this.sessionReady = false;
        pending.reject(new SandboxWorkerCancelledError());
        this.rejectAll(new SandboxWorkerCancelledError());
        return true;
    }

    /** Start a validation and expose its request id for UI stop buttons. */
    validateRequest(save: SandboxSave, signal?: AbortSignal): SandboxWorkerRequestHandle<SandboxValidationResult> {
        const task = this.requestTask<SandboxValidationResult>({ kind: "validate", save, options: this.options });
        const promise = this.awaitWithSignal(task, signal).then(
            result => {
                this.rememberValidationResult(result, save);
                return result;
            },
            error => {
                // A rejected validation may follow a partially-mutated worker
                // session. Do not let a later check() reuse that stale state.
                this.invalidateSession();
                throw error;
            }
        );
        return { requestId: task.requestId, promise, cancel: task.cancel };
    }

    private request<T>(message: SandboxRequest): Promise<T> {
        return this.requestTask<T>(message).promise;
    }

    private requestTask<T>(message: SandboxRequest): SandboxWorkerRequestHandle<T> {
        const worker = this.ensureWorker();
        const id = this.nextId++;
        const promise = new Promise<T>((resolve, reject) => {
            this.pending.set(id, { resolve, reject });
            try {
                worker.postMessage({ id, ...message });
            } catch (error) {
                this.pending.delete(id);
                reject(error instanceof Error ? error : new Error(String(error)));
            }
        });
        return { requestId: id, promise, cancel: () => this.cancel(id) };
    }

    private async awaitWithSignal<T>(task: SandboxWorkerRequestHandle<T>, signal?: AbortSignal) {
        if (!signal) return task.promise;
        if (signal.aborted) {
            task.cancel();
            // Await the rejected task so callers receive the same cancellation
            // error without leaving an unhandled rejection behind.
            return await task.promise;
        }
        const onAbort = () => { task.cancel(); };
        signal.addEventListener("abort", onAbort, { once: true });
        try {
            return await task.promise;
        } finally {
            signal.removeEventListener("abort", onAbort);
        }
    }

    private rememberValidationResult(result: SandboxValidationResult, save: SandboxSave) {
        if (result.status === "cancelled" || result.status === "budget-exhausted") {
            this.invalidateSession();
            return;
        }
        this.sessionReady = true;
        this.sessionSaveKey = sandboxValidationSemanticsKey(save);
    }

    private invalidateSession() {
        this.sessionReady = false;
        this.sessionSaveKey = "";
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
