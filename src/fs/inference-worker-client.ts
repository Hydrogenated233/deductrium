import {
    InferenceWorkerRequest,
    InferenceWorkerResult
} from "./inference-worker-core.js";

export type { InferenceWorkerRequest, InferenceWorkerResult, InferenceWorkerTarget } from "./inference-worker-core.js";

type WorkerResponse =
    | { id: number; ok: true; result: InferenceWorkerResult }
    | { id: number; ok: false; error: string };

export class InferenceWorkerClient {
    private worker: Worker | null = null;
    private nextId = 1;
    private readonly pending = new Map<number, {
        resolve: (result: InferenceWorkerResult) => void;
        reject: (error: Error) => void;
        timer: number;
    }>();

    expand(payload: InferenceWorkerRequest, timeout = 120_000): Promise<InferenceWorkerResult> {
        const worker = this.ensureWorker();
        const id = this.nextId++;
        return new Promise((resolve, reject) => {
            const timer = window.setTimeout(() => {
                this.restart(new Error("推理层 Worker 超时"));
            }, Math.max(250, timeout));
            this.pending.set(id, { resolve, reject, timer });
            try {
                worker.postMessage({ id, kind: "expand", payload });
            } catch (error) {
                window.clearTimeout(timer);
                this.pending.delete(id);
                reject(error instanceof Error ? error : new Error(String(error)));
            }
        });
    }

    terminate() {
        this.restart(new Error("推理层 Worker 已终止"), false);
    }

    private ensureWorker(): Worker {
        if (this.worker) return this.worker;
        if (typeof Worker === "undefined") throw new Error("推理层 Worker 不可用");
        const worker = new Worker(new URL("./inference-worker.js", import.meta.url), { type: "module" });
        this.worker = worker;
        worker.addEventListener("message", (event: MessageEvent<WorkerResponse>) => {
            const response = event.data;
            const pending = this.pending.get(response.id);
            if (!pending) return;
            this.pending.delete(response.id);
            window.clearTimeout(pending.timer);
            if (response.ok) pending.resolve(response.result);
            else pending.reject(new Error("error" in response ? response.error : "推理层 Worker 失败"));
        });
        worker.addEventListener("error", event => {
            if (worker !== this.worker) return;
            this.restart(new Error(event.message || "推理层 Worker 失败"));
        });
        return worker;
    }

    private restart(error: Error, recreate = true) {
        this.worker?.terminate();
        this.worker = null;
        for (const pending of this.pending.values()) {
            window.clearTimeout(pending.timer);
            pending.reject(error);
        }
        this.pending.clear();
        if (recreate && typeof Worker !== "undefined") this.ensureWorker();
    }
}
