import {
    expandInferenceSnapshot,
    InferenceWorkerRequest,
    InferenceWorkerResult
} from "./inference-worker-core.js";

type Request = { id: number; kind: "expand"; payload: InferenceWorkerRequest };
type Response =
    | { id: number; ok: true; result: InferenceWorkerResult }
    | { id: number; ok: false; error: string };

globalThis.addEventListener("message", (event: MessageEvent<Request>) => {
    const request = event.data;
    try {
        if (request?.kind !== "expand") throw new Error("推理层 Worker 操作无效");
        const result = expandInferenceSnapshot(request.payload);
        globalThis.postMessage({ id: request.id, ok: true, result } satisfies Response);
    } catch (error) {
        globalThis.postMessage({
            id: request?.id ?? 0,
            ok: false,
            error: error instanceof Error ? error.message : String(error)
        } satisfies Response);
    }
});
