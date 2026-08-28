import { expandInferenceSnapshot } from "./inference-worker-core.js";
globalThis.addEventListener("message", (event) => {
    const request = event.data;
    try {
        if (request?.kind !== "expand")
            throw new Error("推理层 Worker 操作无效");
        const result = expandInferenceSnapshot(request.payload);
        globalThis.postMessage({ id: request.id, ok: true, result });
    }
    catch (error) {
        globalThis.postMessage({
            id: request?.id ?? 0,
            ok: false,
            error: error instanceof Error ? error.message : String(error)
        });
    }
});
//# sourceMappingURL=inference-worker.js.map