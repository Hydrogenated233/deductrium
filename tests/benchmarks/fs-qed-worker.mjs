import { parentPort } from "node:worker_threads";
import { expandInferenceSnapshot } from "../../js/fs/inference-worker-core.js";

parentPort.once("message", request => {
    try {
        parentPort.postMessage(expandInferenceSnapshot(request));
    } catch (error) {
        parentPort.postMessage({ error: String(error) });
    }
});
