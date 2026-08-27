import { TTCoreSession } from "./core-session.js";
const session = new TTCoreSession();
globalThis.addEventListener("message", (event) => {
    const request = event.data;
    try {
        const { id, ...command } = request;
        const result = session.dispatch(command);
        globalThis.postMessage({ id, ok: true, result });
    }
    catch (error) {
        globalThis.postMessage({ id: request.id, ok: false, error: String(error) });
    }
});
//# sourceMappingURL=core-worker.js.map