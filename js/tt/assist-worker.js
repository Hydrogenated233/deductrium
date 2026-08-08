import { TTAssistEngine } from "./assist-engine.js";
import { TTCoreSession } from "./core-session.js";
const definitions = new TTCoreSession();
const engine = new TTAssistEngine(definitions.engine);
globalThis.addEventListener("message", (event) => {
    const request = event.data;
    try {
        let result;
        if (request.kind === "configure") {
            definitions.configure(request.config, request.definitions);
            engine.clear();
        }
        else if (request.kind === "truncate") {
            definitions.truncate(request.startIndex);
            engine.clear();
        }
        else if (request.kind === "set-definition") {
            definitions.setDefinition(request.index, request.definition);
            engine.clear();
        }
        else if (request.kind === "start") {
            result = engine.start(request.target, request.options, request.history);
        }
        else if (request.kind === "apply") {
            result = engine.apply(request.command);
        }
        else if (request.kind === "undo") {
            result = engine.undo();
        }
        else if (request.kind === "qed") {
            result = engine.qed();
        }
        else {
            engine.clear();
        }
        globalThis.postMessage({ id: request.id, ok: true, result });
    }
    catch (error) {
        globalThis.postMessage({
            id: request.id,
            ok: false,
            error: String(error),
            operationError: request.kind === "apply" || request.kind === "qed"
        });
    }
});
//# sourceMappingURL=assist-worker.js.map