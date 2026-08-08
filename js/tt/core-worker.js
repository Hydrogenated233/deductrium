import { TTCoreSession } from "./core-session.js";
const session = new TTCoreSession();
globalThis.addEventListener("message", (event) => {
    const request = event.data;
    try {
        if (request.kind === "configure") {
            session.configure(request.config, request.definitions);
            globalThis.postMessage({ id: request.id, ok: true });
            return;
        }
        if (request.kind === "truncate") {
            session.truncate(request.startIndex);
            globalThis.postMessage({ id: request.id, ok: true });
            return;
        }
        if (request.kind === "set-definition") {
            session.setDefinition(request.index, request.definition);
            globalThis.postMessage({ id: request.id, ok: true });
            return;
        }
        if (request.kind === "validate") {
            const result = session.validate(request.index, request.ast, request.context);
            globalThis.postMessage({ id: request.id, ok: true, result });
            return;
        }
        globalThis.postMessage({
            id: request.id,
            ok: true,
            result: request.ast
                ? session.engine.checkAst(request.ast, request.context)
                : session.engine.check(request.input, request.context)
        });
    }
    catch (error) {
        globalThis.postMessage({ id: request.id, ok: false, error: String(error) });
    }
});
//# sourceMappingURL=core-worker.js.map