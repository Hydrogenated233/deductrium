import { AST } from "./astparser.js";
import { Context } from "./core.js";
import { TTCoreCheckResult, TTCoreConfig } from "./engine.js";
import { TTCoreSession, TTDefinitionSlot } from "./core-session.js";

type Request =
    | { id: number, kind: "configure", config: TTCoreConfig, definitions?: TTDefinitionSlot[] }
    | { id: number, kind: "truncate", startIndex: number }
    | { id: number, kind: "set-definition", index: number, definition: TTDefinitionSlot }
    | { id: number, kind: "check", input?: string, ast?: AST, context?: Context }
    | { id: number, kind: "validate", index: number, ast: AST, context?: Context };
type Response =
    | { id: number, ok: true, result?: TTCoreCheckResult }
    | { id: number, ok: false, error: string };

const session = new TTCoreSession();

globalThis.addEventListener("message", (event: MessageEvent<Request>) => {
    const request = event.data;
    try {
        if (request.kind === "configure") {
            session.configure(request.config, request.definitions);
            globalThis.postMessage({ id: request.id, ok: true } satisfies Response);
            return;
        }
        if (request.kind === "truncate") {
            session.truncate(request.startIndex);
            globalThis.postMessage({ id: request.id, ok: true } satisfies Response);
            return;
        }
        if (request.kind === "set-definition") {
            session.setDefinition(request.index, request.definition);
            globalThis.postMessage({ id: request.id, ok: true } satisfies Response);
            return;
        }
        if (request.kind === "validate") {
            const result = session.validate(request.index, request.ast, request.context);
            globalThis.postMessage({ id: request.id, ok: true, result } satisfies Response);
            return;
        }
        globalThis.postMessage({
            id: request.id,
            ok: true,
            result: request.ast
                ? session.engine.checkAst(request.ast, request.context)
                : session.engine.check(request.input, request.context)
        } satisfies Response);
    } catch (error) {
        globalThis.postMessage({ id: request.id, ok: false, error: String(error) } satisfies Response);
    }
});
