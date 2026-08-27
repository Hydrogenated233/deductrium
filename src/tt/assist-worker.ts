import { AST } from "./astparser.js";
import {
    TTAssistEngine,
    TTAssistOptions,
    TTAssistQedResult,
    TTAssistSnapshot
} from "./assist-engine.js";
import { TTCoreConfig } from "./engine.js";
import { TTCoreSession, TTDefinitionSlot } from "./core-session.js";

type Request =
    | {
        id: number;
        kind: "configure";
        config: TTCoreConfig;
        definitions?: TTDefinitionSlot[];
        loadedThrough?: number;
    }
    | { id: number, kind: "truncate", startIndex: number }
    | { id: number, kind: "set-definition", index: number, definition: TTDefinitionSlot }
    | { id: number, kind: "start", target: AST | string, options: TTAssistOptions, history?: string[] }
    | { id: number, kind: "apply", command: string }
    | { id: number, kind: "undo" }
    | { id: number, kind: "qed" }
    | { id: number, kind: "clear" };
type Response =
    | { id: number, ok: true, result?: TTAssistSnapshot | TTAssistQedResult }
    | { id: number, ok: false, error: string, operationError?: boolean };

const definitions = new TTCoreSession();
const engine = new TTAssistEngine(definitions.engine);

globalThis.addEventListener("message", (event: MessageEvent<Request>) => {
    const request = event.data;
    try {
        let result: TTAssistSnapshot | TTAssistQedResult;
        if (request.kind === "configure") {
            definitions.configure(request.config, request.definitions, request.loadedThrough);
            engine.clear();
        } else if (request.kind === "truncate") {
            definitions.truncate(request.startIndex);
            engine.clear();
        } else if (request.kind === "set-definition") {
            definitions.setDefinition(request.index, request.definition);
            engine.clear();
        } else if (request.kind === "start") {
            result = engine.start(request.target, request.options, request.history);
        } else if (request.kind === "apply") {
            result = engine.apply(request.command);
        } else if (request.kind === "undo") {
            result = engine.undo();
        } else if (request.kind === "qed") {
            result = engine.qed();
        } else {
            engine.clear();
        }
        globalThis.postMessage({ id: request.id, ok: true, result } satisfies Response);
    } catch (error) {
        globalThis.postMessage({
            id: request.id,
            ok: false,
            error: String(error),
            operationError: request.kind === "apply" || request.kind === "qed"
        } satisfies Response);
    }
});
