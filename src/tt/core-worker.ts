import type { TTCoreCheckResult } from "./engine.js";
import {
    TTCoreSession,
    type TTCoreSessionRequest
} from "./core-session.js";

type Request = { id: number } & TTCoreSessionRequest;
type Response =
    | { id: number, ok: true, result?: TTCoreCheckResult }
    | { id: number, ok: false, error: string };

const session = new TTCoreSession();

globalThis.addEventListener("message", (event: MessageEvent<Request>) => {
    const request = event.data;
    try {
        const { id, ...command } = request;
        const result = session.dispatch(command);
        globalThis.postMessage({ id, ok: true, result } satisfies Response);
    } catch (error) {
        globalThis.postMessage({ id: request.id, ok: false, error: String(error) } satisfies Response);
    }
});
