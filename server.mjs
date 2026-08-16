import { fork, spawn } from "node:child_process";
import { randomUUID } from "node:crypto";
import { createReadStream } from "node:fs";
import { stat } from "node:fs/promises";
import { createServer } from "node:http";
import { extname, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";

const root = resolve(fileURLToPath(new URL(".", import.meta.url)));
const ttProcessPath = fileURLToPath(new URL("./tt-process.mjs", import.meta.url));
const host = process.env.HOST || "127.0.0.1";
const port = Number(process.env.PORT || 4174);
const shouldOpen = !process.argv.includes("--no-open");
const protocolVersion = 1;
const bodyLimit = readPositiveInteger("DEDUCTRIUM_TT_BODY_MB", 32) * 1024 * 1024;
const childHeapMb = readPositiveInteger("DEDUCTRIUM_TT_HEAP_MB", 2048);
const childReadyTimeout = readPositiveInteger("DEDUCTRIUM_TT_READY_TIMEOUT_MS", 15_000);
const defaultRpcTimeout = readPositiveInteger("DEDUCTRIUM_TT_RPC_TIMEOUT_MS", 120_000);
const idleTimeout = readPositiveInteger("DEDUCTRIUM_TT_IDLE_TIMEOUT_MS", 30 * 60_000);
const maxSessions = readPositiveInteger("DEDUCTRIUM_TT_MAX_SESSIONS", 4);
const maxSessionRequests = readPositiveInteger("DEDUCTRIUM_TT_MAX_PENDING", 4);
const maxApiRequests = readPositiveInteger("DEDUCTRIUM_TT_MAX_API_REQUESTS", 8);
const idleSweepInterval = Math.min(Math.max(Math.floor(idleTimeout / 4), 10_000), 60_000);
const hardMaxRpcTimeout = 30 * 60_000;
const maxRpcTimeout = Math.min(
    readPositiveInteger("DEDUCTRIUM_TT_MAX_RPC_TIMEOUT_MS", hardMaxRpcTimeout),
    hardMaxRpcTimeout
);
const sessions = new Map();
let activeApiRequests = 0;

const mimeTypes = {
    ".css": "text/css; charset=utf-8",
    ".html": "text/html; charset=utf-8",
    ".ico": "image/x-icon",
    ".jpeg": "image/jpeg",
    ".jpg": "image/jpeg",
    ".js": "text/javascript; charset=utf-8",
    ".json": "application/json; charset=utf-8",
    ".map": "application/json; charset=utf-8",
    ".png": "image/png",
    ".svg": "image/svg+xml",
    ".txt": "text/plain; charset=utf-8",
    ".webp": "image/webp",
    ".woff": "font/woff",
    ".woff2": "font/woff2"
};
const publicRootFiles = new Set(["index.html", "gui.css"]);

class HttpError extends Error {
    constructor(status, code, message, generation) {
        super(message);
        this.status = status;
        this.code = code;
        this.generation = generation;
    }
}

function readPositiveInteger(name, fallback) {
    const value = Number(process.env[name]);
    return Number.isFinite(value) && value > 0 ? Math.floor(value) : fallback;
}

function openBrowser(url) {
    const command = process.platform === "win32"
        ? ["cmd.exe", ["/c", "start", "", url]]
        : process.platform === "darwin"
            ? ["open", [url]]
            : ["xdg-open", [url]];

    try {
        spawn(command[0], command[1], { detached: true, stdio: "ignore" }).unref();
    } catch {
        // The URL is printed below even when no desktop opener is available.
    }
}

function sendJson(response, status, value, headers = {}) {
    const body = Buffer.from(JSON.stringify(value));
    response.writeHead(status, {
        "Cache-Control": "no-store",
        "Content-Length": body.length,
        "Content-Type": "application/json; charset=utf-8",
        ...headers
    });
    response.end(body);
}

function sendApiError(response, error) {
    if (response.destroyed) return;
    if (response.headersSent) {
        response.destroy();
        return;
    }
    const status = error instanceof HttpError ? error.status : 500;
    const result = {
        ok: false,
        error: error instanceof Error ? error.message : String(error),
        code: error instanceof HttpError ? error.code : "TT_PROCESS_SERVER_ERROR"
    };
    if (error instanceof HttpError && Number.isFinite(error.generation)) {
        result.generation = error.generation;
    }
    sendJson(response, status, result);
}

function isLoopbackHostname(hostname) {
    let normalized = String(hostname || "").toLowerCase().replace(/^\[|\]$/g, "");
    if (normalized.startsWith("::ffff:")) normalized = normalized.slice("::ffff:".length);
    if (normalized === "localhost" || normalized === "::1") return true;
    const octets = normalized.split(".");
    return octets.length === 4
        && octets[0] === "127"
        && octets.every(octet => /^\d{1,3}$/.test(octet) && Number(octet) <= 255);
}

function assertSameOrigin(request) {
    if (request.headers["sec-fetch-site"] === "cross-site") {
        throw new HttpError(403, "TT_PROCESS_FORBIDDEN", "Cross-origin type-theory requests are forbidden");
    }
    let authority;
    try {
        authority = new URL(`http://${request.headers.host || ""}`);
    } catch {
        throw new HttpError(400, "TT_PROCESS_INVALID_HOST", "Invalid request host");
    }
    if (!isLoopbackHostname(authority.hostname)) {
        throw new HttpError(
            404,
            "TT_PROCESS_LOCAL_ONLY",
            "The isolated type-theory process is available only from localhost"
        );
    }
    if (!isLoopbackHostname(request.socket.remoteAddress)) {
        throw new HttpError(
            404,
            "TT_PROCESS_LOCAL_ONLY",
            "The isolated type-theory process accepts only local connections"
        );
    }
    const origin = request.headers.origin;
    if (!origin) return;
    let parsed;
    try {
        parsed = new URL(origin);
    } catch {
        throw new HttpError(403, "TT_PROCESS_FORBIDDEN", "Invalid request origin");
    }
    if (parsed.protocol !== "http:"
        || !isLoopbackHostname(parsed.hostname)
        || parsed.host !== authority.host) {
        throw new HttpError(403, "TT_PROCESS_FORBIDDEN", "Cross-origin type-theory requests are forbidden");
    }
}

function readJson(request, allowEmpty = false) {
    const declaredLength = Number(request.headers["content-length"]);
    if (Number.isFinite(declaredLength) && declaredLength > bodyLimit) {
        throw new HttpError(413, "TT_PROCESS_BODY_TOO_LARGE", "Type-theory request body is too large");
    }
    return new Promise((resolveBody, rejectBody) => {
        const chunks = [];
        let size = 0;
        let settled = false;

        const fail = error => {
            if (settled) return;
            settled = true;
            rejectBody(error);
        };
        request.on("aborted", () => fail(new HttpError(400, "TT_PROCESS_ABORTED", "Request was aborted")));
        request.on("error", fail);
        request.on("data", chunk => {
            if (settled) return;
            size += chunk.length;
            if (size > bodyLimit) {
                fail(new HttpError(413, "TT_PROCESS_BODY_TOO_LARGE", "Type-theory request body is too large"));
                request.resume();
                return;
            }
            chunks.push(chunk);
        });
        request.on("end", () => {
            if (settled) return;
            settled = true;
            const source = Buffer.concat(chunks).toString("utf8").trim();
            if (!source && allowEmpty) {
                resolveBody({});
                return;
            }
            try {
                resolveBody(JSON.parse(source));
            } catch {
                rejectBody(new HttpError(400, "TT_PROCESS_INVALID_JSON", "Invalid JSON request body"));
            }
        });
    });
}

function childExecArgv() {
    return [`--max-old-space-size=${childHeapMb}`];
}

function createSessionState() {
    const session = {
        id: randomUUID(),
        generation: 1,
        child: null,
        readyPromise: null,
        restartPromise: null,
        pending: new Map(),
        activeRequests: 0,
        nextRpcId: 1,
        lastUsed: Date.now(),
        disposed: false
    };
    sessions.set(session.id, session);
    return session;
}

async function createSession() {
    sweepIdleSessions();
    if (sessions.size >= maxSessions) {
        throw new HttpError(
            429,
            "TT_PROCESS_SESSION_LIMIT",
            `At most ${maxSessions} isolated type-theory sessions may run at once`
        );
    }
    const session = createSessionState();
    try {
        await launchChild(session);
        return session;
    } catch (error) {
        sessions.delete(session.id);
        disposeSession(session, error);
        throw error;
    }
}

function launchChild(session) {
    if (session.disposed) {
        return Promise.reject(new HttpError(410, "TT_PROCESS_DISPOSED", "Type-theory session was disposed"));
    }

    let child;
    try {
        child = fork(ttProcessPath, [], {
            execArgv: childExecArgv(),
            serialization: "advanced",
            stdio: ["ignore", "inherit", "inherit", "ipc"],
            windowsHide: true
        });
    } catch (error) {
        return Promise.reject(new HttpError(
            503,
            "TT_PROCESS_START_FAILED",
            `Unable to start type-theory process: ${error instanceof Error ? error.message : String(error)}`,
            session.generation
        ));
    }

    session.child = child;
    const generation = session.generation;
    session.readyPromise = new Promise((resolveReady, rejectReady) => {
        let readySettled = false;
        const finishReady = error => {
            if (readySettled) return;
            readySettled = true;
            clearTimeout(timer);
            if (error) rejectReady(error);
            else resolveReady();
        };
        const timer = setTimeout(() => {
            const error = new HttpError(
                503,
                "TT_PROCESS_START_TIMEOUT",
                "Type-theory process did not become ready",
                generation
            );
            if (session.child === child) session.child = null;
            finishReady(error);
            terminateChild(child);
        }, childReadyTimeout);
        timer.unref?.();

        child.on("message", message => {
            if (!message || typeof message !== "object") return;
            if (message.kind === "ready") {
                finishReady();
                return;
            }
            handleChildResponse(session, child, generation, message);
        });
        child.once("error", error => {
            const wrapped = new HttpError(
                503,
                "TT_PROCESS_EXITED",
                `Type-theory process failed: ${error.message}`,
                generation
            );
            finishReady(wrapped);
            handleChildFailure(session, child, wrapped);
        });
        child.once("exit", (code, signal) => {
            const detail = signal ? `signal ${signal}` : `code ${code ?? "unknown"}`;
            const error = new HttpError(
                503,
                "TT_PROCESS_EXITED",
                `Type-theory process exited with ${detail}`,
                generation
            );
            finishReady(error);
            handleChildFailure(session, child, error);
        });
    });
    return session.readyPromise;
}

function handleChildResponse(session, child, generation, message) {
    if (session.child !== child || generation !== session.generation || message.kind !== "rpc-result") return;
    const pending = session.pending.get(message.rpcId);
    if (!pending || pending.generation !== generation) return;
    session.pending.delete(message.rpcId);
    clearTimeout(pending.timer);
    pending.resolve({
        ok: message.ok === true,
        result: message.result,
        error: message.error,
        operationError: message.operationError === true,
        generation
    });
}

function handleChildFailure(session, child, error) {
    if (session.disposed || session.child !== child) return;
    session.child = null;
    session.readyPromise = null;
    const restartError = new HttpError(
        error.status ?? 503,
        error.code ?? "TT_PROCESS_EXITED",
        error.message,
        session.generation + 1
    );
    // Restart lazily on the next request. A child that fails immediately after
    // becoming ready must not create an unbounded fork/restart loop.
    rejectPending(session, restartError);
}

function rejectPending(session, error) {
    for (const pending of session.pending.values()) {
        clearTimeout(pending.timer);
        pending.reject(error);
    }
    session.pending.clear();
}

function terminateChild(child) {
    if (!child) return;
    try {
        child.kill("SIGKILL");
    } catch {
        // The process may already have exited.
    }
}

function restartSession(session, reason = new Error("Type-theory process reset")) {
    if (session.disposed) {
        return Promise.reject(new HttpError(410, "TT_PROCESS_DISPOSED", "Type-theory session was disposed"));
    }
    if (session.restartPromise) return session.restartPromise;

    session.restartPromise = (async () => {
        const previousChild = session.child;
        session.child = null;
        session.readyPromise = null;
        session.generation++;
        rejectPending(session, reason);
        terminateChild(previousChild);
        await launchChild(session);
        session.lastUsed = Date.now();
        return session.generation;
    })().finally(() => {
        session.restartPromise = null;
    });
    return session.restartPromise;
}

async function ensureReady(session) {
    if (session.disposed) {
        throw new HttpError(410, "TT_PROCESS_DISPOSED", "Type-theory session was disposed");
    }
    if (session.restartPromise) await session.restartPromise;
    if (!session.child || !session.readyPromise) {
        await restartSession(session, new Error("Type-theory process was unavailable"));
    } else {
        await session.readyPromise;
    }
}

function normalizeTimeout(value) {
    if (value === undefined || value === null || value === "") return defaultRpcTimeout;
    const timeout = Number(value);
    if (!Number.isFinite(timeout) || timeout <= 0) {
        throw new HttpError(400, "TT_PROCESS_INVALID_TIMEOUT", "Type-theory process timeout must be positive");
    }
    return Math.min(Math.max(Math.floor(timeout), 100), maxRpcTimeout);
}

function requireSession(sessionId) {
    if (typeof sessionId !== "string" || !sessionId) {
        throw new HttpError(400, "TT_PROCESS_INVALID_SESSION", "A type-theory session id is required");
    }
    const session = sessions.get(sessionId);
    if (!session || session.disposed) {
        throw new HttpError(404, "TT_PROCESS_SESSION_NOT_FOUND", "Type-theory session was not found");
    }
    return session;
}

function assertGeneration(session, generation) {
    if (generation === undefined || generation === null) return;
    if (!Number.isFinite(Number(generation)) || Number(generation) !== session.generation) {
        throw new HttpError(
            409,
            "TT_PROCESS_GENERATION_CHANGED",
            "Type-theory process generation changed",
            session.generation
        );
    }
}

function extractRpcRequest(body) {
    if (body.request && typeof body.request === "object") return body.request;
    if (body.message && typeof body.message === "object") return body.message;
    if (typeof body.kind === "string") {
        const { sessionId, generation, channel, timeout, ...request } = body;
        return request;
    }
    throw new HttpError(400, "TT_PROCESS_INVALID_REQUEST", "A type-theory RPC request is required");
}

async function runRpc(session, body, httpRequest, httpResponse) {
    if (session.activeRequests >= maxSessionRequests) {
        throw new HttpError(
            429,
            "TT_PROCESS_BUSY",
            `This type-theory session already has ${maxSessionRequests} pending requests`,
            session.generation
        );
    }
    session.activeRequests++;
    let disconnected = false;
    let cancelPending = null;
    const disconnectedError = () => new HttpError(
        499,
        "TT_PROCESS_CLIENT_CLOSED",
        "The type-theory request client disconnected",
        session.generation + 1
    );
    const markDisconnected = () => {
        if (disconnected) return;
        disconnected = true;
        cancelPending?.(disconnectedError());
    };
    const handleResponseClose = () => {
        if (!httpResponse.writableEnded) markDisconnected();
    };
    httpRequest.once("aborted", markDisconnected);
    httpResponse.once("close", handleResponseClose);
    try {
        await ensureReady(session);
        if (disconnected) throw disconnectedError();
        assertGeneration(session, body.generation);
        const channel = body.channel;
        if (channel !== "core" && channel !== "assist") {
            throw new HttpError(400, "TT_PROCESS_INVALID_CHANNEL", "Unknown type-theory process channel", session.generation);
        }
        const request = extractRpcRequest(body);
        if (typeof request.kind !== "string") {
            throw new HttpError(400, "TT_PROCESS_INVALID_REQUEST", "A type-theory request kind is required", session.generation);
        }
        const timeout = normalizeTimeout(body.timeout);
        const generation = session.generation;
        const child = session.child;
        const rpcId = session.nextRpcId++;
        session.lastUsed = Date.now();

        return await new Promise((resolveRpc, rejectRpc) => {
            const cancel = error => {
                if (!session.pending.has(rpcId)) return;
                const pending = session.pending.get(rpcId);
                clearTimeout(pending?.timer);
                session.pending.delete(rpcId);
                rejectRpc(error);
                void restartSession(session, error).catch(restartError => {
                    console.error(`Unable to restart disconnected type-theory session ${session.id}: ${restartError.message}`);
                });
            };
            const timer = setTimeout(() => {
                if (!session.pending.has(rpcId)) return;
                const error = new HttpError(
                    504,
                    "TT_PROCESS_TIMEOUT",
                    "Type-theory process timed out",
                    session.generation + 1
                );
                void restartSession(session, error).catch(restartError => {
                    console.error(`Unable to restart timed-out type-theory session ${session.id}: ${restartError.message}`);
                });
            }, timeout);
            timer.unref?.();
            session.pending.set(rpcId, {
                generation,
                resolve: resolveRpc,
                reject: rejectRpc,
                timer
            });
            cancelPending = cancel;
            if (disconnected) {
                cancel(disconnectedError());
                return;
            }

            try {
                child.send({
                    kind: "rpc",
                    rpcId,
                    generation,
                    channel,
                    request
                }, error => {
                    if (!error || !session.pending.has(rpcId)) return;
                    const wrapped = new HttpError(
                        503,
                        "TT_PROCESS_IPC_FAILED",
                        `Unable to contact type-theory process: ${error.message}`,
                        session.generation + 1
                    );
                    void restartSession(session, wrapped).catch(restartError => {
                        console.error(`Unable to restart type-theory session ${session.id}: ${restartError.message}`);
                    });
                });
            } catch (error) {
                const wrapped = new HttpError(
                    503,
                    "TT_PROCESS_IPC_FAILED",
                    `Unable to contact type-theory process: ${error instanceof Error ? error.message : String(error)}`,
                    session.generation + 1
                );
                void restartSession(session, wrapped).catch(restartError => {
                    console.error(`Unable to restart type-theory session ${session.id}: ${restartError.message}`);
                });
            }
        });
    } finally {
        cancelPending = null;
        httpRequest.off("aborted", markDisconnected);
        httpResponse.off("close", handleResponseClose);
        session.activeRequests--;
    }
}

function disposeSession(session, reason = new Error("Type-theory session disposed")) {
    if (session.disposed) return;
    session.disposed = true;
    session.restartPromise = null;
    rejectPending(session, reason);
    const child = session.child;
    session.child = null;
    session.readyPromise = null;
    terminateChild(child);
}

async function handleApi(request, response, url) {
    assertSameOrigin(request);
    const pathname = url.pathname;

    if (pathname === "/api/tt/health") {
        if (request.method !== "GET" && request.method !== "HEAD") {
            throw new HttpError(405, "TT_PROCESS_METHOD_NOT_ALLOWED", "Method not allowed");
        }
        const result = {
            ok: true,
            available: true,
            protocolVersion,
            sessions: sessions.size
        };
        if (request.method === "HEAD") {
            response.writeHead(200, { "Cache-Control": "no-store" });
            response.end();
        } else {
            sendJson(response, 200, result);
        }
        return;
    }

    if (request.method !== "POST") {
        throw new HttpError(405, "TT_PROCESS_METHOD_NOT_ALLOWED", "Method not allowed");
    }

    if (pathname === "/api/tt/session") {
        await readJson(request, true);
        const session = await createSession();
        if (request.aborted || response.destroyed) {
            sessions.delete(session.id);
            disposeSession(session, new Error("Type-theory session client disconnected"));
            return;
        }
        try {
            sendJson(response, 201, {
                ok: true,
                sessionId: session.id,
                generation: session.generation,
                protocolVersion
            });
        } catch (error) {
            sessions.delete(session.id);
            disposeSession(session, error);
            throw error;
        }
        return;
    }

    const body = await readJson(request);
    if (!body || typeof body !== "object" || Array.isArray(body)) {
        throw new HttpError(400, "TT_PROCESS_INVALID_REQUEST", "Invalid type-theory request body");
    }

    if (pathname === "/api/tt/rpc") {
        const session = requireSession(body.sessionId);
        const result = await runRpc(session, body, request, response);
        session.lastUsed = Date.now();
        sendJson(response, 200, result);
        return;
    }

    if (pathname === "/api/tt/reset") {
        const session = requireSession(body.sessionId);
        if (body.generation !== undefined && Number(body.generation) !== session.generation) {
            sendJson(response, 200, {
                ok: true,
                generation: session.generation,
                restarted: false
            });
            return;
        }
        const generation = await restartSession(session);
        sendJson(response, 200, { ok: true, generation, restarted: true });
        return;
    }

    if (pathname === "/api/tt/dispose") {
        const session = sessions.get(body.sessionId);
        if (session) {
            sessions.delete(session.id);
            disposeSession(session);
        }
        sendJson(response, 200, { ok: true });
        return;
    }

    throw new HttpError(404, "TT_PROCESS_API_NOT_FOUND", "Type-theory API endpoint was not found");
}

async function serveStatic(request, response, url) {
    if (request.method !== "GET" && request.method !== "HEAD") {
        response.writeHead(405, {
            "Allow": "GET, HEAD",
            "Content-Type": "text/plain; charset=utf-8"
        });
        response.end("Method not allowed");
        return;
    }
    try {
        let pathname = decodeURIComponent(url.pathname);
        if (pathname.endsWith("/")) pathname += "index.html";

        const relativePath = pathname.replace(/^\/+/, "").replace(/\\/g, "/");
        const pathSegments = relativePath.split("/");
        if (pathSegments.some(segment => segment === "." || segment === "..")) {
            response.writeHead(404, { "Content-Type": "text/plain; charset=utf-8" });
            response.end("Not found");
            return;
        }
        if (!publicRootFiles.has(relativePath) && !relativePath.startsWith("js/")) {
            response.writeHead(404, { "Content-Type": "text/plain; charset=utf-8" });
            response.end("Not found");
            return;
        }

        const filePath = resolve(root, relativePath);
        if (filePath !== root && !filePath.startsWith(root + sep)) {
            response.writeHead(403, { "Content-Type": "text/plain; charset=utf-8" });
            response.end("Forbidden");
            return;
        }

        const fileInfo = await stat(filePath);
        if (!fileInfo.isFile()) throw new Error("Not a file");

        response.writeHead(200, {
            "Cache-Control": "no-cache",
            "Content-Length": fileInfo.size,
            "Content-Type": mimeTypes[extname(filePath).toLowerCase()] || "application/octet-stream"
        });

        if (request.method === "HEAD") {
            response.end();
            return;
        }
        createReadStream(filePath).pipe(response);
    } catch {
        response.writeHead(404, { "Content-Type": "text/plain; charset=utf-8" });
        response.end("Not found");
    }
}

const server = createServer((request, response) => {
    let url;
    try {
        url = new URL(request.url || "/", `http://${request.headers.host || host}`);
    } catch {
        response.writeHead(400, { "Content-Type": "text/plain; charset=utf-8" });
        response.end("Bad request");
        return;
    }
    if (url.pathname.startsWith("/api/tt/")) {
        if (activeApiRequests >= maxApiRequests) {
            sendApiError(response, new HttpError(
                429,
                "TT_PROCESS_SERVER_BUSY",
                `The type-theory server already has ${maxApiRequests} active API requests`
            ));
            return;
        }
        activeApiRequests++;
        void handleApi(request, response, url)
            .catch(error => sendApiError(response, error))
            .finally(() => activeApiRequests--);
        return;
    }
    void serveStatic(request, response, url);
});

server.requestTimeout = 60_000;
server.headersTimeout = 15_000;

function sweepIdleSessions(now = Date.now()) {
    for (const [id, session] of sessions) {
        if (session.activeRequests || session.pending.size || session.restartPromise
            || now - session.lastUsed < idleTimeout) continue;
        sessions.delete(id);
        disposeSession(session, new Error("Type-theory session expired"));
    }
}

const idleSweep = setInterval(sweepIdleSessions, idleSweepInterval);
idleSweep.unref?.();

function cleanupSessions() {
    clearInterval(idleSweep);
    for (const session of sessions.values()) disposeSession(session);
    sessions.clear();
}

let shuttingDown = false;
function shutdown(signal) {
    if (shuttingDown) return;
    shuttingDown = true;
    cleanupSessions();
    server.close(() => process.exit(signal === "SIGINT" ? 130 : 0));
    const forceExit = setTimeout(() => process.exit(1), 2_000);
    forceExit.unref?.();
}

process.once("SIGINT", () => shutdown("SIGINT"));
process.once("SIGTERM", () => shutdown("SIGTERM"));
process.once("exit", cleanupSessions);

server.on("error", error => {
    cleanupSessions();
    console.error(`Unable to start Deductrium server: ${error.message}`);
    process.exitCode = 1;
});

server.listen(port, host, () => {
    const url = `http://${host}:${port}/`;
    console.log(`Deductrium is running at ${url}`);
    console.log(`Type-theory checks run in an isolated Node process (up to ${childHeapMb} MB).`);
    console.log("Press Ctrl+C to stop.");
    if (shouldOpen) openBrowser(url);
});
