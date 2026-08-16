import { spawn } from "node:child_process";
import { createServer } from "node:net";
import { resolve } from "node:path";

const delay = milliseconds => new Promise(resolveDelay => setTimeout(resolveDelay, milliseconds));

async function findFreePort() {
    const probe = createServer();
    await new Promise((resolveListen, rejectListen) => {
        probe.once("error", rejectListen);
        probe.listen(0, "127.0.0.1", resolveListen);
    });
    const address = probe.address();
    const port = typeof address === "object" && address ? address.port : 0;
    await new Promise((resolveClose, rejectClose) => {
        probe.close(error => error ? rejectClose(error) : resolveClose());
    });
    if (!port) throw new Error("Unable to allocate a test port");
    return port;
}

async function fetchWithTimeout(url, init = {}, timeout = 30_000) {
    const controller = new AbortController();
    const timer = setTimeout(() => controller.abort(), timeout);
    try {
        return await fetch(url, { ...init, signal: controller.signal });
    } finally {
        clearTimeout(timer);
    }
}

export async function jsonRequest(baseUrl, pathname, options = {}) {
    const method = options.method ?? (options.body === undefined ? "GET" : "POST");
    const headers = {
        ...(options.body === undefined ? {} : { "Content-Type": "application/json" }),
        ...options.headers
    };
    const response = await fetchWithTimeout(`${baseUrl}${pathname}`, {
        method,
        headers,
        body: options.body === undefined ? undefined : JSON.stringify(options.body),
        cache: "no-store"
    }, options.timeout);
    let body = null;
    try {
        body = await response.json();
    } catch {
        // Callers assert the response shape and can report the captured server output.
    }
    return { response, body };
}

export async function startTTServer(directory, extraEnv = {}) {
    const root = resolve(directory);
    const port = await findFreePort();
    const baseUrl = `http://127.0.0.1:${port}`;
    const child = spawn(process.execPath, ["server.mjs", "--no-open"], {
        cwd: root,
        env: {
            ...process.env,
            HOST: "127.0.0.1",
            PORT: String(port),
            DEDUCTRIUM_TT_IDLE_TIMEOUT_MS: "60000",
            ...extraEnv
        },
        stdio: ["ignore", "pipe", "pipe"],
        windowsHide: true
    });
    let stdout = "";
    let stderr = "";
    let spawnError = null;
    child.stdout?.on("data", chunk => { stdout += chunk.toString(); });
    child.stderr?.on("data", chunk => { stderr += chunk.toString(); });
    child.once("error", error => { spawnError = error; });

    const deadline = Date.now() + 15_000;
    while (Date.now() < deadline) {
        if (spawnError) break;
        if (child.exitCode !== null) break;
        try {
            const { response, body } = await jsonRequest(baseUrl, "/api/tt/health", { timeout: 500 });
            if (response.ok && body?.available === true) {
                return {
                    baseUrl,
                    child,
                    output: () => `${stdout}${stderr}`
                };
            }
        } catch {
            // The server may still be binding the port.
        }
        await delay(50);
    }

    if (child.exitCode === null) child.kill("SIGKILL");
    const detail = spawnError?.message || `${stdout}${stderr}`.trim() || "no server output";
    throw new Error(`Deductrium test server did not become ready: ${detail}`);
}

export async function stopTTServer(server, sessionIds = []) {
    for (const sessionId of sessionIds) {
        try {
            await jsonRequest(server.baseUrl, "/api/tt/dispose", {
                body: { sessionId },
                timeout: 1_000
            });
        } catch {
            // The server may already have stopped after a failed assertion.
        }
    }
    if (server.child.exitCode !== null) return;

    server.child.kill("SIGTERM");
    await Promise.race([
        new Promise(resolveExit => server.child.once("exit", resolveExit)),
        delay(2_000)
    ]);
    if (server.child.exitCode === null) server.child.kill("SIGKILL");
}

export const minimalTTConfig = {
    unlockedTypes: ["True"],
    disableSimpleFn: false,
    disableSimpleEq: false,
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
};
