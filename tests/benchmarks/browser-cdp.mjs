import { spawn } from "node:child_process";
import { mkdtemp, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";

const DEFAULT_BROWSER_PATHS = process.platform === "win32"
    ? [
        "C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe",
        "C:\\Program Files (x86)\\Microsoft\\Edge\\Application\\msedge.exe",
        "C:\\Program Files\\Microsoft\\Edge\\Application\\msedge.exe"
    ]
    : process.platform === "darwin"
        ? [
            "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
            "/Applications/Microsoft Edge.app/Contents/MacOS/Microsoft Edge"
        ]
        : ["google-chrome", "chromium", "chromium-browser", "microsoft-edge"];

export async function withHeadlessBrowser(callback, options = {}) {
    const executable = await findBrowserExecutable(options.executable ?? process.env.BROWSER_PATH);
    const debugPort = await reservePort();
    const profileDir = await mkdtemp(join(tmpdir(), "deductrium-browser-benchmark-"));
    const browser = spawn(executable, [
        "--headless=new",
        "--disable-background-networking",
        "--disable-component-update",
        "--disable-default-apps",
        "--disable-extensions",
        "--disable-features=Translate,MediaRouter",
        "--disable-renderer-backgrounding",
        "--disable-sync",
        "--metrics-recording-only",
        "--mute-audio",
        "--no-first-run",
        "--no-default-browser-check",
        `--remote-debugging-port=${debugPort}`,
        `--user-data-dir=${profileDir}`,
        "about:blank"
    ], { stdio: "ignore" });

    try {
        const endpoint = await waitForDebugEndpoint(debugPort, options.timeoutMs ?? 30_000);
        const cdp = await CdpConnection.connect(endpoint.webSocketDebuggerUrl);
        try {
            return await callback(cdp);
        } finally {
            try {
                await Promise.race([
                    cdp.command("Browser.close").catch(() => { }),
                    new Promise(resolve => setTimeout(resolve, 1_000))
                ]);
            } catch { }
            cdp.close();
        }
    } finally {
        await waitForExit(browser, 5_000);
        if (browser.exitCode === null) {
            await terminateBrowserTree(browser);
            await waitForExit(browser, 5_000);
        }
        try {
            await rm(profileDir, {
                recursive: true,
                force: true,
                maxRetries: 50,
                retryDelay: 100
            });
        } catch (error) {
            console.warn(`Unable to remove browser benchmark profile ${profileDir}: ${error.message}`);
        }
    }
}

async function waitForExit(child, timeoutMs) {
    if (child.exitCode !== null) return;
    await Promise.race([
        new Promise(resolve => child.once("exit", resolve)),
        new Promise(resolve => setTimeout(resolve, timeoutMs))
    ]);
}

async function terminateBrowserTree(browser) {
    if (browser.exitCode !== null) return;
    if (process.platform !== "win32") {
        browser.kill("SIGKILL");
        return;
    }
    await new Promise(resolve => {
        const killer = spawn("taskkill", ["/pid", String(browser.pid), "/t", "/f"], {
            stdio: "ignore",
            windowsHide: true
        });
        killer.once("error", resolve);
        killer.once("exit", resolve);
    });
}

export class CdpConnection {
    constructor(socket) {
        this.socket = socket;
        this.nextId = 1;
        this.pending = new Map();
        this.listeners = new Map();
        socket.addEventListener("message", event => this.onMessage(event.data));
        socket.addEventListener("close", () => this.rejectAll(new Error("browser connection closed")));
        socket.addEventListener("error", () => this.rejectAll(new Error("browser connection failed")));
    }

    static async connect(url) {
        const socket = new WebSocket(url);
        await new Promise((resolve, reject) => {
            socket.addEventListener("open", resolve, { once: true });
            socket.addEventListener("error", reject, { once: true });
        });
        return new CdpConnection(socket);
    }

    async command(method, params = {}, sessionId) {
        const id = this.nextId++;
        const response = new Promise((resolve, reject) => this.pending.set(id, { resolve, reject }));
        this.socket.send(JSON.stringify({ id, method, params, ...(sessionId ? { sessionId } : {}) }));
        return response;
    }

    on(method, listener) {
        const listeners = this.listeners.get(method) ?? new Set();
        listeners.add(listener);
        this.listeners.set(method, listeners);
        return () => listeners.delete(listener);
    }

    waitFor(method, predicate = () => true, timeoutMs = 30_000) {
        return new Promise((resolve, reject) => {
            const stop = this.on(method, event => {
                if (!predicate(event)) return;
                clearTimeout(timer);
                stop();
                resolve(event);
            });
            const timer = setTimeout(() => {
                stop();
                reject(new Error(`timed out waiting for ${method}`));
            }, timeoutMs);
        });
    }

    close() {
        this.socket.close();
    }

    onMessage(data) {
        const message = JSON.parse(String(data));
        if (message.id) {
            const pending = this.pending.get(message.id);
            if (!pending) return;
            this.pending.delete(message.id);
            if (message.error) pending.reject(new Error(message.error.message));
            else pending.resolve(message.result);
            return;
        }
        for (const listener of this.listeners.get(message.method) ?? []) listener(message);
    }

    rejectAll(error) {
        for (const pending of this.pending.values()) pending.reject(error);
        this.pending.clear();
    }
}

export async function evaluate(cdp, sessionId, expression, options = {}) {
    const result = await cdp.command("Runtime.evaluate", {
        expression,
        awaitPromise: options.awaitPromise ?? true,
        returnByValue: options.returnByValue ?? true,
        userGesture: options.userGesture ?? false
    }, sessionId);
    if (result.exceptionDetails) {
        const description = result.exceptionDetails.exception?.description
            ?? result.exceptionDetails.text
            ?? "browser evaluation failed";
        throw new Error(description);
    }
    return result.result?.value;
}

async function findBrowserExecutable(explicit) {
    const { access } = await import("node:fs/promises");
    const candidates = explicit ? [explicit] : DEFAULT_BROWSER_PATHS;
    for (const candidate of candidates) {
        try {
            await access(candidate);
            return candidate;
        } catch { }
    }
    throw new Error("Chrome/Edge executable not found; set BROWSER_PATH");
}

async function reservePort() {
    const { createServer } = await import("node:net");
    return new Promise((resolve, reject) => {
        const server = createServer();
        server.once("error", reject);
        server.listen(0, "127.0.0.1", () => {
            const address = server.address();
            server.close(() => resolve(address.port));
        });
    });
}

async function waitForDebugEndpoint(port, timeoutMs) {
    const deadline = Date.now() + timeoutMs;
    let lastError;
    while (Date.now() < deadline) {
        try {
            const response = await fetch(`http://127.0.0.1:${port}/json/version`);
            if (response.ok) return response.json();
        } catch (error) {
            lastError = error;
        }
        await new Promise(resolve => setTimeout(resolve, 50));
    }
    throw lastError ?? new Error("browser debug endpoint did not start");
}
