import { isMainThread, parentPort, Worker, workerData } from "node:worker_threads";

const protocolVersion = 1;
const channels = ["core", "assist"];

function sendToParent(message) {
    if (!process.connected || typeof process.send !== "function") return;
    try {
        process.send(message, error => {
            if (!error) return;
            console.error(`Unable to return type-theory process result: ${error.message}`);
            // A broken IPC channel cannot recover in this child. Exit so the
            // server can reject pending requests and start a fresh generation.
            try { process.disconnect?.(); } catch { }
            process.exit(1);
        });
    } catch (error) {
        console.error(`Unable to return type-theory process result: ${error.message}`);
        try { process.disconnect?.(); } catch { }
        process.exit(1);
    }
}

async function startChannelWorker(channel) {
    if (channel === "core") {
        const { TTCoreSession } = await import("./js/tt/core-session.js");
        const session = new TTCoreSession();
        return request => {
            if (request.kind === "configure") {
                session.configure(request.config, request.definitions);
                return undefined;
            }
            if (request.kind === "truncate") {
                session.truncate(request.startIndex);
                return undefined;
            }
            if (request.kind === "set-definition") {
                session.setDefinition(request.index, request.definition);
                return undefined;
            }
            if (request.kind === "validate") {
                return session.validate(request.index, request.ast, request.context);
            }
            if (request.kind === "check") {
                return request.ast
                    ? session.engine.checkAst(request.ast, request.context)
                    : session.engine.check(request.input, request.context);
            }
            throw new Error(`Unknown core request: ${String(request.kind)}`);
        };
    }

    if (channel === "assist") {
        const [{ TTAssistEngine }, { TTCoreSession }] = await Promise.all([
            import("./js/tt/assist-engine.js"),
            import("./js/tt/core-session.js")
        ]);
        const definitions = new TTCoreSession();
        const engine = new TTAssistEngine(definitions.engine);
        return request => {
            if (request.kind === "configure") {
                definitions.configure(request.config, request.definitions);
                engine.clear();
                return undefined;
            }
            if (request.kind === "truncate") {
                definitions.truncate(request.startIndex);
                engine.clear();
                return undefined;
            }
            if (request.kind === "set-definition") {
                definitions.setDefinition(request.index, request.definition);
                engine.clear();
                return undefined;
            }
            if (request.kind === "start") {
                return engine.start(request.target, request.options, request.history);
            }
            if (request.kind === "apply") return engine.apply(request.command);
            if (request.kind === "undo") return engine.undo();
            if (request.kind === "qed") return engine.qed();
            if (request.kind === "clear") {
                engine.clear();
                return undefined;
            }
            throw new Error(`Unknown assist request: ${String(request.kind)}`);
        };
    }

    throw new Error(`Unknown type-theory process channel: ${String(channel)}`);
}

async function runWorkerThread(channel) {
    if (!parentPort) throw new Error("Type-theory channel worker has no parent port");
    const handle = await startChannelWorker(channel);
    parentPort.postMessage({ kind: "worker-ready", channel, protocolVersion });
    parentPort.on("message", message => {
        if (!message || typeof message !== "object" || message.kind !== "rpc") return;
        const { rpcId, generation, request } = message;
        try {
            if (!request || typeof request !== "object") throw new Error("Invalid type-theory request");
            const result = handle(request);
            parentPort.postMessage({
                kind: "rpc-result",
                rpcId,
                generation,
                ok: true,
                result
            });
        } catch (error) {
            parentPort.postMessage({
                kind: "rpc-result",
                rpcId,
                generation,
                ok: false,
                error: String(error),
                operationError: channel === "assist"
                    && (request?.kind === "apply" || request?.kind === "qed")
            });
        }
    });
}

function runProcessHost() {
    const workers = new Map();
    const readyChannels = new Set();
    let readySent = false;
    let shuttingDown = false;

    const failProcess = error => {
        if (shuttingDown) return;
        console.error(`Type-theory channel worker failed: ${error instanceof Error ? error.message : String(error)}`);
        shuttingDown = true;
        for (const worker of workers.values()) void worker.terminate();
        process.exitCode = 1;
        process.exit(1);
    };

    for (const channel of channels) {
        let worker;
        try {
            worker = new Worker(new URL(import.meta.url), { type: "module", workerData: { channel } });
        } catch (error) {
            failProcess(error);
            return;
        }
        workers.set(channel, worker);
        worker.on("message", message => {
            if (!message || typeof message !== "object") return;
            if (message.kind === "worker-ready") {
                if (message.channel !== channel || message.protocolVersion !== protocolVersion) {
                    failProcess(new Error(`Unsupported channel protocol version: ${String(message.protocolVersion)}`));
                    return;
                }
                readyChannels.add(channel);
                if (!readySent && readyChannels.size === channels.length) {
                    readySent = true;
                    sendToParent({
                        kind: "ready",
                        protocolVersion,
                        pid: process.pid,
                        channels
                    });
                }
                return;
            }
            if (message.kind === "rpc-result") sendToParent(message);
        });
        worker.once("error", failProcess);
        worker.once("exit", code => {
            if (!shuttingDown) failProcess(new Error(`${channel} channel exited with code ${code}`));
        });
    }

    process.on("message", message => {
        if (!message || typeof message !== "object" || message.kind !== "rpc") return;
        const channel = message.channel;
        const worker = workers.get(channel);
        if (!worker) {
            sendToParent({
                kind: "rpc-result",
                rpcId: message.rpcId,
                generation: message.generation,
                ok: false,
                error: `Unknown type-theory process channel: ${String(channel)}`
            });
            return;
        }
        try {
            worker.postMessage(message);
        } catch (error) {
            sendToParent({
                kind: "rpc-result",
                rpcId: message.rpcId,
                generation: message.generation,
                ok: false,
                error: `Unable to dispatch type-theory request: ${error instanceof Error ? error.message : String(error)}`
            });
        }
    });

    process.once("disconnect", () => {
        shuttingDown = true;
        for (const worker of workers.values()) void worker.terminate();
        process.exit(0);
    });
}

if (isMainThread) {
    runProcessHost();
} else {
    runWorkerThread(workerData?.channel).catch(error => {
        if (parentPort) parentPort.postMessage({
            kind: "worker-start-error",
            error: String(error)
        });
        process.exit(1);
    });
}
