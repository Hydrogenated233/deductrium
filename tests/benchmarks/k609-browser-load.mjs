import { spawn } from "node:child_process";
import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";

import { GameSaveLoad } from "../../js/saveload.js";
import {
    createK609BenchmarkTheorems,
    K609_FINAL_THEOREM
} from "../helpers/k609-workload.mjs";
import { withHeadlessBrowser, evaluate } from "./browser-cdp.mjs";

const sourceSave = readFileSync(
    new URL("../fixtures/k609-one-formula-before-perm-master.txt", import.meta.url),
    "utf8"
).trim();
const expectedTheoremCount = createK609BenchmarkTheorems(sourceSave).length;
const encodedSave = appendTheoremToSave(sourceSave, K609_FINAL_THEOREM);
const server = await startServer();

try {
    const result = await withHeadlessBrowser(async cdp => {
        const profileCpu = process.env.TT_BROWSER_PROFILE === "1";
        const origin = server.url;
        const { targetId } = await cdp.command("Target.createTarget", { url: "about:blank" });
        const { sessionId } = await cdp.command("Target.attachToTarget", { targetId, flatten: true });
        await cdp.command("Page.enable", {}, sessionId);
        await cdp.command("Runtime.enable", {}, sessionId);
        await cdp.command("Performance.enable", {}, sessionId);
        if (profileCpu) {
            await cdp.command("Profiler.enable", {}, sessionId);
            await cdp.command("Profiler.start", {}, sessionId);
        }
        await cdp.command("Page.addScriptToEvaluateOnNewDocument", {
            source: `(() => {
                // Inject the fixture before game.js runs. Loading an empty app
                // first would register pagehide autosave, which can overwrite
                // the fixture while navigating to the measured page.
                localStorage.setItem("deductrium-save", ${JSON.stringify(encodedSave)});
                const NativeWorker = globalThis.Worker;
                const stats = globalThis.__workerStats = {
                    created: 0,
                    coreCreated: 0,
                    assistCreated: 0,
                    configure: 0,
                    configureSlots: 0,
                    validate: 0,
                    truncate: 0,
                    setDefinition: 0,
                    byScript: {}
                };
                globalThis.Worker = class InstrumentedWorker extends NativeWorker {
                    constructor(url, options) {
                        super(url, options);
                        const script = String(url);
                        this.__script = script;
                        stats.created++;
                        if (script.includes("core-worker")) stats.coreCreated++;
                        if (script.includes("assist-worker")) stats.assistCreated++;
                        stats.byScript[script] ??= { configure: 0, configureSlots: 0, validate: 0, truncate: 0, setDefinition: 0 };
                    }
                    postMessage(message, transfer) {
                        const scriptStats = stats.byScript[this.__script];
                        if (message?.kind === "configure") {
                            stats.configure++;
                            stats.configureSlots += message.definitions?.length ?? 0;
                            scriptStats.configure++;
                            scriptStats.configureSlots += message.definitions?.length ?? 0;
                        } else if (message?.kind === "validate") {
                            stats.validate++;
                            scriptStats.validate++;
                        } else if (message?.kind === "truncate") {
                            stats.truncate++;
                            scriptStats.truncate++;
                        } else if (message?.kind === "set-definition") {
                            stats.setDefinition++;
                            scriptStats.setDefinition++;
                        }
                        return transfer === undefined
                            ? super.postMessage(message)
                            : super.postMessage(message, transfer);
                    }
                };
                globalThis.__benchmarkNavigationStarted = performance.now();
            })();`
        }, sessionId);

        const started = performance.now();
        // Subscribe before navigation so a fast cached load cannot emit the
        // event between Page.navigate resolving and waitFor registering.
        const loaded = cdp.waitFor(
            "Page.loadEventFired",
            event => event.sessionId === sessionId,
            30_000
        );
        await cdp.command("Page.navigate", { url: `${origin}/index.html` }, sessionId);
        await loaded;
        const browserResult = await evaluate(cdp, sessionId, `(async () => {
            const deadline = Date.now() + 180000;
            while (!globalThis.deductriumGame) {
                if (Date.now() >= deadline) throw new Error("game did not initialize");
                await new Promise(resolve => setTimeout(resolve, 10));
            }
            const game = globalThis.deductriumGame;
            await game.ttGui.waitForValidationIdle();
            while (document.querySelector(".inhabitat .checking")) {
                if (Date.now() >= deadline) throw new Error("theorem validation did not settle");
                await new Promise(resolve => setTimeout(resolve, 10));
                await game.ttGui.waitForValidationIdle();
            }
            const inputs = Array.from(document.querySelectorAll(".inhabitat .tt-theorem-input"));
            const wrappers = inputs.map(input => input.parentElement);
            return {
                pageElapsedMs: Math.round(performance.now() - globalThis.__benchmarkNavigationStarted),
                theoremCount: inputs.length,
                errorCount: wrappers.filter(wrapper => wrapper?.classList.contains("error")).length,
                inferingCount: wrappers.filter(wrapper => wrapper?.classList.contains("infering")).length,
                checkingCount: wrappers.filter(wrapper => wrapper?.classList.contains("checking")).length,
                workerStats: globalThis.__workerStats
            };
        })()`, { awaitPromise: true });
        const metrics = await cdp.command("Performance.getMetrics", {}, sessionId);
        const metricMap = Object.fromEntries(metrics.metrics.map(metric => [metric.name, metric.value]));
        const cpuProfile = profileCpu
            ? await cdp.command("Profiler.stop", {}, sessionId)
            : null;
        return {
            ...browserResult,
            wallElapsedMs: Math.round(performance.now() - started),
            jsHeapUsedMB: toMB(metricMap.JSHeapUsedSize),
            jsHeapTotalMB: toMB(metricMap.JSHeapTotalSize),
            domNodes: metricMap.Nodes,
            documents: metricMap.Documents,
            browserMetrics: {
                taskMs: toMs(metricMap.TaskDuration),
                scriptMs: toMs(metricMap.ScriptDuration),
                layoutMs: toMs(metricMap.LayoutDuration),
                styleMs: toMs(metricMap.RecalcStyleDuration)
            },
            cpuProfile: cpuProfile ? summarizeCpuProfile(cpuProfile.profile) : undefined
        };
    });

    assertBenchmarkCompleted(result, expectedTheoremCount);

    console.log("K609 full browser save-load benchmark; timing and memory are informational only.");
    console.log(JSON.stringify(result, null, 2));
} finally {
    server.stop();
}

async function startServer() {
    const port = await reservePort();
    const child = spawn(process.execPath, ["server.mjs", "--no-open"], {
        cwd: new URL("../..", import.meta.url),
        env: { ...process.env, HOST: "127.0.0.1", PORT: String(port) },
        stdio: ["ignore", "pipe", "pipe"]
    });
    let output = "";
    child.stdout.on("data", chunk => output += chunk);
    child.stderr.on("data", chunk => output += chunk);
    const url = `http://127.0.0.1:${port}`;
    const deadline = Date.now() + 15_000;
    while (Date.now() < deadline) {
        if (child.exitCode !== null) throw new Error(output || `server exited with ${child.exitCode}`);
        try {
            const response = await fetch(`${url}/index.html`, { method: "HEAD" });
            if (response.ok) return { url, stop: () => child.kill() };
        } catch { }
        await new Promise(resolve => setTimeout(resolve, 50));
    }
    child.kill();
    throw new Error(`local server did not start: ${output}`);
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

function toMB(bytes) {
    return Number.isFinite(bytes) ? Number((bytes / 1024 / 1024).toFixed(2)) : null;
}

function toMs(seconds) {
    return Number.isFinite(seconds) ? Math.round(seconds * 1000) : null;
}

function summarizeCpuProfile(profile) {
    const nodes = new Map(profile.nodes.map(node => [node.id, node]));
    const selfMicros = new Map();
    for (let index = 0; index < profile.samples.length; index++) {
        const nodeId = profile.samples[index];
        selfMicros.set(nodeId, (selfMicros.get(nodeId) ?? 0) + (profile.timeDeltas[index] ?? 0));
    }
    return Array.from(selfMicros, ([nodeId, micros]) => {
        const callFrame = nodes.get(nodeId)?.callFrame ?? {};
        return {
            function: callFrame.functionName || "(anonymous)",
            url: shortUrl(callFrame.url),
            line: Number.isFinite(callFrame.lineNumber) ? callFrame.lineNumber + 1 : null,
            selfMs: Math.round(micros / 1000)
        };
    })
        .sort((left, right) => right.selfMs - left.selfMs)
        .slice(0, 30);
}

function shortUrl(url = "") {
    const marker = url.indexOf("/js/");
    return marker >= 0 ? url.slice(marker + 1) : url;
}

function assertBenchmarkCompleted(result, expectedCount) {
    if (result.theoremCount !== expectedCount) {
        throw new Error(`expected ${expectedCount} restored theorems, received ${result.theoremCount}`);
    }
    if (result.errorCount || result.inferingCount || result.checkingCount) {
        throw new Error(
            `validation did not finish cleanly: ${result.errorCount} error, `
            + `${result.inferingCount} infering, ${result.checkingCount} checking`
        );
    }
    const stats = result.workerStats;
    if (stats.coreCreated !== 1 || stats.assistCreated !== 0
        || stats.configure !== 1 || stats.configureSlots !== 0
        || stats.validate !== expectedCount || stats.truncate !== 0) {
        throw new Error(`unexpected Worker loading protocol: ${JSON.stringify(stats)}`);
    }
}

function appendTheoremToSave(encoded, theorem) {
    const saveLoader = Object.create(GameSaveLoad.prototype);
    saveLoader.storageKey = "deductrium-save";
    const parts = saveLoader.deserializeStr(encoded).split("-(=)-");
    if (parts.length !== 4) throw new Error(`expected 4 save sections, received ${parts.length}`);

    const saved = JSON.parse(parts[3]);
    if (Array.isArray(saved)) {
        saved.push(theorem);
    } else if (Array.isArray(saved?.items)) {
        saved.items.push({ kind: "theorem", value: theorem });
    } else {
        throw new Error("type-theory save section has no theorem items");
    }
    parts[3] = JSON.stringify(saved);
    return saveLoader.serializeStr(parts.join("-(=)-"));
}
