import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";

import { Core } from "../../js/tt/core.js";
import {
    SandboxEnvironment,
    creativeSandboxSystemRuleIds
} from "../../js/tt/sandbox.js";

const source = readFileSync(
    new URL("../fixtures/hit3-expansion-stress.txt", import.meta.url),
    "utf8"
).trim();
const timeoutMs = positiveInteger(process.env.TT_BENCHMARK_TIMEOUT_MS, 60_000);
const globalTimeoutMs = positiveInteger(process.env.TT_GLOBAL_TIMEOUT_MS, 10_000);
globalThis.gc?.();
const beforeMemory = process.memoryUsage();
const countNodes = ast => {
    let count = 0;
    const stack = [ast];
    const seen = new WeakSet();
    while (stack.length) {
        const node = stack.pop();
        if (!node || typeof node !== "object" || seen.has(node)) continue;
        seen.add(node);
        count++;
        for (const child of node.nodes ?? []) stack.push(child);
    }
    return count;
};
const countBundleNodes = bundle => [
    bundle.type?.[1],
    ...(bundle.auxiliaryTypes ?? []).flatMap(([, type]) => [type]),
    ...(bundle.constructors ?? []).flatMap(([, type]) => [type]),
    bundle.eliminator?.[1],
    bundle.recursor?.[1],
    ...(bundle.definitions ?? []).flatMap(([, definition]) => [definition]),
    ...Object.values(bundle.computeRules ?? {}).flatMap(rules =>
        rules.flatMap(rule => [...rule.pattern, rule.result])
    )
].filter(Boolean).reduce((total, ast) => total + countNodes(ast), 0);

const previousGlobalTimeout = Core.timeout;
Core.timeout = globalTimeoutMs;
const environment = new SandboxEnvironment({
    systemRuleIds: creativeSandboxSystemRuleIds,
    validationTimeoutMs: timeoutMs
});
const validationStarted = performance.now();
let registration = "ok";
let error;
let bundle;
try {
    const result = environment.add(source);
    bundle = result.bridge?.inductives?.[0];
    if (!result.ok) {
        registration = result.status;
        error = result.error;
    }
} catch (cause) {
    registration = "error";
    error = cause instanceof Error ? cause.message : String(cause);
} finally {
    Core.timeout = previousGlobalTimeout;
}
const validationMs = performance.now() - validationStarted;
const rawMemory = process.memoryUsage();
globalThis.gc?.();
const liveMemory = process.memoryUsage();

console.log("3D HIT expansion benchmark; timings and heap are informational only.");
console.log(JSON.stringify({
    sourceChars: source.length,
    pathLevels: bundle?.metadata?.pathLevels?.length ?? 0,
    generatedNames: bundle?.generatedNames?.length ?? 0,
    bundleAstNodes: bundle ? countBundleNodes(bundle) : 0,
    globalCoreTimeoutMs: globalTimeoutMs,
    sandboxValidationTimeoutMs: timeoutMs,
    registration,
    error,
    validationMs: round(validationMs),
    heapBeforeMB: toMB(beforeMemory.heapUsed),
    heapAfterValidationMB: toMB(rawMemory.heapUsed),
    heapAfterGcMB: toMB(liveMemory.heapUsed),
    rssAfterValidationMB: toMB(rawMemory.rss),
    rssAfterGcMB: toMB(liveMemory.rss)
}, null, 2));

if (registration !== "ok") process.exitCode = 1;

function positiveInteger(value, fallback) {
    const parsed = Number(value);
    return Number.isInteger(parsed) && parsed > 0 ? parsed : fallback;
}

function round(value) {
    return Number(value.toFixed(2));
}

function toMB(bytes) {
    return Number((bytes / 1024 / 1024).toFixed(2));
}
