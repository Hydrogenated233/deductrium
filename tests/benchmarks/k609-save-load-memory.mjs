import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";

import { ASTParser } from "../../js/tt/astparser.js";
import { Core } from "../../js/tt/core.js";
import { TTCoreSession } from "../../js/tt/core-session.js";
import { initTypeSystem } from "../../js/tt/initial.js";
import { SemanticNbeKernel } from "../../js/tt/nbe-kernel.js";
import {
    createK609BenchmarkTheorems,
    decodeK609Theorems
} from "../helpers/k609-workload.mjs";

const encoded = readFileSync(
    new URL("../fixtures/k609-one-formula-before-perm-master.txt", import.meta.url),
    "utf8"
);
const savedTheorems = decodeK609Theorems(encoded);
const theoremValues = createK609BenchmarkTheorems(encoded);
const parser = new ASTParser();
const semanticProfile = new Map();
if (process.env.TT_SEMANTIC_PROFILE === "1") installSemanticProfiler();
Core.semanticTypeCheckAttempts = 0;
Core.semanticTypeCheckHits = 0;
Core.semanticTypeCheckFastPathHits = 0;
if (process.env.TT_SEMANTIC_TYPECHECK_RECURSIVE !== undefined) {
    Core.semanticTypeCheckRecursive = process.env.TT_SEMANTIC_TYPECHECK_RECURSIVE !== "0";
}
const session = new TTCoreSession();
session.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    disableSimpleFn: false,
    disableSimpleEq: false,
    inferDisplayMode: "_",
    timeout: Number.MAX_SAFE_INTEGER,
    language: "zh"
});

const started = performance.now();
let peakHeapBytes = process.memoryUsage().heapUsed;
let peakRssBytes = process.memoryUsage().rss;

for (let index = 0; index < theoremValues.length; index++) {
    const result = session.validate(index, parser.parse(theoremValues[index]));
    if (!result.ok) throw new Error(`theorem ${index} failed: ${result.error}`);

    const memory = process.memoryUsage();
    peakHeapBytes = Math.max(peakHeapBytes, memory.heapUsed);
    peakRssBytes = Math.max(peakRssBytes, memory.rss);
}

const finalMemory = process.memoryUsage();
console.log("K609 save-load benchmark; memory and timing values are informational only.");
console.log(JSON.stringify({
    savedTheorems: savedTheorems.length,
    benchmarkTheorems: theoremValues.length,
    appendedTheorem: "permEqvV87K_pg10",
    kernel: "nbe",
    semanticTypeCheckRecursive: Core.semanticTypeCheckRecursive,
    semanticTypeElaborationMaxNodes: Core.semanticTypeElaborationMaxNodes,
    semanticTypeCheckMaxOutputNodes: Core.semanticTypeCheckMaxOutputNodes,
    semanticTypeCheckAttempts: Core.semanticTypeCheckAttempts,
    semanticTypeCheckHits: Core.semanticTypeCheckHits,
    semanticTypeCheckFastPathHits: Core.semanticTypeCheckFastPathHits,
    semanticDefinitions: session.engine.core.semanticKernel.definitionCount,
    semanticDefinitionRevision: session.engine.core.semanticKernel.revision,
    semanticProfile: process.env.TT_SEMANTIC_PROFILE === "1"
        ? Array.from(semanticProfile.entries())
            .sort(([, left], [, right]) => right.attempts - left.attempts)
            .slice(0, 30)
            .map(([heads, counts]) => ({ heads, ...counts }))
        : undefined,
    elapsedMs: Math.round(performance.now() - started),
    peakHeapMB: toMB(peakHeapBytes),
    finalHeapMB: toMB(finalMemory.heapUsed),
    peakRssMB: toMB(peakRssBytes),
    finalRssMB: toMB(finalMemory.rss)
}, null, 2));

function toMB(bytes) {
    return Number((bytes / 1024 / 1024).toFixed(2));
}

function installSemanticProfiler() {
    const original = SemanticNbeKernel.prototype.tryEqual;
    SemanticNbeKernel.prototype.tryEqual = function profiledTryEqual(left, right, ...args) {
        const heads = `${headName(left)} ~ ${headName(right)}`;
        const counts = semanticProfile.get(heads) ?? { attempts: 0, hits: 0, falseResults: 0, fallbacks: 0 };
        counts.attempts++;
        const result = original.call(this, left, right, ...args);
        if (result === true) counts.hits++;
        else if (result === false) counts.falseResults++;
        else counts.fallbacks++;
        semanticProfile.set(heads, counts);
        return result;
    };
}

function headName(ast) {
    let head = ast;
    while (head?.type === "apply") head = head.nodes?.[0];
    if (!head) return "<missing>";
    if (head.type === "var") return head.name || "<var>";
    return head.type || "<node>";
}
