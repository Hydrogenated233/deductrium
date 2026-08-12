import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";

import { ASTParser } from "../../js/tt/astparser.js";
import { Core } from "../../js/tt/core.js";
import { TTCoreSession } from "../../js/tt/core-session.js";
import { initTypeSystem } from "../../js/tt/initial.js";
import { SemanticNbeTypeChecker } from "../../js/tt/nbe-checker.js";
import { createK609BenchmarkTheorems } from "../helpers/k609-workload.mjs";

const encoded = readFileSync(
    new URL("../fixtures/k609-one-formula-before-perm-master.txt", import.meta.url),
    "utf8"
);
const theoremValues = createK609BenchmarkTheorems(encoded);
const parser = new ASTParser();
const stopAfter = boundedInteger(
    process.env.TT_STOP_AFTER,
    theoremValues.length - 1,
    0,
    theoremValues.length - 1
);
const elaborationMaxNodes = boundedInteger(
    process.env.TT_SEMANTIC_ELABORATION_MAX_NODES,
    Core.semanticTypeElaborationMaxNodes,
    1
);
const outputMaxNodes = boundedInteger(
    process.env.TT_SEMANTIC_OUTPUT_MAX_NODES,
    256,
    1
);

const previous = {
    recursive: Core.semanticTypeCheckRecursive,
    recursiveMin: Core.semanticTypeCheckRecursiveMinDefinitions,
    elaborationMaxNodes: Core.semanticTypeElaborationMaxNodes,
    outputMaxNodes: Core.semanticTypeCheckMaxOutputNodes
};
const originalAssertion = Core.prototype.trySemanticTypeAssertion;
const originalSynthesis = Core.prototype.trySemanticTypeSynthesis;
const originalCheckerSynthesis = SemanticNbeTypeChecker.prototype.trySynthesize;
const originalCheckerCheck = SemanticNbeTypeChecker.prototype.tryCheck;
const probeStack = [];
let activeTheorem;

installCoverageProfiler();
Core.semanticTypeCheckRecursive = true;
Core.semanticTypeCheckRecursiveMinDefinitions = 0;
Core.semanticTypeElaborationMaxNodes = elaborationMaxNodes;
Core.semanticTypeCheckMaxOutputNodes = outputMaxNodes;

const session = new TTCoreSession();
session.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    disableSimpleFn: false,
    disableSimpleEq: false,
    inferDisplayMode: "_",
    timeout: Number.MAX_SAFE_INTEGER,
    language: "zh"
});

const totals = {
    validated: 0,
    pureSemanticSuccess: 0,
    rootFallbackReasons: {},
    recursive: createAttemptCounts(),
    checkerCalls: {}
};
const started = performance.now();

console.log("K609 high-output semantic coverage benchmark; timings are informational only.");
console.log(JSON.stringify({
    kind: "configuration",
    theoremCount: theoremValues.length,
    stopAfter,
    semanticTypeElaborationMaxNodes: elaborationMaxNodes,
    semanticTypeCheckMaxOutputNodes: outputMaxNodes
}));

try {
    for (let index = 0; index <= stopAfter; index++) {
        const ast = parser.parse(theoremValues[index]);
        activeTheorem = {
            index,
            name: definitionName(ast),
            root: undefined,
            recursive: createAttemptCounts(),
            checkerCalls: {},
            startedAt: performance.now()
        };

        const result = session.validate(index, ast);
        if (!result.ok) {
            throw new Error(`theorem ${index} (${activeTheorem.name}) failed: ${result.error}`);
        }

        const root = activeTheorem.root ?? {
            kind: "none",
            success: false,
            fallbackReason: "not-attempted",
            checkerCalls: []
        };
        const row = {
            kind: "theorem",
            index,
            name: activeTheorem.name,
            elapsedMs: round(performance.now() - activeTheorem.startedAt),
            pureSemantic: root.success,
            root: {
                kind: root.kind,
                fallbackReason: root.fallbackReason,
                checkerCalls: root.checkerCalls
            },
            recursive: activeTheorem.recursive,
            checkerCalls: activeTheorem.checkerCalls
        };

        totals.validated++;
        if (row.pureSemantic) totals.pureSemanticSuccess++;
        else increment(totals.rootFallbackReasons, root.fallbackReason);
        mergeAttemptCounts(totals.recursive, row.recursive);
        mergeCounts(totals.checkerCalls, row.checkerCalls);
        console.log(JSON.stringify(row));
        activeTheorem = undefined;
    }
} finally {
    restoreCoverageProfiler();
    Core.semanticTypeCheckRecursive = previous.recursive;
    Core.semanticTypeCheckRecursiveMinDefinitions = previous.recursiveMin;
    Core.semanticTypeElaborationMaxNodes = previous.elaborationMaxNodes;
    Core.semanticTypeCheckMaxOutputNodes = previous.outputMaxNodes;
}

console.log(JSON.stringify({
    kind: "summary",
    theoremCount: theoremValues.length,
    ...totals,
    pureSemanticFallback: totals.validated - totals.pureSemanticSuccess,
    elapsedMs: Math.round(performance.now() - started)
}, null, 2));

function installCoverageProfiler() {
    SemanticNbeTypeChecker.prototype.trySynthesize = function profiledSynthesis(...args) {
        const result = originalCheckerSynthesis.apply(this, args);
        recordCheckerCall("synthesize", result);
        return result;
    };
    SemanticNbeTypeChecker.prototype.tryCheck = function profiledCheck(...args) {
        const result = originalCheckerCheck.apply(this, args);
        recordCheckerCall("check", result);
        return result;
    };
    Core.prototype.trySemanticTypeAssertion = function profiledAssertion(...args) {
        const probe = createProbe("assertion");
        if (activeTheorem && !activeTheorem.root) activeTheorem.root = probe;
        return runProbe(probe, () => originalAssertion.apply(this, args));
    };
    Core.prototype.trySemanticTypeSynthesis = function profiledSynthesis(...args) {
        const isRoot = !!activeTheorem && !activeTheorem.root;
        const probe = createProbe(isRoot ? "synthesis" : "recursive-synthesis");
        if (isRoot) activeTheorem.root = probe;
        return runProbe(probe, () => originalSynthesis.apply(this, args));
    };
}

function restoreCoverageProfiler() {
    Core.prototype.trySemanticTypeAssertion = originalAssertion;
    Core.prototype.trySemanticTypeSynthesis = originalSynthesis;
    SemanticNbeTypeChecker.prototype.trySynthesize = originalCheckerSynthesis;
    SemanticNbeTypeChecker.prototype.tryCheck = originalCheckerCheck;
}

function createProbe(kind) {
    return { kind, success: false, fallbackReason: undefined, checkerCalls: [] };
}

function runProbe(probe, operation) {
    probeStack.push(probe);
    try {
        const result = operation();
        probe.success = !!result;
        probe.fallbackReason = probe.success ? undefined : classifyFallback(probe);
        return result;
    } finally {
        probeStack.pop();
        if (activeTheorem && probe.kind === "recursive-synthesis") {
            recordAttempt(activeTheorem.recursive, probe);
        }
    }
}

function recordCheckerCall(method, result) {
    const probe = probeStack.at(-1);
    if (!probe) return;
    const call = result.status === "success"
        ? { method, status: "success", outputNodes: countNodes(result.type) }
        : { method, status: result.status, code: result.code };
    probe.checkerCalls.push(call);
    if (!activeTheorem) return;
    increment(activeTheorem.checkerCalls, call.status === "success" ? "success" : call.code);
}

function classifyFallback(probe) {
    if (!probe.checkerCalls.length) return "input-budget";
    const lastCall = probe.checkerCalls.at(-1);
    if (lastCall.status !== "success") return lastCall.code;
    if (probe.kind === "assertion"
        && !probe.checkerCalls.some(call => call.method === "check")) {
        return "expected-type-not-universe";
    }
    return "output-budget";
}

function createAttemptCounts() {
    return { attempts: 0, success: 0, fallbackReasons: {} };
}

function recordAttempt(counts, probe) {
    counts.attempts++;
    if (probe.success) counts.success++;
    else increment(counts.fallbackReasons, probe.fallbackReason);
}

function mergeAttemptCounts(target, source) {
    target.attempts += source.attempts;
    target.success += source.success;
    mergeCounts(target.fallbackReasons, source.fallbackReasons);
}

function mergeCounts(target, source) {
    for (const [name, count] of Object.entries(source)) {
        target[name] = (target[name] ?? 0) + count;
    }
}

function increment(counts, name) {
    counts[name] = (counts[name] ?? 0) + 1;
}

function definitionName(ast) {
    return ast.type === ":=" && ast.nodes?.[0]?.type === "var"
        ? ast.nodes[0].name
        : "<anonymous>";
}

function countNodes(ast) {
    if (!ast) return 0;
    let count = 0;
    const pending = [ast];
    while (pending.length) {
        const current = pending.pop();
        count++;
        for (const node of current.nodes ?? []) pending.push(node);
    }
    return count;
}

function boundedInteger(value, fallback, minimum, maximum = Number.MAX_SAFE_INTEGER) {
    const parsed = Number(value);
    if (!Number.isFinite(parsed)) return fallback;
    return Math.min(maximum, Math.max(minimum, Math.floor(parsed)));
}

function round(value) {
    return Number(value.toFixed(3));
}
