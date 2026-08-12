import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";

import { ASTParser } from "../../js/tt/astparser.js";
import { Core } from "../../js/tt/core.js";
import { TTCoreSession } from "../../js/tt/core-session.js";
import { initTypeSystem } from "../../js/tt/initial.js";
import { createK609BenchmarkTheorems } from "../helpers/k609-workload.mjs";

const encoded = readFileSync(
    new URL("../fixtures/k609-one-formula-before-perm-master.txt", import.meta.url),
    "utf8"
);
const theoremValues = createK609BenchmarkTheorems(encoded);
const parser = new ASTParser();
const profileFrom = Number(process.env.TT_PROFILE_FROM ?? 0);
const profileTo = Number(process.env.TT_PROFILE_TO ?? theoremValues.length - 1);
const profileAll = process.env.TT_PROFILE === "1";
const stopAfter = Number(process.env.TT_STOP_AFTER ?? -1);
const traceSemanticTypecheck = process.env.TT_TRACE_SEMANTIC_TYPECHECK === "1";
const semanticRecursiveFrom = process.env.TT_SEMANTIC_TYPECHECK_RECURSIVE_FROM === undefined
    ? null
    : Number(process.env.TT_SEMANTIC_TYPECHECK_RECURSIVE_FROM);
const semanticRecursiveTo = Number(
    process.env.TT_SEMANTIC_TYPECHECK_RECURSIVE_TO ?? semanticRecursiveFrom ?? -1
);

const methods = [
    ["checker.synthesize", "semanticTypeChecker", "trySynthesize"],
    ["checker.check", "semanticTypeChecker", "tryCheck"],
    ["kernel.equal", "semanticKernel", "tryEqualResult"],
    ["kernel.normalize", "semanticKernel", "tryNormalize"],
    ["kernel.whnf", "semanticKernel", "tryWhnf"]
];
const profileState = new Map();
let activeProfile = null;
let activeTheoremIndex = -1;
const semanticTrace = [];

const session = new TTCoreSession();
if (process.env.TT_SEMANTIC_TYPECHECK_RECURSIVE !== undefined) {
    Core.semanticTypeCheckRecursive = process.env.TT_SEMANTIC_TYPECHECK_RECURSIVE !== "0";
}
session.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    disableSimpleFn: false,
    disableSimpleEq: false,
    inferDisplayMode: "_",
    timeout: Number.MAX_SAFE_INTEGER,
    language: "zh"
});
if (profileAll) installProfiler();
if (traceSemanticTypecheck) installSemanticTypecheckTrace();
if (traceSemanticTypecheck) installErrorTrace();

const started = performance.now();
for (let index = 0; index < theoremValues.length; index++) {
    activeTheoremIndex = index;
    if (semanticRecursiveFrom !== null) {
        Core.semanticTypeCheckRecursive = index >= semanticRecursiveFrom
            && index <= semanticRecursiveTo;
    }
    activeProfile = profileAll && index >= profileFrom && index <= profileTo
        ? createSample(index)
        : null;
    const result = session.validate(index, parser.parse(theoremValues[index]));
    if (!result.ok) {
        if (traceSemanticTypecheck) {
            console.error(JSON.stringify(semanticTrace.slice(-80), null, 2));
        }
        throw new Error(`theorem ${index} failed: ${result.error}`);
    }
    if (activeProfile) {
        activeProfile.elapsedMs = performance.now() - activeProfile.startedAt;
        profileState.set(index, activeProfile);
        activeProfile = null;
    }
    if ((index >= profileTo && profileAll) || (stopAfter >= 0 && index >= stopAfter)) break;
}

function installSemanticTypecheckTrace() {
    const original = Core.prototype.trySemanticTypeSynthesis;
    Core.prototype.trySemanticTypeSynthesis = function tracedSemanticTypeSynthesis(ast, context, options) {
        const result = original.call(this, ast, context, options);
        if (activeTheoremIndex >= semanticRecursiveFrom
            && parser.stringify(ast).includes("ind_nat")) {
            console.error("SEMANTIC_IND_NAT", parser.stringify(ast),
                result ? parser.stringify(result) : "<miss>",
                ast.checked ? parser.stringify(ast.checked) : "<no checked>");
        }
        if (activeTheoremIndex >= semanticRecursiveFrom && result) {
            semanticTrace.push({
                theorem: activeTheoremIndex,
                term: parser.stringify(ast),
                type: parser.stringify(result),
                context: context.map(([name, , id]) => `${name}:${id}`).join(",")
            });
            if (semanticTrace.length > 200) semanticTrace.shift();
        }
        return result;
    };
}

function installErrorTrace() {
    const original = Core.prototype.error;
    Core.prototype.error = function tracedError(ast, msg, stop) {
        if (activeTheoremIndex >= semanticRecursiveFrom
            && String(msg).includes("函数参数类型不合法")) {
            console.error("SEMANTIC_ERROR_AST", parser.stringify(ast));
            for (const [index, child] of (ast.nodes ?? []).entries()) {
                console.error("SEMANTIC_ERROR_CHILD", index, parser.stringify(child),
                    child?.checked ? parser.stringify(child.checked) : "<no checked>");
            }
        }
        return original.call(this, ast, msg, stop);
    };
}

if (profileAll) {
    const rows = [...profileState.values()].sort((a, b) => b.elapsedMs - a.elapsedMs);
    console.log(JSON.stringify({
        profileFrom,
        profileTo: Math.min(profileTo, theoremValues.length - 1),
        elapsedMs: Math.round(performance.now() - started),
        rows: rows.map(row => ({
            index: row.index,
            elapsedMs: round(row.elapsedMs),
            calls: Object.fromEntries(
                Object.entries(row.methods).map(([label, sample]) => [label, sample.calls])
            ),
            methodMs: Object.fromEntries(Object.entries(row.methods)
                .map(([label, sample]) => [label, round(sample.elapsedMs)])
                .filter(([, value]) => value > 0))
        }))
    }, null, 2));
}

function createSample(index) {
    return {
        index,
        startedAt: performance.now(),
        elapsedMs: 0,
        methods: Object.fromEntries(methods.map(([label]) => [label, { calls: 0, elapsedMs: 0 }]))
    };
}

function installProfiler() {
    for (const [label, ownerName, methodName] of methods) {
        const owner = session.engine.core[ownerName];
        const original = owner[methodName];
        if (typeof original !== "function") continue;
        owner[methodName] = function profiledMethod(...args) {
            if (!activeProfile) return original.apply(this, args);
            const sample = activeProfile.methods[label];
            sample.calls++;
            const startedAt = performance.now();
            try {
                return original.apply(this, args);
            } finally {
                sample.elapsedMs += performance.now() - startedAt;
            }
        };
    }

    const clone = Core.clone;
    Core.clone = function profiledClone(...args) {
        if (!activeProfile) return clone.apply(this, args);
        const startedAt = performance.now();
        try {
            return clone.apply(this, args);
        } finally {
            const sample = activeProfile.methods.clone ??= { calls: 0, elapsedMs: 0 };
            sample.calls++;
            sample.elapsedMs += performance.now() - startedAt;
        }
    };
}

function round(value) {
    return Number(value.toFixed(3));
}
