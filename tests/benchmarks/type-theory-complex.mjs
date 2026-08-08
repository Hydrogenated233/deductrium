import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";

import { ASTParser } from "../../js/tt/astparser.js";
import { TTCoreSession } from "../../js/tt/core-session.js";
import { initTypeSystem } from "../../js/tt/initial.js";

const parser = new ASTParser();
const statements = readFileSync(new URL("../fixtures/hott-complex.txt", import.meta.url), "utf8")
    .split(/\r?\n\s*\r?\n/)
    .map(statement => statement.trim())
    .filter(Boolean);

const runCount = positiveInteger(process.env.BENCHMARK_RUNS, 3);
const timeoutMs = positiveInteger(process.env.TT_BENCHMARK_TIMEOUT_MS, 60_000);
const baseConfig = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    disableSimpleFn: false,
    disableSimpleEq: false,
    inferDisplayMode: "_",
    timeout: timeoutMs,
    language: "zh"
};

const setupSamples = [];
const samples = statements.map(() => ({ clone: [], check: [], total: [] }));
let labels = [];

for (let run = 0; run < runCount; run++) {
    const session = new TTCoreSession();
    const runLabels = [];
    const setupStarted = performance.now();
    session.configure(baseConfig);
    setupSamples.push(performance.now() - setupStarted);

    for (let index = 0; index < statements.length; index++) {
        const ast = parser.parse(statements[index]);
        const label = ast.type === ":=" && ast.nodes?.[0]?.type === "var"
            ? ast.nodes[0].name
            : `statement-${index + 1}`;
        runLabels.push(label);

        const request = { index, ast };
        const cloneStarted = performance.now();
        const clonedRequest = structuredClone(request);
        let cloneMs = performance.now() - cloneStarted;

        const checkStarted = performance.now();
        const result = session.validate(clonedRequest.index, clonedRequest.ast);
        const checkMs = performance.now() - checkStarted;

        const responseCloneStarted = performance.now();
        const clonedResult = structuredClone(result);
        cloneMs += performance.now() - responseCloneStarted;

        if (!clonedResult.ok) {
            throw new Error(`${label} failed during benchmark: ${clonedResult.error}`);
        }
        if (clonedResult.timeout) {
            throw new Error(`${label} exceeded the ${timeoutMs} ms benchmark timeout`);
        }

        samples[index].clone.push(cloneMs);
        samples[index].check.push(checkMs);
        samples[index].total.push(cloneMs + checkMs);
    }

    labels = runLabels;
}

const rows = samples.map((sample, index) => ({
    case: labels[index],
    clone: median(sample.clone),
    check: median(sample.check),
    total: median(sample.total)
}));
rows.push({
    case: "TOTAL",
    clone: sum(rows, "clone"),
    check: sum(rows, "check"),
    total: sum(rows, "total")
});

console.log(`Complex HoTT benchmark: median of ${runCount} run(s), timeout ${timeoutMs} ms`);
console.log(`Persistent Worker setup: ${round(median(setupSamples))} ms (once per system configuration)`);
console.log("Timing values are informational only; no machine-specific threshold is asserted.\n");
console.table(rows.map(row => ({
    case: row.case,
    "structuredClone ms": round(row.clone),
    "check ms": round(row.check),
    "total ms": round(row.total)
})));

function positiveInteger(value, fallback) {
    const parsed = Number(value);
    return Number.isInteger(parsed) && parsed > 0 ? parsed : fallback;
}

function median(values) {
    const ordered = [...values].sort((a, b) => a - b);
    const middle = Math.floor(ordered.length / 2);
    return ordered.length % 2 ? ordered[middle] : (ordered[middle - 1] + ordered[middle]) / 2;
}

function sum(rows, key) {
    return rows.reduce((total, row) => total + row[key], 0);
}

function round(value) {
    return Number(value.toFixed(2));
}
