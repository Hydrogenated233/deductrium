import { performance } from "node:perf_hooks";

import { ASTParser } from "../../js/tt/astparser.js";
import { TTCoreSession } from "../../js/tt/core-session.js";
import { initTypeSystem } from "../../js/tt/initial.js";

const parser = new ASTParser();
const session = new TTCoreSession();
let configureCalls = 0;
const configure = session.engine.configure.bind(session.engine);
session.engine.configure = (...args) => {
    configureCalls++;
    return configure(...args);
};

const configureStarted = performance.now();
session.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});
const configureMs = performance.now() - configureStarted;

function measure(index, source) {
    const started = performance.now();
    const result = session.validate(index, parser.parse(source));
    const roundTripMs = performance.now() - started;
    if (!result.ok) throw new Error(`${source} failed: ${result.error ?? "unknown error"}`);
    return { roundTripMs, checkMs: result.durationMs };
}

const first = measure(0, "True");
const append = measure(1, "base");
const repeated = [];
for (let run = 0; run < 40; run++) {
    repeated.push(measure(1, run % 2 ? "True" : "base"));
}

const summarize = values => {
    const sorted = [...values].sort((left, right) => left - right);
    const percentile = ratio => sorted[Math.min(sorted.length - 1, Math.floor(sorted.length * ratio))];
    return {
        min: Number(sorted[0].toFixed(3)),
        median: Number(percentile(0.5).toFixed(3)),
        p95: Number(percentile(0.95).toFixed(3)),
        max: Number(sorted[sorted.length - 1].toFixed(3))
    };
};

console.log("Short-expression Worker-session benchmark; timings are informational only.");
console.log(JSON.stringify({
    configureCalls,
    configureMs: Number(configureMs.toFixed(3)),
    first,
    append,
    repeatedRoundTripMs: summarize(repeated.map(sample => sample.roundTripMs)),
    repeatedCheckMs: summarize(repeated.map(sample => sample.checkMs))
}, null, 2));
