import { performance } from "node:perf_hooks";

import { SemanticNbeTypeChecker } from "../../js/tt/nbe-checker.js";
import { SemanticNbeKernel } from "../../js/tt/nbe-kernel.js";

const maxDepth = positiveInteger(process.env.SCOPED_SYNTAX_DEPTH, 2_000);
const depths = [100, 500, 1_000, maxDepth]
    .filter((depth, index, values) => depth > 0 && values.indexOf(depth) === index)
    .sort((left, right) => left - right);

console.log("Scoped-syntax telescope benchmark; timing is informational only.");
for (const depth of depths) {
    const kernel = new SemanticNbeKernel();
    const normalizationStart = performance.now();
    const normalized = kernel.tryNormalize(telescope(depth), [], { maxSteps: 10_000_000 });
    const normalizationElapsedMs = performance.now() - normalizationStart;

    const checker = new SemanticNbeTypeChecker(kernel);
    const checkerStart = performance.now();
    const checked = checker.trySynthesize(checkerTelescope(depth), [], { maxSteps: 10_000_000 });
    const checkerElapsedMs = performance.now() - checkerStart;

    console.log(JSON.stringify({
        depth,
        normalized: !!normalized,
        normalizationElapsedMs: round(normalizationElapsedMs),
        checkerStatus: checked.status,
        checkerElapsedMs: round(checkerElapsedMs)
    }));
}

function telescope(depth) {
    let body = variable("True");
    for (let index = 0; index < depth; index++) {
        body = {
            type: "P",
            name: `x${index}`,
            bondVarId: index + 1,
            nodes: [variable("U"), body]
        };
    }
    return body;
}

function checkerTelescope(depth) {
    let body = variable("U");
    for (let index = 0; index < depth; index++) {
        body = {
            type: "P",
            name: `x${index}`,
            bondVarId: index + 1,
            nodes: [variable("U"), body]
        };
    }
    return body;
}

function variable(name) {
    return { type: "var", name };
}

function positiveInteger(value, fallback) {
    const parsed = Number(value);
    return Number.isInteger(parsed) && parsed > 0 ? parsed : fallback;
}

function round(value) {
    return Number(value.toFixed(2));
}
