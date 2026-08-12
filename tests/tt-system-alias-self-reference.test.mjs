import assert from "node:assert/strict";

import { Core } from "../js/tt/core.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const rules = initTypeSystem();
const transleftrightComputeIndex = 158;
assert.equal(rules[transleftrightComputeIndex].id, "eq.transleftright");
assert.equal(rules[transleftrightComputeIndex].ast.type, "===");

// This prefix contains the transleftright and transeq aliases while keeping
// the regression focused on the first startup rule that used to loop.
const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: [...new Set(rules.slice(0, 167).map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 10_000,
    language: "zh"
});

const definitionHead = definition => {
    let head = definition;
    while (head?.type === "apply") head = head.nodes?.[0];
    return head;
};

for (const name of ["eq", "refl", "transleftright", "transeq"]) {
    const definition = engine.core.state.sysDefs[name];
    assert.ok(definition, `missing system definition ${name}`);
    const head = definitionHead(definition);
    assert.equal(
        head?.type === "var" && !head.bondVarId && head.name === name,
        false,
        `system alias ${name} must not be stored with itself as its definition head`
    );
}

const originalAssign = Core.assign;
let assignments = 0;
const assignmentBudget = 4_096;
Core.assign = function (...args) {
    assignments++;
    if (assignments > assignmentBudget) {
        throw new Error("transleftright computation exceeded the assignment budget");
    }
    return originalAssign.apply(this, args);
};

try {
    assert.ok(engine.core.checkType(
        Core.clone(rules[transleftrightComputeIndex].ast),
        [],
        false
    ));
} finally {
    Core.assign = originalAssign;
}

assert.ok(assignments <= assignmentBudget);

console.log("system alias self-reference regression passed");
