import assert from "node:assert/strict";

import { Core } from "../js/tt/core.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const rules = initTypeSystem();
const computeRuleIndex = 158;
assert.equal(rules[computeRuleIndex].id, "eq.transleftright");

const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: [...new Set(rules.slice(0, 167).map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 10_000,
    language: "zh"
});

const core = engine.core;
const checked = core.checkType(
    Core.clone(rules[computeRuleIndex].ast),
    [],
    false
);
assert.ok(checked);

console.log("pure NbE system compute-rule regression passed");
