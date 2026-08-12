import assert from "node:assert/strict";

import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

const result = engine.check("λp:true=true,@inveq _ _ _ _ p");

assert.equal(result.ok, true, result.error);
assert.doesNotMatch(result.error ?? "", /semantic-nbe-unsupported/);

console.log("pure NbE explicit-hole elaboration regression passed");
