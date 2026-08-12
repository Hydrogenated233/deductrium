import assert from "node:assert/strict";

import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const engine = new TTAssistEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

let snapshot = engine.start("Πx:True,x=x", {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
});
assert.equal(snapshot.goals.length, 1);
snapshot = engine.apply("intro x");
assert.equal(snapshot.goals.length, 1);
snapshot = engine.apply("rfl");
assert.equal(snapshot.goals.length, 0);

console.log("proof-assistant native NbE state regression passed");
