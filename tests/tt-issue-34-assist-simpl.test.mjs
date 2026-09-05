import assert from "node:assert/strict";

import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const engine = new TTAssistEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 60_000,
    language: "zh"
});

engine.start(
    "Πa:U,Πb:U,Πc:U,Πd:U,a≃b→c≃d→(a×c)≃(b×d)",
    {
        disableMultipleApply: false,
        disableDestructConds: false,
        disableDestructEq: false
    }
);
for (const command of [
    "intro a",
    "intro b",
    "intro c",
    "intro d",
    "intro h1",
    "intro h2",
    "expand eqv",
    "ex",
    "intro h3",
    "case",
    "apply pr0 h1",
    "apply pr0 h3",
    "apply pr0 h2",
    "apply pr1 h3"
]) {
    engine.apply(command);
}

const before = engine.snapshot();
const beforeGoal = before.goals[0]?.type;
assert.ok(beforeGoal, "the reproduction must leave one Sigma/product goal");
assert.doesNotThrow(
    () => engine.apply("simpl"),
    "simpl should be a no-op when the current top-level goal is already in WHNF"
);
const after = engine.snapshot();
assert.equal(after.goals.length, 1);
assert.equal(after.goals[0].type.type, beforeGoal.type);
assert.equal(after.error, undefined);

console.log("issue #34 top-level WHNF simpl regression passed");
