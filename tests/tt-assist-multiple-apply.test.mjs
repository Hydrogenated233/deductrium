import assert from "node:assert/strict";

import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
};
const options = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};
const lockedOptions = {
    ...options,
    disableMultipleApply: true
};

const engine = new TTAssistEngine();
engine.configure(config);
const target = "ΠA:U,Πf:Πx:A,Πy:A,A,Πx:A,Πy:A,A";
const originalLog = console.log;
try {
    console.log = () => { };
    let snapshot = engine.start(target, options);
    for (const command of ["intro A", "intro f", "intro x", "intro y"]) {
        snapshot = engine.apply(command);
    }
    assert.ok(snapshot.tactics.includes("apply f"),
        "multi-argument function f should be recommended at the final goal");
    snapshot = engine.apply("apply f");
    assert.equal(snapshot.goals.length, 2,
        "applying the recommended multi-argument function should create two goals");

    snapshot = engine.start("Πf:True→True→False,False", options);
    snapshot = engine.apply("intro f");
    assert.ok(snapshot.tactics.includes("apply f"),
        "an arrow-notation multi-argument function should be recommended");
    snapshot = engine.apply("apply f");
    assert.deepEqual(snapshot.goals.map(goal => goal.type.name), ["True", "True"]);

    snapshot = engine.start("Πf:True→True→False,False", lockedOptions);
    snapshot = engine.apply("intro f");
    assert.ok(!snapshot.tactics.includes("apply f"),
        "multi-argument apply should remain unavailable until ttapply2 is unlocked");

    const pureEngine = new TTAssistEngine();
    pureEngine.configure(config);
    snapshot = pureEngine.start("Πf:True→True→False,False", options);
    snapshot = pureEngine.apply("intro f");
    assert.ok(snapshot.tactics.includes("apply f"),
        "pure NbE should recommend the multi-argument function");
    snapshot = pureEngine.apply("apply f");
    assert.deepEqual(snapshot.goals.map(goal => goal.type.name), ["True", "True"]);
} finally {
    console.log = originalLog;
}

console.log("multi-argument apply recommendation regression passed");
