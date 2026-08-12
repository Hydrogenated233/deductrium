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

const options = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};

const originalLog = console.log;
try {
    console.log = () => { };
    let snapshot = engine.start(
        "pr0 (id2eqv rfl)=λx:True.x",
        options
    );
    assert.ok(snapshot.tactics.includes("simpl"));

    snapshot = engine.apply("simpl");
    assert.ok(snapshot.tactics.includes("fnext"),
        "the normalized function equality should recommend fnext");

    snapshot = engine.apply("fnext");
    assert.equal(snapshot.goals.length, 1);
    assert.ok(snapshot.tactics.some(tactic => tactic.startsWith("intro ")),
        "fnext should expose the pointwise equality goal");

    const intro = snapshot.tactics.find(tactic => tactic.startsWith("intro "));
    assert.ok(intro);
    snapshot = engine.apply(intro);
    if (snapshot.tactics.includes("simpl")) snapshot = engine.apply("simpl");
    snapshot = engine.apply("rfl");
    assert.equal(snapshot.goals.length, 0);
} finally {
    console.log = originalLog;
}

console.log("pure NbE fnext proof-assistant regression passed");
