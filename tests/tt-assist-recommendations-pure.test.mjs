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
const originalWarn = console.warn;

try {
    console.log = () => { };
    console.warn = () => { };
    let snapshot = engine.start("true=true", options);
    assert.equal(snapshot.tactics.includes("rfl"), true,
        "definitionally equal endpoints must recommend rfl");

    snapshot = engine.start("Bool→Bool", options);
    snapshot = engine.apply("intro h");
    assert.equal(snapshot.tactics.includes("apply h"), true,
        "a context value matching the goal must be recommended");

    snapshot = engine.start("(True→True→False)→False", options);
    snapshot = engine.apply("intro f");
    assert.equal(snapshot.tactics.includes("apply f"), true,
        "a multi-argument context function ending in the goal must be recommended");

    snapshot = engine.start("Πa:U,a→False", options);
    snapshot = engine.apply("intro a");
    snapshot = engine.apply("intro x");
    assert.equal(snapshot.tactics.includes("apply a"), false);
    assert.equal(snapshot.tactics.includes("apply x"), false,
        "unsupported or mismatched candidates must simply be omitted");

} finally {
    console.log = originalLog;
    console.warn = originalWarn;
}

console.log("pure NbE tactic-recommendation regression passed");
