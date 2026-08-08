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

engine.start("Even 0", options);
assert.throws(() => engine.apply("not-a-tactic"), /未知的证明策略/);

// A failed command must leave the assistant session usable, just like the
// original synchronous proof assistant did after displaying its error.
const snapshot = engine.apply("exact even0");
assert.equal(snapshot.goals.length, 0);
assert.match(engine.qed().proof, /even0/);

console.log("proof-assistant invalid-command recovery regression passed");
