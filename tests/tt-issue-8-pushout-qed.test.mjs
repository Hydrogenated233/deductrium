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

const engine = new TTAssistEngine();
engine.configure(config);
// Replay the actual issue sequence in one session.
engine.start("Πa:U0,Πb:U0,(Join a b)->(Join b a)", options);
for (const command of [
    "intro a",
    "intro b",
    "expand Join",
    "intro h",
    "destruct h",
    "right",
    "apply hl",
    "left",
    "apply hr",
    "simpl",
    "eq",
    "destruct hg",
    "simpl",
    "apply inveq",
    "apply glue(bXa)pr0 pr1(hg1,hg0)"
]) engine.apply(command);

const result = engine.qed();
assert.match(result.theorem, /Join/);
assert.match(result.proof, /ind_Pushout/);

console.log("GitHub issue #8 Pushout qed regression reproducer passed");
