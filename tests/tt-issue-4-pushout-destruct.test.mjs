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
let snapshot = engine.start("Πa:U,Πb:U,(Join a b)->(Join b a)", options);
for (const command of ["expand Join", "intro a", "intro b", "intro h"]) {
    snapshot = engine.apply(command);
}

assert.doesNotThrow(() => {
    snapshot = engine.apply("destruct h");
}, "Pushout destruct must specialize its hidden parameters before creating branches");
assert.equal(snapshot.goals.length, 3,
    "Pushout destruct should create pol, por, and glue constructor goals");
for (const goal of snapshot.goals) {
    assert.doesNotMatch(JSON.stringify(goal), /\?nbe\d+/,
        "Pushout branch goals must not retain unresolved semantic metas");
}

console.log("GitHub issue #4 Pushout destruct regression passed");
