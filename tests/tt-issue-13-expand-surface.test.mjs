import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
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

const snapshot = engine.apply.bind(engine);
engine.start("not(isProp Bool)", options);
const expanded = snapshot("expand isProp");

assert.equal(
    parser.stringify(expanded.goals[0].type),
    "(not (Πx:Bool,(Πy:Bool,(x=y))))",
    "expand isProp must not unfold the unrelated outer not definition"
);
assert.equal(expanded.history.at(-1), "expand isProp");

console.log("GitHub issue #13 expand surface regression passed");
