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

const originalLog = console.log;
const originalWarn = console.warn;
try {
    console.log = () => { };
    console.warn = () => { };
    engine.start("((True+True) ≃ Bool)", options);
    engine.apply("expand eqv");
    engine.apply("ex");
    engine.apply("intro h");

    const snapshot = engine.apply("destruct h");
    const goals = snapshot.goals;
    assert.equal(goals.length, 3);
    assert.equal(parser.stringify(goals[0].context[0][1]), "True");
    assert.equal(parser.stringify(goals[1].context[0][1]), "True");
} finally {
    console.log = originalLog;
    console.warn = originalWarn;
}

console.log("proof-assistant Sum destruct regression passed");
