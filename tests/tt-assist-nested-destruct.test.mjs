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

    let snapshot = engine.start(
        "Σf:nat→Bool,(eq (f 0) 0b)×(Πn:nat,eq (f (succ n)) 1b)",
        options
    );
    for (const command of [
        "ex",
        "intro h",
        "destruct h",
        "exact 0b",
        "exact 1b",
        "simpl",
        "case",
        "rfl",
        "intro h",
        "destruct h"
    ]) {
        snapshot = engine.apply(command);
    }

    assert.equal(snapshot.goals.length, 2);
    const [zeroGoal, successorGoal] = snapshot.goals.map(goal => parser.stringify(goal.type));
    assert.equal(zeroGoal, "(1b=1b)",
        "the zero branch must normalize after substituting the destructed variable");
    assert.equal(successorGoal, "(1b=1b)",
        "the successor branch must normalize after substituting the destructed variable");
} finally {
    console.log = originalLog;
    console.warn = originalWarn;
}

console.log("proof-assistant nested destruct regression passed");
