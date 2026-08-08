import assert from "node:assert/strict";

import { Assist } from "../js/tt/assist.js";
import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";

const parser = new ASTParser();
const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: ["True", "False", "eq", "nat", "Even"],
    inferDisplayMode: "_",
    timeout: 10_000,
    language: "zh"
});

function suggestions(target) {
    return new Assist(engine.core, target).autofillTactics();
}

const evenZero = suggestions("Even 0");
assert.ok(evenZero.includes("exact even0"));
assert.ok(!evenZero.includes("apply evenss _"));

for (const [target, nextGoal] of [["Even 2", "(Even 0)"], ["Even 3", "(Even 1)"], ["Even 4", "(Even 2)"]]) {
    const tactics = suggestions(target);
    assert.ok(tactics.includes("apply evenss _"), `${target} did not recommend evenss`);

    const assist = new Assist(engine.core, target);
    const log = console.log;
    try {
        console.log = () => { };
        assist.apply("evenss _");
    } finally {
        console.log = log;
    }
    assert.equal(parser.stringify(assist.goal[0].type), nextGoal);
}

console.log("Even tactic recommendations regression passed");
