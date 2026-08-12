import assert from "node:assert/strict";

import { Assist } from "../js/tt/assist.js";
import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 10_000,
    language: "zh"
});

const eliminatorType = engine.core.checkType(parser.parse("ind_S2"), [], false);
assert.match(parser.stringify(eliminatorType), /^\(ΠC:/);

const assist = new Assist(engine.core, "Πx:S2,(x=x)");
assert.ok(assist.autofillTactics().includes("intro x"));
assist.intro("x");

const log = console.log;
try {
    console.log = () => { };
    assert.ok(assist.autofillTactics().includes("destruct x"));
    assist.destruct("x");
} finally {
    console.log = log;
}
assert.equal(assist.goal.length, 2);

console.log("S2 destruct recommendation regression passed");
