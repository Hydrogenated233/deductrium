import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

assert.equal(
    parser.stringify(engine.core.checkType(parser.parse("true"), [], false)),
    "True",
    "a closed term must synthesize through the semantic checker"
);

assert.match(
    parser.stringify(engine.core.checkType(parser.parse("_"), [], false)),
    /^\?nbe/,
    "a later standalone hole must stay in the native semantic solver"
);

console.log("semantic standalone-hole state regression passed");
