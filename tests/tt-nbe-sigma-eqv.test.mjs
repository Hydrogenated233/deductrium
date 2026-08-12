import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
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

const checker = engine.core.semanticTypeChecker;
const sourceCore = new Core();
const sigmaType = sourceCore.markBondVars(parser.parse("Σz:?0,?1 z"), []);
assert.equal(checker.setConstantSchemeSnapshot("sigmaEqvExpected", {
    type: sigmaType,
    metas: [
        { name: "?0", expectedType: parser.parse("U") },
        { name: "?1", expectedType: parser.parse("Π_:?0,U") }
    ]
}), true);

assert.equal(
    checker.tryCheck(
        parser.parse("sigmaEqvExpected"),
        parser.parse("eqv True True"),
        [],
        { elaborateMetas: false, maxSteps: 100_000 }
    ).status,
    "success",
    "conversion-head preparation must expose the transparent eqv Sigma"
);

assert.deepEqual(
    checker.trySynthesize(
        parser.parse("eqv _ True"),
        [],
        { elaborateMetas: false, maxSteps: 100_000 }
    ),
    { status: "unsupported", code: "metavariable" },
    "conversion-only alias expansion must not enable user input holes"
);

console.log("semantic Sigma/eqv conversion regression passed");
