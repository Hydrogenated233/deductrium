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

for (const name of ["eqvrefl", "LEM", "rec_S1", "trunc", "ind_Trunc", "apd_trunc"]) {
    const result = engine.check(name);
    assert.equal(result.ok, true, result.error ?? name);
    assert.ok(result.ast?.checked, `${name} must have a displayable inferred type`);
    assert.doesNotMatch(parser.stringify(result.ast.checked), /\?nbe/,
        `${name} must not expose internal semantic metavariable names`);
}

console.log("system alias rendering regression passed");
