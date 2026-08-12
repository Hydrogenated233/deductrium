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

const core = engine.core;
for (const [source, expectedType] of [
        ["nil: List ?1", "(List ?1)"],
        ["rfl: ?a = ?a", "(?a=?a)"],
        ["true: ?x", "?x"]
    ]) {
        const result = engine.check(source);
        assert.equal(result.ok, true, result.error ?? source);
        assert.equal(parser.stringify(result.ast.checked), expectedType,
            `${source} must preserve its shared schematic meta name`);
}

console.log("pure NbE generic-axiom regression passed");
