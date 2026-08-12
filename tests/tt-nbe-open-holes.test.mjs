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

for (const source of [
        "Lx:_.x",
        "@Sum _ _ True",
        "_",
        "_:True",
        "rfl===rfl",
        "nil===nil",
        "rfl=rfl"
    ]) {
        const result = engine.check(source);
        assert.equal(result.ok, true, `${source}: ${result.error ?? "unknown error"}`);
}

for (const source of ["v:=_", "v:=_:True"]) {
        const result = engine.registerDefinition(parser.parse(source));
        assert.equal(result.ok, true, `${source}: ${result.error ?? "unknown error"}`);
        assert.equal(result.definitionCache?.kind, "nbe",
            `${source} must produce a native semantic cache`);
        assert.equal(result.inferenceComplete, false,
            `${source} must remain visibly incomplete instead of generalizing a proof hole`);
}

console.log("pure NbE open-hole and polymorphic-meta regression passed");
