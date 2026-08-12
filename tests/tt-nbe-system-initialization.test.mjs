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

for (const name of ["eq", "refl", "pr0", "trunc", "ind_Trunc"]) {
    const definition = engine.core.state.sysDefs[name];
    assert.ok(definition, `missing system definition ${name}`);
    assert.equal(
        definition.type === "var" && definition.name === name,
        false,
        `system alias ${name} must not be stored as ${name} := ${name}`
    );
}

for (const source of [
    "isProp True",
    "ap pr0",
    "Join",
    "ind_Trunc",
    "apd_trunc"
]) {
    const result = engine.core.semanticTypeChecker.trySynthesize(
        parser.parse(source),
        [],
        {
            elaborateMetas: true,
            generalizeMetas: true,
            annotateTerm: true,
            maxSteps: 100_000
        }
    );
    assert.equal(result.status, "success",
        `semantic system initialization did not register ${source}: ${result.code ?? "unknown"}`);
}

console.log("pure semantic system-initialization regression passed");
