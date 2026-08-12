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
for (const [source, expectedPattern] of [
        ["rfl===rfl", /^\(\?nbe[0-9]+=\?nbe[0-9]+\)$/],
        ["nil===nil", /^\(List \?nbe[0-9]+\)$/],
        ["rfl=rfl", /^\(U\?nbe[0-9]+\)$/],
    ]) {
        const result = engine.check(source);
        assert.equal(result.ok, true, result.error ?? source);
        assert.match(parser.stringify(result.ast.checked), expectedPattern,
            `${source} must be checked by semantic NbE`);
}

const declaration = engine.registerDefinition(parser.parse("d:=rfl:rfl=rfl"));
assert.equal(declaration.ok, true, declaration.error ?? "d definition");
assert.equal(declaration.definitionCache?.kind, "nbe",
    "a bare polymorphic definition must receive a native NbE cache");
assert.ok((declaration.definitionCache?.metas?.length ?? 0) > 0,
    "the native cache must retain the unresolved polymorphic parameters");

console.log("pure NbE generic-polymorphic regression passed");
