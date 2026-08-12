import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";
import { restoreSemanticMetaNamesForDisplay } from "../js/tt/presentation.js";

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
        ["rfl===rfl", /^\(\?[0-9]+=\?[0-9]+\)$/],
        ["nil===nil", /^\(List \?[0-9]+\)$/],
        ["rfl=rfl", /^\(U\?[0-9]+\)$/],
    ]) {
        const result = engine.check(source);
        assert.equal(result.ok, true, result.error ?? source);
        assert.match(parser.stringify(result.ast.checked), expectedPattern,
            `${source} must be checked by semantic NbE`);
}

const isProp = engine.check("isProp");
assert.equal(isProp.ok, true, isProp.error);
assert.equal(
    parser.stringify(isProp.ast.checked),
    "((U?0)→(U?0))",
    "public inference names must use ?N and idempotent universe maxima must normalize"
);

core.semanticTypeChecker.setConstantSchemeSnapshot("levelIdem", {
    type: parser.parse("U?0→U(@max ?0 ?0)"),
    metas: [{ name: "?0", expectedType: parser.parse("U@") }]
});
const levelIdem = core.semanticTypeChecker.trySynthesize(
    parser.parse("levelIdem"),
    [],
    { elaborateMetas: true, allowGeneratedSchematicMetas: true }
);
assert.equal(levelIdem.status, "success");
assert.match(
    parser.stringify(levelIdem.type),
    /\?nbe[0-9]+/,
    "solver-private inference names must remain disjoint from user-written ?N names"
);
assert.equal(
    parser.stringify(restoreSemanticMetaNamesForDisplay(Core.clone(levelIdem.type, true))),
    "((U?0)→(U?0))",
    "cached polymorphic types must normalize idempotent maxima at the presentation boundary"
);

const declaration = engine.registerDefinition(parser.parse("d:=rfl:rfl=rfl"));
assert.equal(declaration.ok, true, declaration.error ?? "d definition");
assert.equal(declaration.definitionCache?.kind, "nbe",
    "a bare polymorphic definition must receive a native NbE cache");
assert.ok((declaration.definitionCache?.metas?.length ?? 0) > 0,
    "the native cache must retain the unresolved polymorphic parameters");

console.log("pure NbE generic-polymorphic regression passed");
