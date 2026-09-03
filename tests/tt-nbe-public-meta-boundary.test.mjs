import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";
import { SemanticNbeTypeChecker } from "../js/tt/nbe-checker.js";
import { SemanticNbeKernel } from "../js/tt/nbe-kernel.js";

const parser = new ASTParser();
const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

const privateMetaPattern = /\?nbe[0-9]+/;
const leakedSystemTypes = Object.entries(engine.core.state.sysTypes)
    .filter(([, type]) => privateMetaPattern.test(parser.stringify(type)))
    .map(([name]) => name);
assert.deepEqual(leakedSystemTypes, [],
    "solver-private NbE metas must not be stored in the public system type table");

const truncType = engine.core.checkType(parser.parse("apd_trunc"), [], false);
assert.doesNotMatch(parser.stringify(truncType), privateMetaPattern,
    "Core.checkType must return public ?N metas without relying on UI rewriting");

const checker = new SemanticNbeTypeChecker(new SemanticNbeKernel());
checker.setConstantSchemeSnapshot("levelIdem", {
    type: parser.parse("U?0→U(@max ?0 ?0)"),
    metas: [{ name: "?0", expectedType: parser.parse("U@") }]
});
const collision = checker.trySynthesize(
    parser.parse("λx:U?0.levelIdem"),
    [],
    {
        elaborateMetas: true,
        allowNamedSchematicMetas: true,
        allowGeneratedSchematicMetas: true,
        generalizeMetas: true,
        annotateTerm: true,
        maxSteps: 100_000
    }
);
assert.equal(collision.status, "success");
assert.equal(parser.stringify(collision.type), "(Πx:(U?0),((U?1)→(U?1)))",
    "a generated meta must skip a user-owned ?0 in the same result");
assert.equal(parser.stringify(collision.term), "(λx:(U?0).levelIdem)");
assert.equal(parser.stringify(collision.elaboratedTerm), "(λx:(U?0).levelIdem)");
assert.deepEqual(collision.generalizedMetas?.map(meta => meta.name), ["?0", "?1"]);
assert.deepEqual(collision.schematicMetaNames, ["?0", "?1"]);
const collisionMetas = collectMetas(collision.type);
assert.ok(collisionMetas.get("?0")?.every(node => node.nbeGeneratedMeta !== true),
    "a user-owned ?0 must not be marked as an NbE-generated metavariable");
assert.ok(collisionMetas.get("?1")?.every(node => node.nbeGeneratedMeta === true),
    "a publicized solver meta must retain non-semantic provenance");
for (const ast of [
    collision.type,
    collision.term,
    collision.elaboratedTerm,
    ...(collision.generalizedMetas?.map(meta => meta.expectedType) ?? [])
]) {
    assert.doesNotMatch(parser.stringify(ast), privateMetaPattern);
}

function collectMetas(ast, result = new Map(), seen = new WeakSet()) {
    if (!ast || seen.has(ast)) return result;
    seen.add(ast);
    if (ast.type === "var" && ast.name.startsWith("?")) {
        const entries = result.get(ast.name) ?? [];
        entries.push(ast);
        result.set(ast.name, entries);
    }
    for (const node of ast.nodes ?? []) collectMetas(node, result, seen);
    if (ast.checked) collectMetas(ast.checked, result, seen);
    return result;
}

const checked = checker.tryCheck(
    parser.parse("levelIdem"),
    parser.parse("U?0→U?0"),
    [],
    {
        elaborateMetas: true,
        allowNamedSchematicMetas: true,
        allowGeneratedSchematicMetas: true,
        generalizeMetas: true,
        annotateTerm: true,
        maxSteps: 100_000
    }
);
assert.equal(checked.status, "success");
for (const ast of [checked.type, checked.expectedTerm, checked.term, checked.elaboratedTerm]) {
    assert.doesNotMatch(parser.stringify(ast), privateMetaPattern,
        "tryCheck must publicize every returned syntax field as one group");
}

const equal = checker.tryDefinitionalEquality(
    parser.parse("levelIdem"),
    parser.parse("levelIdem"),
    [],
    {
        elaborateMetas: true,
        allowGeneratedSchematicMetas: true,
        generalizeMetas: true,
        annotateTerm: true,
        maxSteps: 100_000
    }
);
assert.equal(equal.status, "success");
for (const ast of [equal.type, equal.leftTerm, equal.rightTerm]) {
    assert.doesNotMatch(parser.stringify(ast), privateMetaPattern,
        "definitional equality must not return solver-private names");
}

console.log("NbE public-meta boundary regression passed");
