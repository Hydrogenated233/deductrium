import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
};

function countRootChecks(run) {
    const engine = new TTCoreEngine();
    engine.configure(config);
    let checks = 0;
    const checkType = engine.core.checkType.bind(engine.core);
    engine.core.checkType = (...args) => {
        checks++;
        return checkType(...args);
    };
    const result = run(engine);
    return { engine, result, checks };
}

const current = countRootChecks(engine =>
    engine.registerDefinition(parser.parse("polyId:=Lx:_,x")));

assert.equal(current.result.ok, true, current.result.error);
assert.equal(current.checks, 1,
    "definition registration must perform one semantic root check");
assert.equal(current.result.definitionCache?.kind, "nbe",
    "single-pass registration must return a native semantic cache");
assert.equal(countCheckedNodes(current.result.filledDefinition), 0,
    "the Worker result retained transient checked-type trees after filling holes");

const filled = clearBondIds(Core.clone(current.result.filledDefinition));
const restored = new TTCoreEngine();
restored.configure({
    ...config,
    userDefinitions: [["polyId", current.engine.core.desugar(Core.clone(filled), true)]],
    userDefinitionCaches: [["polyId", current.result.definitionCache]]
});
const useResult = restored.checkAst(parser.parse("(polyId true):True"));
assert.equal(useResult.ok, true, useResult.error);

const invalid = new TTCoreEngine();
invalid.configure(config);
const log = console.log;
let invalidResult;
try {
    console.log = () => { };
    invalidResult = invalid.registerDefinition(parser.parse("bad:=true:False"));
} finally {
    console.log = log;
}
assert.equal(invalidResult.ok, false, "an invalid annotated definition was accepted");
assert.equal(invalid.core.state.defTypes.bad, undefined,
    "a failed single-pass registration left a definition cache behind");

function clearBondIds(ast, seen = new WeakSet()) {
    if (!ast || seen.has(ast)) return ast;
    seen.add(ast);
    ast.bondVarId = null;
    for (const node of ast.nodes ?? []) clearBondIds(node, seen);
    if (ast.checked) clearBondIds(ast.checked, seen);
    return ast;
}

function countCheckedNodes(ast, seen = new WeakSet()) {
    if (!ast || seen.has(ast)) return 0;
    seen.add(ast);
    let count = ast.checked ? 1 + countCheckedNodes(ast.checked, seen) : 0;
    for (const node of ast.nodes ?? []) count += countCheckedNodes(node, seen);
    return count;
}

console.log("single-pass definition registration regression passed");
