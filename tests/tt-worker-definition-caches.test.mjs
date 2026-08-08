import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const definitions = readFileSync(new URL("./fixtures/code-nat.txt", import.meta.url), "utf8")
    .split(/\r?\n/)
    .map(line => line.trim())
    .filter(Boolean);
const baseConfig = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
};
const userDefinitions = [];
const userDefinitionCaches = [];

function clearBondIds(ast) {
    ast.bondVarId = null;
    for (const node of ast.nodes ?? []) clearBondIds(node);
    if (ast.checked) clearBondIds(ast.checked);
    return ast;
}

for (const source of definitions) {
    const engine = new TTCoreEngine();
    engine.configure({ ...baseConfig, userDefinitions, userDefinitionCaches });
    const ast = parser.parse(source);
    const name = ast.nodes[0].name;
    const annotated = ast.nodes[1].type === ":";
    const result = engine.registerDefinition(ast);
    assert.equal(result.ok, true, `${name}: ${result.error}`);

    const filled = clearBondIds(Core.clone(result.filledDefinition, true));
    const value = annotated ? filled.nodes[0] : filled;
    userDefinitions.push([name, engine.core.desugar(Core.clone(value, true), true)]);
    userDefinitionCaches.push([name, result.definitionCache]);
}

console.log("complete code_nat Worker cache regression passed");
