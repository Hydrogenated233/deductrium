import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const sources = readFileSync(new URL("./fixtures/bug1-universe-cache.txt", import.meta.url), "utf8")
    .split(/\r?\n\s*\r?\n/)
    .map(source => source.trim())
    .filter(Boolean);
const config = {
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

for (let index = 0; index < sources.length - 1; index++) {
    const engine = new TTCoreEngine();
    engine.configure({ ...config, userDefinitions, userDefinitionCaches });
    const ast = parser.parse(sources[index]);
    const result = engine.registerDefinition(ast);
    assert.equal(result.ok, true, `definition ${index}: ${result.error}`);

    const filled = clearBondIds(Core.clone(result.filledDefinition, true));
    const value = ast.nodes[1].type === ":" ? filled.nodes[0] : filled;
    userDefinitions.push([ast.nodes[0].name, engine.core.desugar(Core.clone(value, true), true)]);
    userDefinitionCaches.push([ast.nodes[0].name, result.definitionCache]);
}

const cacheBefore = structuredClone(userDefinitionCaches);
const finalEngine = new TTCoreEngine();
finalEngine.configure({ ...config, userDefinitions, userDefinitionCaches });
const result = finalEngine.checkAst(parser.parse(sources.at(-1)));
assert.equal(result.ok, true, result.error);
assert.deepEqual(userDefinitionCaches, cacheBefore, "revalidation must not mutate saved definition caches");

console.log("bug1 cache revalidation regression passed");
