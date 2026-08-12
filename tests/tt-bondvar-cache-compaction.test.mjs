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

let proof = "true";
for (let index = 0; index < 200; index++) {
    proof = `(Lx${index}:True,${proof}) true`;
}

const engine = new TTCoreEngine();
engine.configure(config);
const result = engine.registerDefinition(parser.parse(`bondCacheProbe:=${proof}`));
assert.equal(result.ok, true, result.error);
assert.ok(result.definitionCache, "definition cache was not serialized");
assert.equal(result.definitionCache.kind, "nbe");
assert.equal(result.definitionCache.bondVarRel, undefined,
    "native semantic caches must not retain legacy binder relations");

const filled = Core.clone(result.filledDefinition, true);
const definition = engine.core.desugar(Core.clone(filled), true);
const restored = new TTCoreEngine();
restored.configure({
    ...config,
    userDefinitions: [["bondCacheProbe", definition]],
    userDefinitionCaches: [["bondCacheProbe", result.definitionCache]]
});
const useResult = restored.checkAst(parser.parse("bondCacheProbe:True"));
assert.equal(useResult.ok, true, useResult.error);

console.log("bond-variable cache compaction regression passed");
