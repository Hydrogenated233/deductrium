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

const source = new TTCoreEngine();
source.configure(config);
const declaration = parser.parse("nativeScheme:=La:U,Lx:a,inr x");
const result = source.registerDefinition(declaration);
assert.equal(result.ok, true, result.error);
assert.equal(result.definitionCache?.kind, "nbe");
assert.equal(result.definitionCache?.metas.length, 2);
assert.ok(result.definitionCache?.metas.every(meta => meta.expectedType));

const restored = new TTCoreEngine();
restored.configure(config);
restored.core.setUserDefinition(
    "nativeScheme",
    restored.core.desugar(Core.clone(result.filledDefinition), true)
);

restored.core.restoreDefinitionCache("nativeScheme", result.definitionCache);
assert.equal(restored.core.semanticTypeChecker.hasConstantType("nativeScheme"), true,
    "restoring a native cache must install its semantic constant scheme");

const use = restored.core.semanticTypeChecker.tryCheck(
    parser.parse("nativeScheme True true"),
    parser.parse("@Sum @0 @0 False True"),
    [],
    { elaborateMetas: true, maxSteps: 100_000 }
);
assert.equal(use.status, "success",
    "a restored native scheme must instantiate its generalized metas");
assert.equal(restored.core.serializeDefinitionCache("nativeScheme")?.kind, "nbe");

restored.core.setUserDefinition("brokenCache", parser.parse("true"));
restored.core.restoreDefinitionCache("brokenCache", {
    kind: "nbe",
    type: { type: "var", name: "?ghost", nodes: [] },
    metas: [],
    bondVarId: 1
});
assert.equal(restored.core.hasDefinitionCache("brokenCache"), false,
    "a native snapshot rejected by the scheme compiler must not remain marked as cached");
assert.equal(restored.core.semanticTypeChecker.hasConstantType("brokenCache"), false);

console.log("native semantic definition-cache regression passed");
