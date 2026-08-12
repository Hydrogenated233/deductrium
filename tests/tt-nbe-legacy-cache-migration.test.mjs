import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const configuredEngine = () => {
    const engine = new TTCoreEngine();
    engine.configure({
        unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
        inferDisplayMode: "_",
        timeout: 30_000,
        language: "zh"
    });
    return engine;
};

const parser = new ASTParser();
const source = configuredEngine();
const declaration = source.registerDefinition(parser.parse("legacyId:=λx:True.x"));
assert.equal(declaration.ok, true, declaration.error);

// Simulate the portable cache shape written by older releases. A closed
// definition has no live metas, so the legacy cache can be migrated directly
// to a native semantic scheme without constructing a runtime InferTable.
const legacyCache = {
    type: Core.clone(declaration.definitionCache.type),
    inferTable: {
        list: [],
        rel: {},
        solved: [],
        defered: [],
        nextName: 0
    },
    bondVarRel: { parent: [], size: [] },
    bondVarId: declaration.definitionCache.bondVarId
};

const restored = configuredEngine();
restored.core.setUserDefinition("legacyId", declaration.filledDefinition);

restored.core.restoreDefinitionCache("legacyId", legacyCache);
const migrated = restored.core.serializeDefinitionCache("legacyId");
assert.equal(migrated?.kind, "nbe",
    "restoring an old cache must immediately migrate it to native NbE");
assert.equal(restored.core.semanticTypeChecker.hasConstantType("legacyId"), true,
    "legacy cache migration must install a semantic constant scheme");
assert.equal(restored.check("legacyId true").ok, true,
    "the migrated definition must remain usable through semantic checking");

console.log("legacy definition-cache native NbE migration regression passed");
