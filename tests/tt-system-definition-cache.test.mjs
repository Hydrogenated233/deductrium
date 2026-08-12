import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const rules = initTypeSystem();
const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: [...new Set(rules.map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

const notRule = rules.find(rule => rule.ast?.nodes?.[0]?.name === "not");
assert.ok(notRule, "the False.not system definition must exist");
assert.doesNotThrow(
    () => engine.core.registerSystemDefinition(
        "notReloadProbe",
        Core.clone(notRule.ast.nodes[1])
    ),
    "rebuilding unlocked system definitions must create a native semantic cache"
);
assert.equal(engine.core.serializeDefinitionCache("notReloadProbe")?.kind, "nbe");
assert.ok(engine.core.state.sysDefs.notReloadProbe,
    "the semantic system registration must retain the portable definition source");

assert.ok(engine.core.state.sysDefs.loop_pow, "loop_pow must retain its system definition");
assert.ok(engine.core.state.sysTypes.loop_pow, "loop_pow must register its explicit system type");
assert.ok(engine.core.semanticKernel.hasDefinition("loop_pow"));
assert.ok(engine.core.semanticTypeChecker.hasConstantType("loop_pow"));
const loopPowApplication = engine.core.semanticTypeChecker.trySynthesize(
    parser.parse("loop_pow (succZ 0Z)")
);
assert.equal(loopPowApplication.status, "success");

const serializedSystemDefinitions = Object.fromEntries(
    Object.entries(engine.core.state.sysDefs)
        .map(([name, definition]) => [name, parser.stringify(definition)])
);
assert.equal(serializedSystemDefinitions.eq, "(@eq _ _)");
assert.equal(serializedSystemDefinitions.eqv, "(@eqv _)");
assert.deepEqual(
    Object.entries(serializedSystemDefinitions)
        .filter(([, definition]) => definition.includes("?nbe")),
    [],
    "system aliases must not retain request-local semantic metavariables"
);

const expectedLoopType = engine.core.semanticTypeChecker.trySynthesize(
    engine.core.markBondVars(
        engine.core.desugar(parser.parse("base=base"), false),
        []
    ),
    [],
    { elaborateMetas: true }
);
assert.equal(expectedLoopType.status, "success");
assert.ok(expectedLoopType.elaboratedTerm,
    "the public eq alias must elaborate before entering the semantic kernel");
assert.equal(
    engine.core.semanticKernel.tryEqualResult(
        loopPowApplication.type,
        expectedLoopType.elaboratedTerm,
        []
    ),
    "equal"
);

console.log("system definition cache rebuild regression passed");
