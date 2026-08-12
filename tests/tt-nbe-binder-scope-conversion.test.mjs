import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const previous = {
    recursive: Core.semanticTypeCheckRecursive,
    recursiveMin: Core.semanticTypeCheckRecursiveMinDefinitions
};

try {
    Core.semanticTypeCheckRecursive = false;
    Core.semanticTypeCheckRecursiveMinDefinitions = Number.MAX_SAFE_INTEGER;

    const engine = new TTCoreEngine();
    engine.configure({
        unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
        inferDisplayMode: "_",
        timeout: 30_000,
        language: "zh"
    });

    const checker = engine.core.semanticTypeChecker;
    checker.setConstantType("arrowFunction", parser.parse("True->True"));
    assert.equal(
        checker.tryCheck(
            parser.parse("arrowFunction"),
            parser.parse("Px:True,True"),
            [],
            { elaborateMetas: true, maxSteps: 10_000 }
        ).status,
        "success",
        "a surface arrow must convert to an alpha-equivalent non-dependent Pi"
    );
    assert.notEqual(
        checker.tryCheck(
            parser.parse("arrowFunction"),
            parser.parse("Px:True,x=x"),
            [],
            { elaborateMetas: true, maxSteps: 10_000 }
        ).status,
        "success",
        "arrow conversion must not erase a genuinely dependent Pi codomain"
    );

    const result = engine.registerDefinition(parser.parse(
        "sumInlScope:=(La:U,Lb:U,Lx:a,inl x):(Pa:U,Pb:U,a->a+b)"
    ));
    assert.equal(result.ok, true, result.error ?? "sumInl scope conversion must validate");
    assert.equal(result.definitionCache?.kind, "nbe",
        "implicit result metas must bind into a native semantic scheme");
} finally {
    Core.semanticTypeCheckRecursive = previous.recursive;
    Core.semanticTypeCheckRecursiveMinDefinitions = previous.recursiveMin;
}

console.log("semantic binder-scope conversion regression passed");
