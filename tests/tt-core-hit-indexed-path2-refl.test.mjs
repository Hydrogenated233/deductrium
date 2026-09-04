import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import {
    creativeSandboxSystemRuleIds,
    lowerSandboxHit,
    parseSandboxHit
} from "../js/tt/sandbox.js";

const parser = new ASTParser();
const register = bundle => {
    const engine = new TTCoreEngine();
    engine.configure({ unlockedTypes: creativeSandboxSystemRuleIds });
    return engine.core.registerSystemInductive(structuredClone(bundle));
};

const source =
    "hit IndexedPath2Refl [n:nat] : U "
    + "| pointIP2R:Πn:nat,IndexedPath2Refl n "
    + "| loopIP2R:Πn:nat,pointIP2R n=pointIP2R n "
    + "| path2 directIP2R:Πn:nat,refl (pointIP2R n)=loopIP2R n "
    + "| path2 nestedIP2R:Πn:nat,"
        + "(refl (pointIP2R n)▪loopIP2R n)=loopIP2R n "
    + "| path2 inverseIP2R:Πn:nat,"
        + "inveq (refl (pointIP2R n))=refl (pointIP2R n)";

const signature = parseSandboxHit(source);
const direct = signature.pathLevels[1].constructors.find(path => path.name === "directIP2R");
const nested = signature.pathLevels[1].constructors.find(path => path.name === "nestedIP2R");
const inverse = signature.pathLevels[1].constructors.find(path => path.name === "inverseIP2R");
assert.equal(direct?.leftExpression.kind, "refl");
assert.equal(direct?.leftExpression.pointName, "pointIP2R");
assert.equal(nested?.leftExpression.kind, "compose");
if (nested?.leftExpression.kind === "compose") {
    assert.equal(nested.leftExpression.left.kind, "refl");
}
assert.equal(inverse?.leftExpression.kind, "inverse");
if (inverse?.leftExpression.kind === "inverse") {
    assert.equal(inverse.leftExpression.value.kind, "refl");
}

const bundle = lowerSandboxHit(signature);
assert.equal(
    bundle.metadata.pathLevels[1].constructors.find(path => path.name === "directIP2R")
        ?.leftExpression.kind,
    "refl"
);
assert.doesNotThrow(
    () => register(bundle),
    "Core must certify direct and nested same-fiber indexed path2 refl endpoints"
);

for (const [label, pointName, arguments_] of [
    ["a path constructor", "loopIP2R", [parser.parse("n")]],
    ["a path2 constructor", "directIP2R", [parser.parse("n")]],
    ["an unknown point", "missingIP2R", [parser.parse("n")]],
    ["the point constructor with wrong arity", "pointIP2R", []]
]) {
    const forged = structuredClone(bundle);
    const metadata = forged.metadata.pathLevels[1].constructors
        .find(path => path.name === "directIP2R");
    assert.ok(metadata, `the fixture must expose directIP2R for ${label}`);
    metadata.leftExpression = {
        kind: "refl",
        pointName,
        arguments: arguments_.map(argument => structuredClone(argument))
    };
    assert.throws(
        () => register(forged),
        /点构造子不存在|参数数量与点构造子/,
        `Core must reject a refl endpoint forged to name ${label}`
    );
}

const forgedShape = structuredClone(bundle);
const directMetadata = forgedShape.metadata.pathLevels[1].constructors
    .find(path => path.name === "directIP2R");
assert.ok(directMetadata);
directMetadata.leftExpression.extra = true;
assert.throws(
    () => register(forgedShape),
    /一阶路径 refl 结构无效/,
    "Core must reject surplus fields in path2 refl metadata"
);

const betaBundle = lowerSandboxHit(parseSandboxHit(
    "hit IndexedPath2ReflBudget [n:nat] : U "
    + "| pointBudgetIP2R:Πn:nat,IndexedPath2ReflBudget n "
    + "| loopBudgetIP2R:Πn:nat,pointBudgetIP2R n=pointBudgetIP2R n "
    + "| path2 betaIP2R:Πn:nat,"
        + "refl (pointBudgetIP2R ((λx:nat.x) n))=loopBudgetIP2R n"
));
assert.doesNotThrow(
    () => register(structuredClone(betaBundle)),
    "Core must use semantic equality for beta-equal indexed path2 refl fibers"
);
const previousAssertionBudget = Core.semanticTypeAssertionMaxSteps;
try {
    Core.semanticTypeAssertionMaxSteps = 1;
    assert.throws(
        () => register(structuredClone(betaBundle)),
        /资源耗尽/,
        "an exhausted NbE comparison must not certify beta-equal indexed path2 refl fibers"
    );
} finally {
    Core.semanticTypeAssertionMaxSteps = previousAssertionBudget;
}

console.log("Core indexed path2 refl regression passed");
