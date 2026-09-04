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
    "hit IndexedPath3Refl [n:nat] : U "
    + "| pointIP3R:Πn:nat,IndexedPath3Refl n "
    + "| loopIP3R:Πn:nat,pointIP3R n=pointIP3R n "
    + "| path2 faceIP3R:Πn:nat,loopIP3R n=loopIP3R n "
    + "| path3 directIP3R:Πn:nat,refl (loopIP3R n)=faceIP3R n "
    + "| path3 nestedIP3R:Πn:nat,"
        + "((refl (loopIP3R n))▪inveq (refl (loopIP3R n)))=refl (loopIP3R n)";

const signature = parseSandboxHit(source);
const direct = signature.pathLevels[2].constructors
    .find(path => path.name === "directIP3R");
const nested = signature.pathLevels[2].constructors
    .find(path => path.name === "nestedIP3R");
assert.equal(direct?.leftExpression.kind, "refl");
assert.equal(direct?.leftExpression.pathName, "loopIP3R");
assert.equal(nested?.leftExpression.kind, "compose");
if (nested?.leftExpression.kind === "compose") {
    assert.equal(nested.leftExpression.left.kind, "refl");
    assert.equal(nested.leftExpression.right.kind, "inverse");
    if (nested.leftExpression.right.kind === "inverse") {
        assert.equal(nested.leftExpression.right.value.kind, "refl");
    }
}

const bundle = lowerSandboxHit(signature);
const directMetadata = bundle.metadata.pathLevels[2].constructors
    .find(path => path.name === "directIP3R");
const nestedMetadata = bundle.metadata.pathLevels[2].constructors
    .find(path => path.name === "nestedIP3R");
assert.equal(directMetadata?.leftExpression.kind, "refl");
assert.equal(nestedMetadata?.leftExpression.kind, "compose");
assert.doesNotThrow(
    () => register(structuredClone(bundle)),
    "Core must certify same-fiber indexed path3 refl endpoints, including nested compose/inverse"
);

for (const [label, pathName, arguments_] of [
    ["a point constructor", "pointIP3R", [parser.parse("n")]],
    ["a path2 constructor", "faceIP3R", [parser.parse("n")]],
    ["an unknown constructor", "missingIP3R", [parser.parse("n")]],
    ["the declared path with wrong arity", "loopIP3R", []]
]) {
    const forged = structuredClone(bundle);
    const metadata = forged.metadata.pathLevels[2].constructors
        .find(path => path.name === "directIP3R");
    assert.ok(metadata, `the fixture must expose directIP3R for ${label}`);
    metadata.leftExpression = {
        kind: "refl",
        pathName,
        arguments: arguments_.map(argument => structuredClone(argument))
    };
    assert.throws(
        () => register(forged),
        /一阶路径不存在|参数数量与一阶路径/,
        `Core must reject a refl endpoint forged to name ${label}`
    );
}

const betaBundle = lowerSandboxHit(parseSandboxHit(
    "hit IndexedPath3ReflBudget [n:nat] : U "
    + "| pointBudgetIP3R:Πn:nat,IndexedPath3ReflBudget n "
    + "| loopBudgetIP3R:Πn:nat,pointBudgetIP3R n=pointBudgetIP3R n "
    + "| path2 faceBudgetIP3R:Πn:nat,loopBudgetIP3R n=loopBudgetIP3R n "
    + "| path3 betaReflIP3R:Πn:nat,"
        + "refl (loopBudgetIP3R ((λx:nat.x) n))=refl (loopBudgetIP3R n)"
));
assert.doesNotThrow(
    () => register(structuredClone(betaBundle)),
    "Core must use semantic equality for beta-equal indexed path3 refl fibers"
);
const previousAssertionBudget = Core.semanticTypeAssertionMaxSteps;
try {
    Core.semanticTypeAssertionMaxSteps = 1;
    assert.throws(
        () => register(structuredClone(betaBundle)),
        /资源耗尽/,
        "an exhausted NbE comparison must not certify beta-equal indexed path3 refl fibers"
    );
} finally {
    Core.semanticTypeAssertionMaxSteps = previousAssertionBudget;
}

console.log("Core indexed path3 refl regression passed");
