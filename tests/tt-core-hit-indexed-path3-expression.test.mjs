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

const bundle = lowerSandboxHit(parseSandboxHit(
    "hit IndexedPath3Expr [n:nat] : U "
    + "| pointIPE:Πn:nat,IndexedPath3Expr n "
    + "| loop0IPE:Πn:nat,pointIPE n=pointIPE n "
    + "| loop1IPE:Πn:nat,pointIPE n=pointIPE n "
    + "| loop2IPE:Πn:nat,pointIPE n=pointIPE n "
    + "| path2 face01IPE:Πn:nat,loop0IPE n=loop1IPE n "
    + "| path2 face12IPE:Πn:nat,loop1IPE n=loop2IPE n "
    + "| path2 face02IPE:Πn:nat,loop0IPE n=loop2IPE n "
    + "| path2 face10IPE:Πn:nat,loop1IPE n=loop0IPE n "
    + "| path3 compose3IPE:Πn:nat,(face01IPE n▪face12IPE n)=face02IPE n "
    + "| path3 inverse3IPE:Πn:nat,inveq (face01IPE n)=face10IPE n"
));

const composeMetadata = bundle.metadata.pathLevels[2].constructors
    .find(path => path.name === "compose3IPE");
const inverseMetadata = bundle.metadata.pathLevels[2].constructors
    .find(path => path.name === "inverse3IPE");
assert.equal(composeMetadata?.leftExpression.kind, "compose");
assert.equal(inverseMetadata?.leftExpression.kind, "inverse");
assert.doesNotThrow(
    () => register(bundle),
    "Core must certify same-fiber indexed composed and inverse path3 endpoints"
);

const betaResourceBundle = lowerSandboxHit(parseSandboxHit(
    "hit IndexedPath3Budget [n:nat] : U "
    + "| pointBudget:Πn:nat,IndexedPath3Budget n "
    + "| loopBudget:Πn:nat,pointBudget n=pointBudget n "
    + "| path2 faceBudget:Πn:nat,loopBudget n=loopBudget n "
    + "| path3 betaBudget:Πn:nat,faceBudget ((λx:nat.x) n)=faceBudget n"
));
const previousAssertionBudget = Core.semanticTypeAssertionMaxSteps;
try {
    Core.semanticTypeAssertionMaxSteps = 1;
    assert.throws(
        () => register(betaResourceBundle),
        /资源耗尽/,
        "an exhausted NbE comparison must not certify beta-equal indexed path3 fibers"
    );
} finally {
    Core.semanticTypeAssertionMaxSteps = previousAssertionBudget;
}

const forgedBoundary = structuredClone(bundle);
const forgedCompose = forgedBoundary.metadata.pathLevels[2].constructors
    .find(path => path.name === "compose3IPE");
assert.equal(forgedCompose?.leftExpression.kind, "compose");
if (forgedCompose?.leftExpression.kind === "compose") {
    const localIndexName = forgedCompose.argumentNames[0];
    assert.ok(localIndexName, "the generated path3 telescope must retain its local index");
    forgedCompose.leftExpression.right = {
        kind: "atom",
        name: "face01IPE",
        arguments: [parser.parse(localIndexName)]
    };
}
assert.throws(
    () => register(forgedBoundary),
    /组合项的中间一阶路径边界/,
    "Core must reject forged indexed path3 metadata with a broken intermediate boundary"
);

const forgedRefl = structuredClone(bundle);
const forgedInverse = forgedRefl.metadata.pathLevels[2].constructors
    .find(path => path.name === "inverse3IPE");
assert.ok(forgedInverse, "the fixture must expose the inverse path3 metadata");
const reflIndexName = forgedInverse.argumentNames[0];
assert.ok(reflIndexName, "the generated path3 telescope must retain its local index");
forgedInverse.leftExpression = {
    kind: "inverse",
    value: {
        kind: "refl",
        pathName: "loop0IPE",
        arguments: [parser.parse(reflIndexName)]
    }
};
assert.throws(
    () => register(forgedRefl),
    /索引 HIT 三阶路径构造子.*refl 二阶路径端点/,
    "Core must reject forged nested indexed path3 refl metadata"
);

console.log("Core indexed path3 expression boundary regression passed");
