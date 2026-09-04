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
    "hit IndexedPath2Expr [n:nat] : U "
    + "| pointLeftIPE:Πn:nat,IndexedPath2Expr n "
    + "| pointMiddleIPE:Πn:nat,IndexedPath2Expr n "
    + "| pointRightIPE:Πn:nat,IndexedPath2Expr n "
    + "| edgeLMIPE:Πn:nat,pointLeftIPE n=pointMiddleIPE n "
    + "| edgeMRIPE:Πn:nat,pointMiddleIPE n=pointRightIPE n "
    + "| edgeLRIPE:Πn:nat,pointLeftIPE n=pointRightIPE n "
    + "| edgeMLIPE:Πn:nat,pointMiddleIPE n=pointLeftIPE n "
    + "| path2 composeIPE:Πn:nat,(edgeLMIPE n▪edgeMRIPE n)="
        + "edgeLRIPE n "
    + "| path2 inverseIPE:Πn:nat,inveq (edgeLMIPE n)=edgeMLIPE n"
));

const composeMetadata = bundle.metadata.pathLevels[1].constructors
    .find(path => path.name === "composeIPE");
const inverseMetadata = bundle.metadata.pathLevels[1].constructors
    .find(path => path.name === "inverseIPE");
assert.equal(composeMetadata?.leftExpression.kind, "compose");
assert.equal(inverseMetadata?.leftExpression.kind, "inverse");
assert.doesNotThrow(
    () => register(bundle),
    "Core must certify same-fiber indexed composed and inverse path2 endpoints"
);

const betaResourceBundle = lowerSandboxHit(parseSandboxHit(
    "hit IndexedPath2Budget [n:nat] : U "
    + "| pointBudget:Πn:nat,IndexedPath2Budget n "
    + "| loopBudget0:Πn:nat,pointBudget n=pointBudget n "
    + "| loopBudget1:Πn:nat,pointBudget n=pointBudget n "
    + "| path2 betaBudget:Πn:nat,loopBudget0 n="
        + "loopBudget1 ((λx:nat.x) n)"
));
const previousAssertionBudget = Core.semanticTypeAssertionMaxSteps;
try {
    Core.semanticTypeAssertionMaxSteps = 1;
    assert.throws(
        () => register(betaResourceBundle),
        /资源耗尽/,
        "an exhausted NbE comparison must not certify beta-equal indexed path2 fibers"
    );
} finally {
    Core.semanticTypeAssertionMaxSteps = previousAssertionBudget;
}

const forgedBoundary = structuredClone(bundle);
const forgedCompose = forgedBoundary.metadata.pathLevels[1].constructors
    .find(path => path.name === "composeIPE");
assert.equal(forgedCompose?.leftExpression.kind, "compose");
if (forgedCompose?.leftExpression.kind === "compose") {
    const localIndexName = forgedCompose.argumentNames[0];
    assert.ok(localIndexName, "the generated path2 telescope must retain its local index");
    forgedCompose.leftExpression.right = {
        kind: "atom",
        name: "edgeLMIPE",
        arguments: [parser.parse(localIndexName)]
    };
}
assert.throws(
    () => register(forgedBoundary),
    /组合项的中间点边界.*(?:不一致|不在同一索引纤维)/,
    "Core must reject forged indexed composition metadata with a broken intermediate point"
);

assert.match(
    parser.stringify(composeMetadata.resultIndices[0]),
    /n/,
    "the bundle must retain the indexed result fiber used by Core certification"
);

console.log("Core indexed path2 expression boundary regression passed");
