import assert from "node:assert/strict";

import { TTCoreEngine } from "../js/tt/engine.js";
import {
    SandboxEnvironment,
    creativeSandboxSystemRuleIds,
    lowerSandboxHit,
    parseSandboxHit
} from "../js/tt/sandbox.js";

const torusSource = "hit TorusExpr : U "
    + "| baseTE : TorusExpr "
    + "| pTE : baseTE=baseTE "
    + "| qTE : baseTE=baseTE "
    + "| path2 commTE : (pTE▪qTE)=(qTE▪pTE)";

const expectedLeftExpression = {
    kind: "compose",
    left: { kind: "atom", name: "pTE", arguments: [] },
    right: { kind: "atom", name: "qTE", arguments: [] }
};
const expectedRightExpression = {
    kind: "compose",
    left: { kind: "atom", name: "qTE", arguments: [] },
    right: { kind: "atom", name: "pTE", arguments: [] }
};

const torus = parseSandboxHit(torusSource);
const comm = torus.pathLevels[1].constructors[0];
assert.deepEqual(comm.leftExpression, expectedLeftExpression,
    "path2 must retain a closed composite first-path expression");
assert.deepEqual(comm.rightExpression, expectedRightExpression);

const inverseSource = "hit InverseExpr : U "
    + "| leftIE : InverseExpr "
    + "| rightIE : InverseExpr "
    + "| forwardIE : leftIE=rightIE "
    + "| backwardIE : rightIE=leftIE "
    + "| path2 inverseFaceIE : (inveq forwardIE)=backwardIE";
const inverse = parseSandboxHit(inverseSource);
const inverseFace = inverse.pathLevels[1].constructors[0];
assert.deepEqual(inverseFace.leftExpression, {
    kind: "inverse",
    value: { kind: "atom", name: "forwardIE", arguments: [] }
});
assert.deepEqual(inverseFace.rightExpression, {
    kind: "atom",
    name: "backwardIE",
    arguments: []
});

assert.throws(
    () => parseSandboxHit(
        "hit BadComposeExpr : U "
        + "| aBCE : BadComposeExpr "
        + "| bBCE : BadComposeExpr "
        + "| cBCE : BadComposeExpr "
        + "| pBCE : aBCE=bBCE "
        + "| qBCE : aBCE=cBCE "
        + "| rBCE : aBCE=cBCE "
        + "| path2 brokenBCE : (pBCE▪qBCE)=rBCE"
    ),
    /组合.*边界不一致/,
    "path2 composition must reject non-composable point boundaries"
);

const torusBundle = lowerSandboxHit(torus);
assert.equal(torusBundle.metadata.version, 8);
assert.equal(torusBundle.metadata.kind, "hit2");
const commMetadata = torusBundle.metadata.pathLevels[1].constructors[0];
assert.deepEqual(commMetadata.leftExpression, expectedLeftExpression);
assert.deepEqual(commMetadata.rightExpression, expectedRightExpression);
for (const legacyField of ["left", "right", "leftPath", "rightPath"]) {
    assert.equal(Object.hasOwn(commMetadata, legacyField), false,
        `v8 path2 metadata must not retain legacy field ${legacyField}`);
}

const register = bundle => {
    const engine = new TTCoreEngine();
    engine.configure({ unlockedTypes: creativeSandboxSystemRuleIds });
    return engine.core.registerSystemInductive(structuredClone(bundle));
};
assert.doesNotThrow(() => register(torusBundle),
    "Core must independently accept the certified composite endpoints");
assert.doesNotThrow(() => register(lowerSandboxHit(inverse)),
    "Core must independently accept the certified inverse endpoint");

const forged = structuredClone(torusBundle);
forged.metadata.pathLevels[1].constructors[0].leftExpression = {
    kind: "raw",
    ast: structuredClone(comm.left)
};
assert.throws(
    () => register(forged),
    /一阶路径表达式.*(?:kind|结构).*无效/,
    "Core must reject arbitrary AST escape hatches in path2 metadata"
);

for (const name of [
    "apd_commTE",
    "@apd_commTE",
    "ap_commTE",
    "@ap_commTE",
    "ap2_commTE",
    "@ap2_commTE"
]) {
    assert.ok(torusBundle.auxiliaryTypes.some(([entryName]) => entryName === name),
        `composite path2 lowering must export ${name}`);
}

const sandbox = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const added = sandbox.add(torusSource);
assert.equal(added.ok, true, added.error);
assert.equal(sandbox.check("commTE : (pTE▪qTE)=(qTE▪pTE)").ok, true);
for (const name of ["apd_commTE", "ap_commTE", "ap2_commTE"]) {
    assert.equal(sandbox.check(name).ok, true,
        `creative sandbox must expose ${name} after registration`);
}

console.log("sandbox path2 expression endpoint regression passed");
