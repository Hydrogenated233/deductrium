import assert from "node:assert/strict";

import { TTCoreEngine } from "../js/tt/engine.js";
import {
    SandboxEnvironment,
    creativeSandboxSystemRuleIds,
    lowerSandboxHit,
    parseSandboxHit
} from "../js/tt/sandbox.js";

const register = source => {
    const signature = parseSandboxHit(source);
    const bundle = lowerSandboxHit(signature);
    const engine = new TTCoreEngine();
    engine.configure({ unlockedTypes: creativeSandboxSystemRuleIds, timeout: 60_000 });
    engine.core.registerSystemInductive(structuredClone(bundle));
    return { signature, bundle };
};

const defeqPath2 =
    "hit DefEqBoundary2 : U "
    + "| pointDE2 : nat→DefEqBoundary2 "
    + "| loopDE2 : Πn:nat,pointDE2 n=pointDE2 n "
    + "| path2 faceDE2 : Πn:nat,loopDE2 n=loopDE2 ((λx:nat.x) n)";
assert.doesNotThrow(
    () => register(defeqPath2),
    "non-indexed path2 point boundaries may be definitionally rather than syntactically equal"
);

const defeqPath3 =
    "hit DefEqBoundary3 : U "
    + "| pointDE3 : nat→DefEqBoundary3 "
    + "| loopDE3 : Πn:nat,pointDE3 n=pointDE3 n "
    + "| path2 faceDE3 : Πn:nat,loopDE3 n=loopDE3 n "
    + "| path3 cellDE3 : Πn:nat,faceDE3 n=faceDE3 ((λx:nat.x) n)";
const defeqSandbox = new SandboxEnvironment({
    systemRuleIds: creativeSandboxSystemRuleIds,
    validationTimeoutMs: 60_000
});
const defeqAdded = defeqSandbox.add(defeqPath3);
assert.equal(defeqAdded.ok, true, defeqAdded.error);
assert.equal(defeqSandbox.check("apd3_cellDE3").ok, true);
assert.equal(defeqSandbox.check("ap3_cellDE3").ok, true);

const nonLoopInverse =
    "hit NonLoopInverse3 : U "
    + "| leftNLI3 : NonLoopInverse3 "
    + "| rightNLI3 : NonLoopInverse3 "
    + "| pNLI3 : leftNLI3=rightNLI3 "
    + "| qNLI3 : leftNLI3=rightNLI3 "
    + "| rNLI3 : leftNLI3=rightNLI3 "
    + "| path2 forwardNLI3 : pNLI3=qNLI3 "
    + "| path2 backwardNLI3 : qNLI3=pNLI3 "
    + "| path2 tailNLI3 : qNLI3=rNLI3 "
    + "| path2 directNLI3 : pNLI3=rNLI3 "
    + "| path3 inverseNLI3 : inveq forwardNLI3=backwardNLI3 "
    + "| path3 composeNLI3 : (forwardNLI3▪tailNLI3)=directNLI3 "
    + "| path3 inverseComposeNLI3 : ((inveq backwardNLI3)▪tailNLI3)=directNLI3";
const { signature: inverseSignature } = register(nonLoopInverse);
for (const path of inverseSignature.pathLevels[2].constructors) {
    assert.equal(path.sourcePoint.name, "leftNLI3",
        `${path.name} must retain the common source point of its one-path boundary`);
    assert.equal(path.targetPoint.name, "rightNLI3",
        `${path.name} must retain the common target point of its one-path boundary`);
}

console.log("sandbox non-indexed definitional HIT boundary regression passed");
