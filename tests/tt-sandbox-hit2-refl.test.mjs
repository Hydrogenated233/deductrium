import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import {
    SandboxEnvironment,
    creativeSandboxSystemRuleIds,
    lowerSandboxHit,
    parseSandboxHit
} from "../js/tt/sandbox.js";
import { SandboxWorkerSession } from "../js/tt/sandbox-worker.js";

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
const paths = new Map(signature.pathLevels[1].constructors.map(path => [path.name, path]));
const direct = paths.get("directIP2R");
const nested = paths.get("nestedIP2R");
const inverse = paths.get("inverseIP2R");
assert.equal(direct?.leftExpression.kind, "refl");
if (direct?.leftExpression.kind === "refl") {
    assert.equal(direct.leftExpression.pointName, "pointIP2R");
    assert.deepEqual(
        direct.leftExpression.arguments.map(argument => parser.stringify(argument)),
        ["n"]
    );
}
assert.equal(nested?.leftExpression.kind, "compose");
if (nested?.leftExpression.kind === "compose") {
    assert.equal(nested.leftExpression.left.kind, "refl");
}
assert.equal(inverse?.leftExpression.kind, "inverse");
if (inverse?.leftExpression.kind === "inverse") {
    assert.equal(inverse.leftExpression.value.kind, "refl");
}

const bundle = lowerSandboxHit(signature);
const directMetadata = bundle.metadata.pathLevels[1].constructors
    .find(path => path.name === "directIP2R");
assert.equal(directMetadata?.leftExpression.kind, "refl");
if (directMetadata?.leftExpression.kind === "refl") {
    assert.equal(directMetadata.leftExpression.pointName, "pointIP2R");
    assert.deepEqual(
        directMetadata.leftExpression.arguments.map(argument => parser.stringify(argument)),
        directMetadata.argumentNames,
        "lowering must rename refl point arguments consistently with the path2 telescope"
    );
}
assert.doesNotThrow(
    () => register(structuredClone(bundle)),
    "Core must independently certify same-fiber path2 refl endpoints"
);
for (const name of [
    "apd_directIP2R", "@apd_directIP2R",
    "ap_directIP2R", "@ap_directIP2R",
    "ap2_directIP2R", "@ap2_directIP2R"
]) {
    assert.ok(bundle.generatedNames.includes(name),
        `path2 refl lowering must export ${name}`);
}

const sandbox = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const added = sandbox.add(source);
assert.equal(added.ok, true, added.error);
for (const name of [
    "directIP2R", "nestedIP2R", "inverseIP2R",
    "apd_directIP2R", "ap_directIP2R", "ap2_directIP2R"
]) {
    assert.equal(sandbox.check(name).ok, true,
        `the creative sandbox must expose ${name} after path2 refl registration`);
}

const worker = new SandboxWorkerSession();
const restored = worker.handle({
    id: 1,
    kind: "load",
    save: structuredClone(sandbox.toJSON()),
    options: { systemRuleIds: creativeSandboxSystemRuleIds }
});
assert.equal(restored.ok, true, restored.error);
assert.equal(
    restored.bridge.inductives[0].metadata.pathLevels[1].constructors
        .find(path => path.name === "directIP2R")?.leftExpression.kind,
    "refl",
    "source-only save restoration must retain path2 refl metadata"
);
assert.equal(worker.handle({
    id: 2,
    kind: "check",
    source: "ap2_directIP2R",
    options: { systemRuleIds: creativeSandboxSystemRuleIds }
}).ok, true);

for (const [label, invalidSource, error] of [
    [
        "a first-path constructor",
        "hit BadPathRefl : U | pointBPR:BadPathRefl | loopBPR:pointBPR=pointBPR "
            + "| path2 badBPR:refl loopBPR=loopBPR",
        /refl 端点必须由 BadPathRefl 的点构造子形成/
    ],
    [
        "a path2 constructor",
        "hit BadFaceRefl : U | pointBFR:BadFaceRefl | loopBFR:pointBFR=pointBFR "
            + "| path2 faceBFR:loopBFR=loopBFR "
            + "| path2 badBFR:refl faceBFR=loopBFR",
        /refl 端点必须由 BadFaceRefl 的点构造子形成/
    ],
    [
        "an unknown point",
        "hit BadUnknownRefl : U | pointBUR:BadUnknownRefl | loopBUR:pointBUR=pointBUR "
            + "| path2 badBUR:refl missingBUR=loopBUR",
        /refl 端点必须由 BadUnknownRefl 的点构造子形成/
    ],
    [
        "a point constructor with the wrong arity",
        "hit BadArityRefl [n:nat] : U "
            + "| pointBAR:Πn:nat,BadArityRefl n "
            + "| loopBAR:Πn:nat,pointBAR n=pointBAR n "
            + "| path2 badBAR:Πn:nat,refl pointBAR=loopBAR n",
        /refl 端点 pointBAR 参数数量错误/
    ]
]) {
    assert.throws(() => parseSandboxHit(invalidSource), error,
        `path2 refl must reject ${label}`);
}

console.log("sandbox path2 refl endpoint regression passed");
