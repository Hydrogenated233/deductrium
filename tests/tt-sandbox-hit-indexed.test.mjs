import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";
import {
    SandboxEnvironment,
    creativeSandboxSystemRuleIds,
    lowerSandboxHit,
    parseSandboxHit
} from "../js/tt/sandbox.js";
import { SandboxWorkerSession } from "../js/tt/sandbox-worker.js";

const parser = new ASTParser();
const source = readFileSync(
    new URL("./fixtures/hit-indexed-fiberwise.txt", import.meta.url),
    "utf8"
).trim();

const signature = parseSandboxHit(source);
assert.deepEqual(signature.indices.map(index => index.name), ["n"]);
assert.deepEqual(
    signature.pointConstructors.map(constructor =>
        constructor.resultIndices.map(index => parser.stringify(index))
    ),
    [["n"], ["(succ n)"]]
);
assert.deepEqual(
    signature.pointConstructors[1].argumentAsts.map(argument =>
        argument.recursiveResultIndices?.map(index => parser.stringify(index)) ?? null
    ),
    [null, ["n"]],
    "the indexed recursive point must retain its child fiber"
);
assert.deepEqual(
    signature.pathLevels[0].constructors[0].arguments.map(argument => argument.name),
    ["n"]
);

const bundle = lowerSandboxHit(signature);
assert.equal(bundle.metadata.kind, "hit1");
assert.equal(bundle.metadata.indexCount, 1);
assert.deepEqual(bundle.metadata.indices.map(index => index.name), ["n"]);
const stepMetadata = bundle.metadata.constructors.find(constructor => constructor.name === "stepF");
assert.ok(stepMetadata);
assert.equal(stepMetadata.recursiveArguments.length, 1);
assert.equal(stepMetadata.recursiveArguments[0].index, 1);
assert.deepEqual(
    stepMetadata.recursiveArguments[0].resultIndices.map(index => parser.stringify(index)),
    ["n"]
);
for (const name of ["loopF", "apd_loopF", "@apd_loopF", "ap_loopF", "@ap_loopF"]) {
    assert.ok(new Map(bundle.auxiliaryTypes).has(name), `indexed hit1 must export ${name}`);
}

const register = candidate => {
    const engine = new TTCoreEngine();
    engine.configure({ unlockedTypes: creativeSandboxSystemRuleIds });
    return engine.core.registerSystemInductive(candidate);
};
assert.doesNotThrow(() => register(structuredClone(bundle)));

const parameterizedRecursive = new SandboxEnvironment({
    systemRuleIds: creativeSandboxSystemRuleIds
});
const parameterizedRecursiveResult = parameterizedRecursive.add(
    "hit ParamRecursiveFiber (A:U) [n:nat] : U "
    + "| basePRF : Πn:nat,A→ParamRecursiveFiber A n "
    + "| stepPRF : Πn:nat,ParamRecursiveFiber A n→ParamRecursiveFiber A n "
    + "| loopPRF : Πn:nat,Πa:A,"
    + "stepPRF n (basePRF n a)=stepPRF n (basePRF n a)"
);
assert.equal(parameterizedRecursiveResult.ok, true, parameterizedRecursiveResult.error);
for (const name of ["apd_loopPRF", "ap_loopPRF"]) {
    assert.equal(parameterizedRecursive.check(name).ok, true,
        `parameterized indexed recursive endpoint must generate ${name}`);
}

for (const [label, source] of [
    ["non-final constructor with an extra argument",
        "hit PairFiber (A:U) [n:nat] : U "
        + "| leftP : Πn:nat,A→PairFiber A n "
        + "| rightP : Πn:nat,PairFiber A n "
        + "| bridgeP : Πn:nat,Πa:A,leftP n a=rightP n"],
    ["reordered control with the extra-argument constructor last",
        "hit PairFiberRev (A:U) [n:nat] : U "
        + "| leftR : Πn:nat,PairFiberRev A n "
        + "| rightR : Πn:nat,A→PairFiberRev A n "
        + "| bridgeR : Πn:nat,Πa:A,leftR n=rightR n a"],
    ["middle constructor with an extra argument",
        "hit TripleFiber (A:U) [n:nat] : U "
        + "| firstT : Πn:nat,TripleFiber A n "
        + "| middleT : Πn:nat,A→TripleFiber A n "
        + "| lastT : Πn:nat,TripleFiber A n "
        + "| bridgeT : Πn:nat,Πa:A,middleT n a=lastT n"]
]) {
    const candidate = lowerSandboxHit(parseSandboxHit(source));
    assert.doesNotThrow(
        () => register(structuredClone(candidate)),
        `canonical iota validation must not depend on constructor order: ${label}`
    );
}

const betaFiberBundle = lowerSandboxHit(parseSandboxHit(
    "hit BetaFiber [n:nat] : U "
    + "| pF : Πn:nat,BetaFiber n "
    + "| lF : Πn:nat,pF ((λx:nat.x) n)=pF n"
));
assert.doesNotThrow(
    () => register(betaFiberBundle),
    "definitionally equal endpoint indices must inhabit the same fiber"
);
const previousAssertionBudget = Core.semanticTypeAssertionMaxSteps;
try {
    Core.semanticTypeAssertionMaxSteps = 1;
    assert.throws(
        () => register(structuredClone(betaFiberBundle)),
        /资源耗尽/,
        "an exhausted NbE equality check must never certify the endpoint fiber"
    );
} finally {
    Core.semanticTypeAssertionMaxSteps = previousAssertionBudget;
}

const differentFiberBundle = lowerSandboxHit(parseSandboxHit(
    "hit BadFiberCore [n:nat] : U "
    + "| pointBCore : Πn:nat,BadFiberCore n "
    + "| badLoopCore : pointBCore 0=pointBCore (succ 0)"
));
assert.throws(
    () => register(differentFiberBundle),
    /fiber|纤维/i,
    "Core must reject genuinely different endpoint fibers"
);

const badIndex = structuredClone(bundle);
badIndex.metadata.constructors
    .find(constructor => constructor.name === "stepF")
    .resultIndices = [parser.parse("n")];
assert.throws(
    () => register(badIndex),
    /索引|metadata.*不一致/,
    "Core must reconstruct indexed point results instead of trusting metadata"
);

const badComputation = structuredClone(bundle);
const apdIndex = badComputation.auxiliaryTypes.findIndex(([name]) => name === "apd_loopF");
badComputation.auxiliaryTypes[apdIndex][1] = parser.parse("True");
assert.throws(
    () => register(badComputation),
    /apd_loopF|计算|coherence|等式/,
    "Core must reject a forged indexed path-computation proposition"
);

const sandbox = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const added = sandbox.add(source);
assert.equal(added.ok, true, added.error);
assert.equal(sandbox.check("baseF 0 : FiberLoop 0").ok, true);
assert.equal(sandbox.check("stepF 0 (baseF 0) : FiberLoop (succ 0)").ok, true);

const motive = "(λn:nat.λx:FiberLoop n.True)";
const baseMethod = "(λn:nat.true)";
const stepMethod = "(λn:nat.λx:FiberLoop n.λih:True.true)";
const pathMethod = "(λn:nat.transconst (loopF n) true)";
assert.equal(sandbox.check(
    `ind_FiberLoop ${motive} ${baseMethod} ${stepMethod} ${pathMethod} `
    + "(succ 0) (stepF 0 (baseF 0)) === true"
).ok, true, "indexed HIT induction must compute through a recursive point");
assert.equal(sandbox.check(
    "rec_FiberLoop True (\u03bbn:nat.true) "
    + "(λn:nat.λx:FiberLoop n.λih:True.true) (λn:nat.rfl) "
    + "(succ 0) (stepF 0 (baseF 0)) === true"
).ok, true, "indexed HIT recursion must compute through a recursive point");

const assist = new TTAssistEngine();
assist.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    trustedInductives: [bundle],
    inferDisplayMode: "_",
    timeout: 60_000,
    language: "zh"
});
const assistOptions = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};
let snapshot = assist.start("Πn:nat,Πx:FiberLoop n,True", assistOptions);
snapshot = assist.apply("intro n");
snapshot = assist.apply("intro x");
snapshot = assist.apply("induction x");
assert.equal(snapshot.goals.length, 3,
    "indexed hit1 induction must expose base, recursive-point, and path branches");
assert.ok(snapshot.goals.some(goal =>
    goal.context.some(([name]) => name.includes("ih"))
), "the recursive indexed branch must expose an induction hypothesis");
const pathIndexName = snapshot.goals[2].context.find(([name, type]) =>
    name !== "n" && parser.stringify(type) === "nat"
)?.[0];
assert.ok(pathIndexName, "the path branch must expose its fiber index");
for (const command of [
    "exact true",
    "exact true",
    `exact transconst (loopF ${pathIndexName}) true`
]) snapshot = assist.apply(command);
assert.equal(snapshot.goals.length, 0,
    "indexed hit1 induction must close its base, recursive, and path branches");
const qed = assist.qed();
assert.match(qed.proof, /ind_FiberLoop/,
    "qed must retain the indexed HIT eliminator rather than bypassing induction");
assert.match(qed.theorem, /FiberLoop n/);

const save = sandbox.toJSON();
assert.equal(Object.hasOwn(save.declarations[0], "hit"), false);
const worker = new SandboxWorkerSession();
const loaded = worker.handle({
    id: 1,
    kind: "load",
    save,
    options: { systemRuleIds: creativeSandboxSystemRuleIds }
});
assert.equal(loaded.ok, true, loaded.error);
assert.equal(loaded.bridge.inductives[0].metadata.indexCount, 1);

const differentFibers = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const differentFibersResult = differentFibers.add(
    "hit BadFiber [n : nat] : U "
    + "| pointB : Πn:nat,BadFiber n "
    + "| badLoop : pointB 0=pointB (succ 0)"
);
assert.equal(differentFibersResult.ok, false);
assert.match(differentFibersResult.declarations[0].error ?? "", /索引|类型|断言|fiber|纤维/i);

const indexedTwoPathSource =
    "hit IndexedHit2 [n : nat] : U "
    + "| p2 : Πn:nat,IndexedHit2 n "
    + "| l20 : Πn:nat,p2 n=p2 n "
    + "| l21 : Πn:nat,p2 n=p2 n "
    + "| path2 s2 : Πn:nat,l20 n=l21 n";
const indexedTwoPathSignature = parseSandboxHit(indexedTwoPathSource);
const indexedTwoPath = indexedTwoPathSignature.pathLevels[1].constructors[0];
assert.equal(indexedTwoPath.leftExpression.kind, "atom");
assert.equal(indexedTwoPath.rightExpression.kind, "atom");
assert.equal(indexedTwoPath.resultIndices.length, 1);
assert.equal(
    parser.stringify(indexedTwoPath.resultIndices[0]),
    indexedTwoPath.arguments[0].name,
    "indexed path2 must retain the common first-path fiber"
);

const indexedTwoPathBundle = lowerSandboxHit(indexedTwoPathSignature);
assert.equal(indexedTwoPathBundle.metadata.kind, "hit2");
assert.equal(indexedTwoPathBundle.metadata.indexCount, 1);
for (const name of [
    "apd_s2", "@apd_s2", "ap_s2", "@ap_s2", "ap2_s2", "@ap2_s2"
]) {
    assert.ok(
        new Map(indexedTwoPathBundle.auxiliaryTypes).has(name),
        `indexed path2 must export ${name}`
    );
}
assert.doesNotThrow(
    () => register(structuredClone(indexedTwoPathBundle)),
    "same-fiber atomic indexed path2 must pass Core certification"
);

const betaIndexedTwoPath = lowerSandboxHit(parseSandboxHit(
    "hit IndexedHit2Beta [n:nat] : U "
    + "| p2b : Πn:nat,IndexedHit2Beta n "
    + "| l20b : Πn:nat,p2b n=p2b n "
    + "| l21b : Πn:nat,p2b n=p2b n "
    + "| path2 s2b : Πn:nat,l20b n=l21b ((λx:nat.x) n)"
));
assert.doesNotThrow(
    () => register(betaIndexedTwoPath),
    "definitionally equal indexed path2 fibers must not be rejected syntactically"
);

const forgedTwoPathIndex = structuredClone(indexedTwoPathBundle);
const forgedTwoPathMetadata = forgedTwoPathIndex.metadata.pathLevels[1].constructors[0];
forgedTwoPathMetadata.resultIndices = [parser.parse(
    `succ ${forgedTwoPathMetadata.argumentNames[0]}`
)];
assert.throws(
    () => register(forgedTwoPathIndex),
    /索引|metadata|纤维/i,
    "Core must reconstruct indexed path2 fibers instead of trusting metadata"
);

const crossFiberTwoPath = lowerSandboxHit(parseSandboxHit(
    "hit IndexedHit2Cross [n:nat] : U "
    + "| p2c : Πn:nat,IndexedHit2Cross n "
    + "| l20c : Πn:nat,p2c n=p2c n "
    + "| l21c : Πn:nat,p2c (succ n)=p2c (succ n) "
    + "| path2 s2c : Πn:nat,l20c n=l21c n"
));
assert.throws(
    () => register(crossFiberTwoPath),
    /索引|纤维|类型|相等/i,
    "Core must reject genuinely different indexed path2 endpoint fibers"
);

const indexedPath3Source =
    "hit IndexedHit3 [n : nat] : U "
    + "| point3 : Πn:nat,IndexedHit3 n "
    + "| loop30 : Πn:nat,point3 n=point3 n "
    + "| loop31 : Πn:nat,point3 n=point3 n "
    + "| path2 face30 : Πn:nat,loop30 n=loop31 n "
    + "| path2 face31 : Πn:nat,loop30 n=loop31 n "
    + "| path3 cell3 : Πn:nat,face30 n=face31 n";
const indexedPath3Signature = parseSandboxHit(indexedPath3Source);
const indexedPath3 = indexedPath3Signature.pathLevels[2].constructors[0];
assert.equal(indexedPath3.leftExpression.kind, "atom");
assert.equal(indexedPath3.rightExpression.kind, "atom");
assert.equal(indexedPath3.resultIndices.length, 1);
assert.equal(
    parser.stringify(indexedPath3.resultIndices[0]),
    indexedPath3.arguments[0].name,
    "same-fiber indexed path3 must retain its common index"
);

const indexedPath3Bundle = lowerSandboxHit(indexedPath3Signature);
assert.equal(indexedPath3Bundle.metadata.kind, "hit3");
assert.equal(indexedPath3Bundle.metadata.indexCount, 1);
const indexedPath3Metadata = indexedPath3Bundle.metadata.pathLevels[2].constructors[0];
assert.equal(indexedPath3Metadata.leftExpression.kind, "atom");
assert.equal(indexedPath3Metadata.rightExpression.kind, "atom");
assert.deepEqual(
    indexedPath3Metadata.resultIndices.map(index => parser.stringify(index)),
    [indexedPath3Metadata.argumentNames[0]],
    "lowering must retain canonical indexed path3 result metadata"
);
for (const name of [
    "cell3", "apd3_cell3", "@apd3_cell3", "ap3_cell3", "@ap3_cell3"
]) {
    assert.ok(
        new Map(indexedPath3Bundle.auxiliaryTypes).has(name),
        `indexed path3 must export ${name}`
    );
}
assert.doesNotThrow(
    () => register(structuredClone(indexedPath3Bundle)),
    "same-fiber atomic indexed path3 must pass Core certification"
);

// `ap3` has an internal binder conventionally named `p`.  A user point
// constructor with that legal name must remain a free constructor while its
// generated path3 computation types are checked, rather than being captured
// by the primitive's local binder.
const twoIndexPointPPath3 = lowerSandboxHit(parseSandboxHit(
    "hit Bi [i:nat] [j:nat] : U "
    + "| p:Πi:nat,Πj:nat,Bi i j "
    + "| l0:Πi:nat,Πj:nat,p i j=p i j "
    + "| l1:Πi:nat,Πj:nat,p i j=p i j "
    + "| path2 f0:Πi:nat,Πj:nat,l0 i j=l1 i j "
    + "| path2 f1:Πi:nat,Πj:nat,l0 i j=l1 i j "
    + "| path3 c:Πi:nat,Πj:nat,f0 i j=f1 i j"
));
assert.doesNotThrow(
    () => register(twoIndexPointPPath3),
    "a point constructor named p must not overflow path3 Core registration"
);

// A definitionally equal index cannot be rejected merely because one endpoint
// contains a beta redex.  The parser must carry that semantic equality through
// lowering and Core certification instead of requiring spelling equality.
const betaIndexedPath3 = lowerSandboxHit(parseSandboxHit(
    "hit IndexedHit3Beta [n:nat] : U "
    + "| point3b : Πn:nat,IndexedHit3Beta n "
    + "| loop3b0 : Πn:nat,point3b n=point3b n "
    + "| loop3b1 : Πn:nat,point3b n=point3b n "
    + "| path2 face3b0 : Πn:nat,loop3b0 n=loop3b1 n "
    + "| path2 face3b1 : Πn:nat,loop3b0 n=loop3b1 n "
    + "| path3 cell3b : Πn:nat,face3b0 ((λx:nat.x) n)=face3b1 n"
));
assert.doesNotThrow(
    () => register(betaIndexedPath3),
    "definitionally equal indexed path3 fibers must not be rejected syntactically"
);

// Parsed source always fills these arrays, but lowerSandboxHit is also a
// structured-input boundary for restored saves and bridge callers.
const missingIndexedPath3Indices = structuredClone(indexedPath3Signature);
delete missingIndexedPath3Indices.pathLevels[2].constructors[0].resultIndices;
assert.throws(
    () => lowerSandboxHit(missingIndexedPath3Indices),
    /三阶路径构造子.*resultIndices.*索引数量不一致/,
    "the lowerer must reject missing indexed path3 result metadata"
);

const forgedIndexedPath3Indices = structuredClone(indexedPath3Bundle);
const forgedIndexedPath3Metadata = forgedIndexedPath3Indices.metadata.pathLevels[2].constructors[0];
forgedIndexedPath3Metadata.resultIndices = [parser.parse(
    `succ ${forgedIndexedPath3Metadata.argumentNames[0]}`
)];
assert.throws(
    () => register(forgedIndexedPath3Indices),
    /索引|metadata|纤维/i,
    "Core must reconstruct indexed path3 fibers instead of trusting forged metadata"
);

const missingIndexedPath3Metadata = structuredClone(indexedPath3Bundle);
delete missingIndexedPath3Metadata.metadata.pathLevels[2].constructors[0].resultIndices;
assert.throws(
    () => register(missingIndexedPath3Metadata),
    /resultIndices|索引|metadata/i,
    "Core must reject missing indexed path3 metadata from a forged bridge"
);

const crossFiberIndexedPath3 = lowerSandboxHit(parseSandboxHit(
    "hit IndexedHit3Cross [n:nat] : U "
    + "| point3c : Πn:nat,IndexedHit3Cross n "
    + "| loop3c0 : Πn:nat,point3c n=point3c n "
    + "| loop3c1 : Πn:nat,point3c (succ n)=point3c (succ n) "
    + "| path2 face3c0 : Πn:nat,loop3c0 n=loop3c0 n "
    + "| path2 face3c1 : Πn:nat,loop3c1 n=loop3c1 n "
    + "| path3 cell3c : Πn:nat,face3c0 n=face3c1 n"
));
assert.throws(
    () => register(crossFiberIndexedPath3),
    /端点索引|索引.*纤维|纤维.*不一致|metadata.*索引/i,
    "an indexed path3 must not bridge genuinely different fibers"
);

const indexedPath3ComposeSource =
    "hit IndexedHit3Compose [n:nat] : U "
    + "| point3d : Πn:nat,IndexedHit3Compose n "
    + "| loop3d : Πn:nat,point3d n=point3d n "
    + "| path2 face3d : Πn:nat,loop3d n=loop3d n "
    + "| path3 cell3d : Πn:nat,(face3d n▪face3d n)=face3d n";
const indexedPath3ComposeBundle = lowerSandboxHit(
    parseSandboxHit(indexedPath3ComposeSource)
);
assert.equal(
    indexedPath3ComposeBundle.metadata.pathLevels[2].constructors[0].leftExpression.kind,
    "compose",
    "indexed path3 composition metadata must survive lowering"
);
assert.doesNotThrow(
    () => register(structuredClone(indexedPath3ComposeBundle)),
    "indexed path3 composition endpoints must be certifiable"
);

const indexedPath3InverseSource =
    "hit IndexedHit3Inverse [n:nat] : U "
    + "| point3e : Πn:nat,IndexedHit3Inverse n "
    + "| loop3e : Πn:nat,point3e n=point3e n "
    + "| path2 face3e : Πn:nat,loop3e n=loop3e n "
    + "| path3 cell3e : Πn:nat,inveq (face3e n)=face3e n";
const indexedPath3InverseBundle = lowerSandboxHit(
    parseSandboxHit(indexedPath3InverseSource)
);
assert.equal(
    indexedPath3InverseBundle.metadata.pathLevels[2].constructors[0].leftExpression.kind,
    "inverse",
    "indexed path3 inverse metadata must survive lowering"
);
assert.doesNotThrow(
    () => register(structuredClone(indexedPath3InverseBundle)),
    "indexed path3 inverse endpoints must be certifiable"
);

assert.throws(
    () => parseSandboxHit(
        "hit IndexedHit3Refl [n:nat] : U "
        + "| point3r : Πn:nat,IndexedHit3Refl n "
        + "| loop3r : Πn:nat,point3r n=point3r n "
        + "| path2 face3r : Πn:nat,loop3r n=loop3r n "
        + "| path3 cell3r : Πn:nat,(refl (loop3r n))=face3r n"
    ),
    /索引 HIT 三阶路径构造子.*refl 二阶路径端点/,
    "indexed path3 refl endpoints must remain outside the supported slice"
);

for (const [label, source] of [
    [
        "composition",
        "hit IndexedHit3ReflCompose [n:nat] : U "
        + "| point3rc : Πn:nat,IndexedHit3ReflCompose n "
        + "| loop3rc : Πn:nat,point3rc n=point3rc n "
        + "| path2 face3rc : Πn:nat,loop3rc n=loop3rc n "
        + "| path3 cell3rc : Πn:nat,((refl (loop3rc n))▪face3rc n)=face3rc n"
    ],
    [
        "inverse",
        "hit IndexedHit3ReflInverse [n:nat] : U "
        + "| point3ri : Πn:nat,IndexedHit3ReflInverse n "
        + "| loop3ri : Πn:nat,point3ri n=point3ri n "
        + "| path2 face3ri : Πn:nat,loop3ri n=loop3ri n "
        + "| path3 cell3ri : Πn:nat,inveq (refl (loop3ri n))=face3ri n"
    ]
]) {
    assert.throws(
        () => parseSandboxHit(source),
        /索引 HIT 三阶路径构造子.*refl 二阶路径端点/,
        `indexed path3 ${label} must not bypass the refl boundary`
    );
}

const forgedIndexedPath3Refl = structuredClone(indexedPath3Signature);
forgedIndexedPath3Refl.pathLevels[2].constructors[0].leftExpression = {
    kind: "inverse",
    value: { kind: "refl", pathName: "loop30", arguments: [parser.parse("n")] }
};
assert.throws(
    () => lowerSandboxHit(forgedIndexedPath3Refl),
    /索引 HIT 三阶路径构造子.*refl 二阶路径端点/,
    "structured indexed path3 input must not bypass the recursive refl boundary"
);

const indexedPath3Sandbox = new SandboxEnvironment({
    systemRuleIds: creativeSandboxSystemRuleIds
});
const indexedPath3Added = indexedPath3Sandbox.add(indexedPath3Source);
assert.equal(indexedPath3Added.ok, true, indexedPath3Added.error);
for (const name of [
    "cell3", "apd3_cell3", "@apd3_cell3", "ap3_cell3", "@ap3_cell3"
]) {
    assert.equal(
        indexedPath3Sandbox.check(name).ok,
        true,
        `the indexed path3 sandbox bridge must expose ${name}`
    );
}
const indexedPath3Save = indexedPath3Sandbox.toJSON();
assert.equal(Object.hasOwn(indexedPath3Save.declarations[0], "hit"), false);
const indexedPath3Worker = new SandboxWorkerSession();
const indexedPath3Loaded = indexedPath3Worker.handle({
    id: 3,
    kind: "load",
    save: indexedPath3Save,
    options: { systemRuleIds: creativeSandboxSystemRuleIds }
});
assert.equal(indexedPath3Loaded.ok, true, indexedPath3Loaded.error);
assert.equal(indexedPath3Loaded.bridge.inductives[0].metadata.kind, "hit3");
assert.equal(
    indexedPath3Loaded.bridge.inductives[0].metadata.pathLevels[2].constructors[0]
        .resultIndices.length,
    1,
    "the worker/save bridge must preserve indexed path3 result metadata"
);
assert.equal(indexedPath3Worker.handle({
    id: 4,
    kind: "check",
    source: "apd3_cell3",
    options: { systemRuleIds: creativeSandboxSystemRuleIds }
}).ok, true, "the restored indexed path3 bridge must retain apd3 exports");

const indexedPath3Assist = new TTAssistEngine();
indexedPath3Assist.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    trustedInductives: [indexedPath3Bundle],
    inferDisplayMode: "_",
    timeout: 60_000,
    language: "zh"
});
let indexedPath3Snapshot = indexedPath3Assist.start(
    parser.stringify(indexedPath3Bundle.eliminator[1]),
    assistOptions
);
for (const command of [
    "intro C", "intro c0",
    "intro p0", "intro p1",
    "intro p2_0", "intro p2_1", "intro p3_0",
    "intro n", "intro x", "induction x"
]) indexedPath3Snapshot = indexedPath3Assist.apply(command);
assert.equal(indexedPath3Snapshot.goals.length, 6,
    "indexed hit3 induction must expose point, path, path2, and path3 branches");
for (const method of ["c0", "p0", "p1", "p2_0", "p2_1", "p3_0"]) {
    const branchIndexName = indexedPath3Snapshot.goals[0]?.context.find(([name, type]) =>
        name !== "n" && parser.stringify(type) === "nat"
    )?.[0];
    assert.ok(branchIndexName,
        `indexed hit3 ${method} branch must expose its local fiber index`);
    indexedPath3Snapshot = indexedPath3Assist.apply(`exact ${method} ${branchIndexName}`);
}
assert.equal(indexedPath3Snapshot.goals.length, 0,
    "proof-assistant induction must discharge the indexed path3 coherence branch");
assert.match(indexedPath3Assist.qed().proof, /ind_IndexedHit3/);

const indexedTwoPathSandbox = new SandboxEnvironment({
    systemRuleIds: creativeSandboxSystemRuleIds
});
const indexedTwoPathAdded = indexedTwoPathSandbox.add(indexedTwoPathSource);
assert.equal(indexedTwoPathAdded.ok, true, indexedTwoPathAdded.error);
for (const name of ["apd_s2", "ap_s2", "ap2_s2"]) {
    assert.equal(
        indexedTwoPathSandbox.check(name).ok,
        true,
        `the sandbox bridge must expose ${name}`
    );
}
const indexedTwoPathWorker = new SandboxWorkerSession();
const indexedTwoPathLoaded = indexedTwoPathWorker.handle({
    id: 2,
    kind: "load",
    save: indexedTwoPathSandbox.toJSON(),
    options: { systemRuleIds: creativeSandboxSystemRuleIds }
});
assert.equal(indexedTwoPathLoaded.ok, true, indexedTwoPathLoaded.error);
assert.equal(indexedTwoPathLoaded.bridge.inductives[0].metadata.kind, "hit2");

const indexedTwoPathAssist = new TTAssistEngine();
indexedTwoPathAssist.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    trustedInductives: [indexedTwoPathBundle],
    inferDisplayMode: "_",
    timeout: 60_000,
    language: "zh"
});
let indexedTwoPathSnapshot = indexedTwoPathAssist.start(
    "Πn:nat,Πx:IndexedHit2 n,True",
    assistOptions
);
for (const command of ["intro n", "intro x", "induction x"]) {
    indexedTwoPathSnapshot = indexedTwoPathAssist.apply(command);
}
assert.equal(indexedTwoPathSnapshot.error, undefined);
assert.equal(
    indexedTwoPathSnapshot.goals.length,
    4,
    "indexed hit2 induction must expose point, two path, and path2 coherence branches"
);
assert.ok(
    indexedTwoPathSnapshot.goals[3].context.some(([name]) => name.includes("path2")),
    "the indexed path2 coherence branch must retain its fiber index"
);

// Indexed recursive points must carry the child fiber explicitly.  The
// lowerer is also a trust boundary for structured callers, so reject missing
// or truncated metadata before it can produce a malformed bundle/TypeError.
const recursiveEndpointSource = "hit FiberTree [n:nat] : U "
    + "| leafTree : Πn:nat,FiberTree n "
    + "| stepTree : Πn:nat,FiberTree n→FiberTree (succ n) "
    + "| loopTree : Πn:nat,stepTree n (leafTree n)=stepTree n (leafTree n)";
const recursiveEndpointSignature = parseSandboxHit(recursiveEndpointSource);
const recursivePoint = recursiveEndpointSignature.pointConstructors
    .find(constructor => constructor.name === "stepTree");
assert.deepEqual(
    recursivePoint?.argumentAsts[1].recursiveResultIndices
        ?.map(index => parser.stringify(index)),
    ["n"],
    "indexed recursive point arguments must retain their child fiber"
);
const recursiveEndpointBundle = lowerSandboxHit(recursiveEndpointSignature);
assert.doesNotThrow(
    () => register(structuredClone(recursiveEndpointBundle)),
    "same-fiber paths over indexed recursive points must remain certifiable"
);
const forgedRecursiveIndices = structuredClone(recursiveEndpointSignature);
forgedRecursiveIndices.pointConstructors
    .find(constructor => constructor.name === "stepTree")
    .argumentAsts[1].recursiveResultIndices = [];
assert.throws(
    () => lowerSandboxHit(forgedRecursiveIndices),
    /递归参数.*resultIndices.*索引数量不一致/,
    "the lowerer must reject truncated indexed recursive result metadata"
);
const forgedPathIndices = structuredClone(recursiveEndpointSignature);
delete forgedPathIndices.pathLevels[0].constructors[0].resultIndices;
assert.throws(
    () => lowerSandboxHit(forgedPathIndices),
    /一阶路径构造子.*resultIndices.*索引数量不一致/,
    "the lowerer must reject missing indexed path result metadata"
);

console.log("sandbox indexed fiberwise hit1/path2/path3 regression passed");
