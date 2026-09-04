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

for (const unsupported of [
    "hit IndexedHit2Compose [n:nat] : U "
        + "| p2d : Πn:nat,IndexedHit2Compose n "
        + "| l2d : Πn:nat,p2d n=p2d n "
        + "| path2 s2d : Πn:nat,(l2d n▪l2d n)=(l2d n▪l2d n)",
    "hit IndexedHit2Inverse [n:nat] : U "
        + "| p2e : Πn:nat,IndexedHit2Inverse n "
        + "| l2e : Πn:nat,p2e n=p2e n "
        + "| path2 s2e : Πn:nat,inveq (l2e n)=inveq (l2e n)"
]) {
    assert.throws(
        () => parseSandboxHit(unsupported),
        /索引.*原子|原子.*索引/i,
        "indexed path2 composition/inverse must stay outside the first supported slice"
    );
}

const indexedPath3Source =
    "hit IndexedHit3 [n : nat] : U | p3 : Πn:nat,IndexedHit3 n "
    + "| l3 : Πn:nat,p3 n=p3 n | path2 s3 : Πn:nat,l3 n=l3 n "
    + "| path3 c3 : Πn:nat,s3 n=s3 n";
assert.throws(
    () => parseSandboxHit(indexedPath3Source),
    /索引.*(?:path3|三维)|(?:path3|三维).*索引/i,
    "indexed path3 must remain an explicit unsupported boundary"
);

// Keep a separate lowerer guard: structured callers can bypass the source parser.
const forgedIndexedPath3 = parseSandboxHit(indexedTwoPathSource);
forgedIndexedPath3.pathLevels[2].constructors.push({});
assert.throws(
    () => lowerSandboxHit(forgedIndexedPath3),
    /索引.*(?:path3|三维)|(?:path3|三维).*索引/i,
    "the lowerer must reject indexed path3 from structured input"
);

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

console.log("sandbox indexed fiberwise hit1/path2 regression passed");
