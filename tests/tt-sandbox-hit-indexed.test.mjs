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

for (const unsupported of [
    "hit IndexedHit2 [n : nat] : U | p2 : Πn:nat,IndexedHit2 n "
        + "| l2 : Πn:nat,p2 n=p2 n | path2 s2 : Πn:nat,l2 n=l2 n",
    "hit IndexedHit3 [n : nat] : U | p3 : Πn:nat,IndexedHit3 n "
        + "| l3 : Πn:nat,p3 n=p3 n | path2 s3 : Πn:nat,l3 n=l3 n "
        + "| path3 c3 : Πn:nat,s3 n=s3 n"
]) {
    assert.throws(
        () => lowerSandboxHit(parseSandboxHit(unsupported)),
        /索引.*(?:path[23]|二维|三维)|(?:path[23]|二维|三维).*索引/i
    );
}

console.log("sandbox indexed fiberwise hit1 regression passed");
