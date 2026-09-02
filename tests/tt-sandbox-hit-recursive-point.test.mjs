import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { ASTParser } from "../js/tt/astparser.js";
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
    new URL("./fixtures/hit-recursive-point.txt", import.meta.url),
    "utf8"
).trim();
const source3 = readFileSync(
    new URL("./fixtures/hit3-recursive-point.txt", import.meta.url),
    "utf8"
).trim();

const signature = parseSandboxHit(source);
assert.deepEqual(signature.pointConstructors.map(constructor => constructor.name), ["leaf", "step"]);
assert.ok(signature.pointConstructors[1].argumentAsts[0].recursiveTelescope,
    "the recursive point argument must retain its recursive telescope");

assert.throws(
    () => lowerSandboxHit(parseSandboxHit(
        "hit RoseLoop : U "
        + "| roseLeaf : RoseLoop "
        + "| roseNode : (nat→RoseLoop)→RoseLoop "
        + "| roseLoop : roseNode (λn:nat.roseLeaf)=roseNode (λn:nat.roseLeaf)"
    )),
    /函数型递归点参数/,
    "function-recursive point arguments in path endpoints must remain an explicit boundary"
);

const bundle3 = lowerSandboxHit(parseSandboxHit(source3));
assert.equal(bundle3.metadata.kind, "hit3");
assert.equal(bundle3.metadata.constructors
    .find(constructor => constructor.name === "step3").recursiveArguments.length, 1);
const engine3 = new TTCoreEngine();
engine3.configure({ unlockedTypes: creativeSandboxSystemRuleIds });
assert.doesNotThrow(() => engine3.core.registerSystemInductive(bundle3));
for (const name of ["ap3_cell3", "@ap3_cell3", "apd3_cell3", "@apd3_cell3"]) {
    assert.equal(engine3.check(name).ok, true,
        `${name} must form for a recursive point endpoint in a three-dimensional HIT`);
}

const bundle = lowerSandboxHit(signature);
const stepMetadata = bundle.metadata.constructors.find(constructor => constructor.name === "step");
assert.ok(stepMetadata);
assert.equal(stepMetadata.recursiveArguments.length, 1);
assert.equal(stepMetadata.recursiveArguments[0].index, 0);
assert.deepEqual(stepMetadata.recursiveArguments[0].telescope, []);

const sandbox = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const added = sandbox.add(source);
assert.equal(added.ok, true, added.error);
assert.equal(sandbox.check(
    "ind_LoopTree (λ_:LoopTree.True) true (λx:LoopTree.λih:True.true) "
    + "(transconst loopLeaf true) (transconst loopStep true) (step leaf) === true"
).ok, true, "dependent eliminator iota must pass the recursive hypothesis to step");
assert.equal(sandbox.check(
    "rec_LoopTree True true (λx:LoopTree.λih:True.true) rfl rfl (step leaf) === true"
).ok, true, "recursor iota must pass the recursive result to step");

const apdLoopStep = new Map(bundle.auxiliaryTypes).get("apd_loopStep");
assert.ok(apdLoopStep);
const apdLoopStepSource = parser.stringify(apdLoopStep);
assert.match(apdLoopStepSource, /c1 leaf/,
    "the step endpoint must apply the point branch to the recursive argument");
assert.match(apdLoopStepSource, /c1 leaf c0/,
    "the step endpoint must also pass the structurally computed induction hypothesis");

const register = candidate => {
    const engine = new TTCoreEngine();
    engine.configure({ unlockedTypes: creativeSandboxSystemRuleIds });
    return engine.core.registerSystemInductive(candidate);
};
assert.doesNotThrow(() => register(structuredClone(bundle)));
const forged = structuredClone(bundle);
forged.metadata.constructors.find(constructor => constructor.name === "step").recursiveArguments = [];
assert.throws(
    () => register(forged),
    /recursive|递归|metadata.*不一致/i,
    "Core must reject recursive point metadata that disagrees with the constructor type"
);

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
let snapshot = assist.start("Πx:LoopTree,True", assistOptions);
snapshot = assist.apply("intro x");
snapshot = assist.apply("induction x with d ih");
assert.equal(snapshot.goals.length, 4,
    "recursive HIT induction must expose two point and two path branches");
assert.ok(snapshot.goals.some(goal => goal.context.some(([name]) => name === "ih")),
    "the recursive point branch must expose its induction hypothesis");
for (const command of [
    "exact true",
    "exact true",
    "exact transconst loopLeaf true",
    "exact transconst loopStep true"
]) snapshot = assist.apply(command);
assert.equal(snapshot.goals.length, 0);
assert.match(assist.qed().proof, /ind_LoopTree/);

const save = sandbox.toJSON();
assert.equal(Object.hasOwn(save.declarations[0], "hit"), false);
assert.equal(Object.hasOwn(save.declarations[0], "generatedNames"), false);
const worker = new SandboxWorkerSession();
const loaded = worker.handle({
    id: 1,
    kind: "load",
    save,
    options: { systemRuleIds: creativeSandboxSystemRuleIds }
});
assert.equal(loaded.ok, true, loaded.error);
assert.equal(loaded.bridge.inductives[0].metadata.constructors
    .find(constructor => constructor.name === "step").recursiveArguments.length, 1);
assert.equal(worker.handle({
    id: 2,
    kind: "check",
    source: "rec_LoopTree True true (λx:LoopTree.λih:True.true) rfl rfl (step leaf) === true",
    options: { systemRuleIds: creativeSandboxSystemRuleIds }
}).ok, true);

console.log("sandbox recursive-point HIT regression passed");
