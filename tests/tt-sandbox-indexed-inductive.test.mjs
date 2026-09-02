import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { cloneInductiveBundle } from "../js/tt/gui.js";
import { initTypeSystem } from "../js/tt/initial.js";
import {
    SandboxEnvironment,
    creativeSandboxSystemRuleIds,
    lowerSandboxInductive,
    parseSandboxInductive
} from "../js/tt/sandbox.js";

const parser = new ASTParser();
const source = "inductive Vec (A : U) [n : nat] : U "
    + "| vnil : Vec A 0 "
    + "| vcons : Pn:nat,A -> Vec A n -> Vec A (succ n)";

const signature = parseSandboxInductive(source);
assert.deepEqual(signature.parameters.map(parameter => parameter.name), ["A"]);
assert.deepEqual(signature.indices.map(index => index.name), ["n"]);
assert.deepEqual(
    signature.constructors.map(constructor =>
        constructor.resultIndices.map(index => parser.stringify(index))
    ),
    [["0"], ["(succ n)"]]
);
assert.deepEqual(
    signature.constructors[1].argumentAsts.map(argument =>
        argument.recursiveResultIndices?.map(index => parser.stringify(index)) ?? null
    ),
    [null, null, ["n"]],
    "the recursive Vec argument must retain the index used by its induction hypothesis"
);

assert.throws(
    () => parseSandboxInductive(
        "inductive MissingIndex (A : U) [n : nat] : U | bad : MissingIndex A"
    ),
    /索引.*数量|必须返回/
);
assert.throws(
    () => parseSandboxInductive(
        "inductive NonUniform (A : U) [n : nat] : U | bad : NonUniform True n"
    ),
    /参数.*一致|统一参数/
);

const sandbox = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const result = sandbox.add(source);
assert.equal(result.ok, true, result.error);
assert.equal(sandbox.check("vnil True : Vec True 0").ok, true);
assert.equal(
    sandbox.check("vcons True 0 true (vnil True) : Vec True (succ 0)").ok,
    true
);

const badScope = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const badScopeResult = badScope.add(
    "inductive BadScope (A : U) [n : nat] : U | badScope : BadScope A missing"
);
assert.equal(badScopeResult.ok, false);
assert.match(badScopeResult.declarations[0].error, /missing|未知/);
assert.equal(
    sandbox.check(
        "ind_Vec True (Ln:nat.Lxs:Vec True n.True) "
        + "true (Ln:nat.Lx:True.Lxs:Vec True n.Lih:True.true) "
        + "0 (vnil True) === true"
    ).ok,
    true,
    "the indexed eliminator must compute on vnil"
);
assert.equal(
    sandbox.check(
        "ind_Vec True (Ln:nat.Lxs:Vec True n.True) "
        + "true (Ln:nat.Lx:True.Lxs:Vec True n.Lih:True.true) "
        + "(succ 0) (vcons True 0 true (vnil True)) === true"
    ).ok,
    true,
    "the indexed eliminator must pass the recursive hypothesis to vcons"
);
assert.equal(
    sandbox.check(
        "rec_Vec True nat 0 "
        + "(Ln:nat.Lx:True.Lxs:Vec True n.Lih:nat.succ ih) "
        + "(succ 0) (vcons True 0 true (vnil True)) === succ 0"
    ).ok,
    true,
    "the indexed recursor must compute through the recursive constructor"
);

const bundle = lowerSandboxInductive(signature);
assert.equal(bundle.metadata.version, 2);
assert.equal(bundle.metadata.parameterCount, 1);
assert.equal(bundle.metadata.indexCount, 1);
assert.deepEqual(bundle.metadata.indices.map(index => index.name), ["n"]);
const clonedBundle = cloneInductiveBundle(bundle);
assert.equal(clonedBundle.metadata.parameterCount, 1);
assert.equal(clonedBundle.metadata.indexCount, 1);
assert.deepEqual(clonedBundle.metadata.indices.map(index => index.name), ["n"]);
assert.deepEqual(
    clonedBundle.metadata.constructors[1].resultIndices.map(index => parser.stringify(index)),
    ["(succ n)"]
);

const restored = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
restored.load(sandbox.serialize());
assert.deepEqual(restored.declarations[0].inductive.indices.map(index => index.name), ["n"]);
assert.equal(restored.check("vnil True : Vec True 0").ok, true);

const lifecycle = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const oldDeclaration = lifecycle.add(source).declarations[0];
assert.equal(lifecycle.engine.core.getInductiveMetadata("Vec").indexCount, 1);
assert.equal(lifecycle.replace(
    "inductive Vec2 (A : U) [n : nat] : U | only2 : Pn:nat,Vec2 A n",
    oldDeclaration.id
).ok, true);
assert.equal(lifecycle.check("Vec True 0").ok, false,
    "replacing an indexed signature must revoke the old type and compute rules");
assert.equal(lifecycle.engine.core.getInductiveMetadata("Vec"), undefined);
assert.equal(lifecycle.engine.core.state.computeRules.ind_Vec, undefined);
assert.equal(lifecycle.check("only2 True 0 : Vec2 True 0").ok, true);

const assist = new TTAssistEngine();
assist.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    trustedInductives: [bundle],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});
const options = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};
let constructorSnapshot = assist.start("PA:U,Pa:A,Vec A (succ 0)", options);
constructorSnapshot = assist.apply("intro A");
constructorSnapshot = assist.apply("intro a");
assert.equal(constructorSnapshot.tactics.includes("apply vcons A 0"), true);
assert.equal(constructorSnapshot.tactics.includes("exact vnil A"), false);
constructorSnapshot = assist.apply("constructor");
assert.equal(constructorSnapshot.goals.length, 2,
    "constructor must skip vnil when the target index only matches vcons");
constructorSnapshot = assist.apply("exact a");
constructorSnapshot = assist.apply("constructor");
assert.equal(constructorSnapshot.goals.length, 0);
assert.match(assist.qed().proof, /vcons A 0 a/);

let snapshot = assist.start("PA:U,Pn:nat,Pxs:Vec A n,n=n", options);
snapshot = assist.apply("intro A");
snapshot = assist.apply("intro n");
snapshot = assist.apply("intro xs");
assert.equal(snapshot.tactics.includes("induction xs"), true);
snapshot = assist.apply("induction xs with k a tail ih");
assert.equal(snapshot.goals.length, 2);
assert.equal(snapshot.goals.some(goal => goal.context.some(([name]) => name === "ih")), true);
snapshot = assist.apply("rfl");
snapshot = assist.apply("rfl");
assert.equal(snapshot.goals.length, 0);
const qed = assist.qed();
assert.match(qed.theorem, /Vec A n/);

// Ordinary indexed declarations use the same user-name surface as HITs.
// Names containing the legacy parser markers must survive lowering and later
// proof-assistant applications.
const namedIndexed = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const namedIndexedResult = namedIndexed.add(
    "inductive VecX (PType : U) [idx : nat] : U "
    + "| vnilX : VecX PType 0 "
    + "| vconsX : Pn:nat,Px:PType,VecX PType n -> VecX PType (succ n)"
);
assert.equal(namedIndexedResult.ok, true, namedIndexedResult.error);
assert.equal(namedIndexed.check("vnilX True : VecX True 0").ok, true);
assert.equal(namedIndexed.check(
    "vconsX True 0 true (vnilX True) : VecX True (succ 0)"
).ok, true);
const namedIndexedBundle = namedIndexed.bridge().inductives[0];
const namedIndexedAssist = new TTAssistEngine();
namedIndexedAssist.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    trustedInductives: [namedIndexedBundle],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});
let namedSnapshot = namedIndexedAssist.start("VecX True 0", options);
assert.equal(namedSnapshot.tactics.includes("exact vnilX True"), true);
namedSnapshot = namedIndexedAssist.apply("exact vnilX True");
assert.equal(namedSnapshot.goals.length, 0);

console.log("sandbox indexed-inductive regression passed");
