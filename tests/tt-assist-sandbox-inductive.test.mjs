import assert from "node:assert/strict";

import { TTAssistEngine } from "../js/tt/assist-engine.js";
import {
    lowerSandboxInductive,
    parseSandboxInductive
} from "../js/tt/sandbox.js";
import { initTypeSystem } from "../js/tt/initial.js";

const bundle = lowerSandboxInductive(parseSandboxInductive(
    "inductive tri : U | nt : tri | 0t : tri | pt : tri"
));
const engine = new TTAssistEngine();
engine.configure({
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

let snapshot = engine.start("Px:tri.x=x", options);
snapshot = engine.apply("intro x");
assert.equal(snapshot.tactics.includes("destruct x"), true,
    "registered sandbox inductives should be recommended for destruct");
assert.equal(snapshot.tactics.includes("induction x"), true,
    "registered sandbox inductives should be recommended for induction");

snapshot = engine.apply("destruct x");
assert.equal(snapshot.goals.length, 3);
assert.deepEqual(snapshot.goals.map(goal => goal.context.map(([name]) => name)), [[], [], []]);
for (let index = 0; index < 3; index++) snapshot = engine.apply("rfl");
assert.equal(snapshot.goals.length, 0);

const qed = engine.qed();
assert.match(qed.proof, /ind_tri/);
assert.match(qed.theorem, /tri/);

snapshot = engine.start("tri", options);
assert.equal(snapshot.tactics.includes("constructor"), true,
    "registered sandbox inductives should expose the Lean-style constructor tactic");
assert.deepEqual(
    snapshot.tactics.filter(tactic => /^(?:exact|apply) (?:nt|0t|pt)$/.test(tactic)),
    ["exact nt", "exact 0t", "exact pt"],
    "registered constructors should be recommended from dynamic metadata"
);
snapshot = engine.apply("constructor");
assert.equal(snapshot.goals.length, 0,
    "constructor should select the first nullary constructor of a sandbox inductive");
assert.match(engine.qed().proof, /nt/);

const natBundle = lowerSandboxInductive(parseSandboxInductive(
    "inductive Nat2 : U | zero2 : Nat2 | succ2 : Nat2 -> Nat2"
));
const natEngine = new TTAssistEngine();
natEngine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    trustedInductives: [natBundle],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

snapshot = natEngine.start("Nat2", options);
assert.equal(snapshot.tactics.includes("exact zero2"), true);
assert.equal(snapshot.tactics.includes("apply succ2"), true);
snapshot = natEngine.apply("constructor");
assert.equal(snapshot.goals.length, 0,
    "constructor should close a recursive inductive target with its first nullary constructor");

snapshot = natEngine.start("Pn:Nat2.n=n", options);
snapshot = natEngine.apply("intro n");
snapshot = natEngine.apply("induction n with d dh");
assert.equal(snapshot.goals.length, 2,
    "dynamic induction should expose one base branch and one recursive branch");
assert.equal(snapshot.goals.some(goal => goal.context.some(([name]) => name === "d")), true);
assert.equal(snapshot.goals.some(goal => goal.context.some(([name]) => name === "dh")), true);
for (let index = 0; index < 2; index++) snapshot = natEngine.apply("rfl");
assert.equal(snapshot.goals.length, 0);
assert.match(natEngine.qed().proof, /λd:Nat2\.\(λdh:/,
    "Lean-style induction names should be written into the generated proof term");

const listBundle = lowerSandboxInductive(parseSandboxInductive(
    "inductive List2 (A : U) : U "
    + "| nil2 : List2 A "
    + "| cons2 : A -> List2 A -> List2 A"
));
const listEngine = new TTAssistEngine();
listEngine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    trustedInductives: [listBundle],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});
const listMetadata = listEngine.engine.core.getInductiveMetadata("List2");
assert.deepEqual(listMetadata.parameters.map(parameter => parameter.name), ["A"],
    "dynamic inductive metadata should retain its uniform parameter telescope");

snapshot = listEngine.start("PA:U,List2 A", options);
snapshot = listEngine.apply("intro A");
assert.equal(snapshot.tactics.includes("exact nil2 A"), true,
    "nullary constructors should receive the instantiated uniform parameter");
assert.equal(snapshot.tactics.includes("apply cons2 A"), true,
    "non-nullary constructors should receive the instantiated uniform parameter");
snapshot = listEngine.apply("constructor");
assert.equal(snapshot.goals.length, 0,
    "constructor should instantiate a parameterized inductive constructor from the goal");
assert.match(listEngine.qed().proof, /nil2 A/);

snapshot = listEngine.start("PA:U,Pxs:List2 A,xs=xs", options);
snapshot = listEngine.apply("intro A");
snapshot = listEngine.apply("intro xs");
assert.equal(snapshot.tactics.includes("destruct xs"), true);
assert.equal(snapshot.tactics.includes("induction xs"), true);
snapshot = listEngine.apply("induction xs with a tail ih");
assert.equal(snapshot.goals.length, 2,
    "parameterized induction should expose one branch per constructor");
const recursiveBranch = snapshot.goals.find(goal =>
    goal.context.some(([name]) => name === "ih")
);
assert.ok(recursiveBranch, "the recursive branch should expose its induction hypothesis");
assert.equal(recursiveBranch.context.some(([name]) => name === "a"), true);
assert.equal(recursiveBranch.context.some(([name]) => name === "tail"), true);
for (let index = 0; index < 2; index++) snapshot = listEngine.apply("rfl");
assert.equal(snapshot.goals.length, 0);
assert.match(listEngine.qed().proof, /ind_List2 A/,
    "destruct/induction should pass the uniform parameter to the eliminator");

const boxBundle = lowerSandboxInductive(parseSandboxInductive(
    "inductive BoxU (u : U@) (A : Uu) : Uu | boxU : A -> BoxU u A"
));
const boxEngine = new TTAssistEngine();
boxEngine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    trustedInductives: [boxBundle],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

snapshot = boxEngine.start("Pu:U@,PA:Uu,Px:BoxU u A,x=x", options);
snapshot = boxEngine.apply("intro u");
snapshot = boxEngine.apply("intro A");
snapshot = boxEngine.apply("intro x");
snapshot = boxEngine.apply("induction x with a");
snapshot = boxEngine.apply("rfl");
assert.equal(snapshot.goals.length, 0,
    "a universe-parameterized sandbox induction should solve all branches");
const boxQed = boxEngine.qed();
assert.match(boxQed.proof, /_ u u A/,
    "high-universe motives must use the implicit full eliminator with its universe level");
assert.match(boxQed.theorem, /BoxU u A/);

console.log("sandbox ordinary-inductive proof-assistant regression passed");
