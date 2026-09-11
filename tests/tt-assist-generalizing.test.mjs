import assert from "node:assert/strict";
import { isTTAssistTacticUnlocked, TTAssistEngine } from "../js/tt/assist-engine.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { ASTParser } from "../js/tt/astparser.js";
import { initTypeSystem } from "../js/tt/initial.js";

const config = { unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_", timeout: 30_000, language: "zh" };
const options = { disableMultipleApply: false, disableDestructConds: false, disableDestructEq: false };
const parser = new ASTParser();
const engine = new TTAssistEngine();
for (const command of ["cases", "induction"]) {
    assert.equal(isTTAssistTacticUnlocked(command, new Set(["destruct"])), true);
    assert.equal(isTTAssistTacticUnlocked(command, new Set()), false);
}
engine.configure(config);
engine.start("Πn:nat,Πp:n=n,Πq:p=p,True", options);
const before = engine.apply("intros n p q");
assert.throws(() => engine.apply("cases n generalizing p"), /q/);
assert.deepEqual(engine.undo(), engine.start("Πn:nat,Πp:n=n,Πq:p=p,True", options));
engine.start("Πn:nat,Πp:n=n,Πq:p=p,True", options, before.history);
const branches = engine.apply("cases n generalizing p q");
assert.equal(branches.goals.length, 2);
for (const goal of branches.goals) {
    assert.ok(!goal.context.some(([name]) => ["p", "q"].includes(name)));
    assert.equal(parser.stringify(goal.context.find(([name]) => name === "n_q")[1]), "(n_p=n_p)");
}
assert.ok(!branches.goals[0].context.some(([, type]) => /\bn\b/.test(parser.stringify(type))));
engine.apply("exact true");
engine.apply("exact true");
const qed = engine.qed();
const fresh = new TTCoreSession();
fresh.configure(config);
assert.equal(fresh.validate(0, parser.parseSurface(`${qed.proof} : ${qed.theorem}`)).ok, true);

engine.start("Πn:nat,True", options);
engine.apply("intro n");
const saved = engine.start("Πn:nat,True", options, ["intro n"]);
assert.throws(() => engine.apply("cases n generalizing missing"), /missing/);
assert.deepEqual(engine.start("Πn:nat,True", options, ["intro n"]), saved);
engine.start("Πn:nat,Πp:n=n,True", { ...options, disableDestructConds: true });
engine.apply("intros n p");
assert.throws(() => engine.apply("cases n generalizing p"), /解锁/);

for (const command of ["cases n", "induction n generalizing p q with d ih"]) {
    engine.start("Πn:nat,Πp:n=n,Πq:p=p,True", options);
    engine.apply("intros n p q");
    const split = engine.apply(command);
    assert.equal(split.goals.length, 2);
    engine.apply("exact true");
    engine.apply("exact true");
    engine.qed();
}
engine.start("Πn:nat,Πh:True,True", options);
engine.apply("intros n h");
const generalized = engine.apply("cases n generalizing h");
assert.ok(generalized.goals.every(goal => goal.context.some(([name]) => name === "n_h")));
engine.apply("exact n_h");
engine.apply("exact n_h");
engine.qed();
engine.start("Πb:Bool,True", options);
engine.apply("intro b");
assert.throws(() => engine.apply("cases b generalizing [] generalizing []"), /重复/);
const empty = engine.apply("cases b generalizing []");
assert.equal(empty.goals.length, 2);
console.log("explicit dependent generalization regression passed");
