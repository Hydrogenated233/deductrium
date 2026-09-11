import assert from "node:assert/strict";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { ASTParser } from "../js/tt/astparser.js";
import { initTypeSystem } from "../js/tt/initial.js";

const config = { unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_", timeout: 30_000, language: "zh" };
const options = { disableMultipleApply: false, disableDestructConds: false, disableDestructEq: false };
const parser = new ASTParser();
for (const tactic of ["cases", "destruct", "induction"]) {
    const engine = new TTAssistEngine();
    engine.configure(config);
    engine.start("Πf:Bool→Bool,Πb:Bool,(f b)=(f b)", options);
    engine.apply("intros f b");
    const split = engine.apply(`${tactic} (f b)`);
    assert.equal(split.goals.length, 2);
    assert.deepEqual(split.goals.map(goal => parser.stringify(goal.type)), ["(0b=0b)", "(1b=1b)"]);
    for (const goal of split.goals) {
        assert.ok(goal.context.some(([name]) => name === "f"));
        assert.ok(goal.context.some(([name]) => name === "b"));
    }
    assert.deepEqual(engine.start(split.theorem, options, split.history), split);
    engine.apply("rfl");
    engine.apply("rfl");
    const qed = engine.qed();
    const fresh = new TTCoreSession();
    fresh.configure(config);
    assert.equal(fresh.validate(0, parser.parseSurface(`${qed.proof} : ${qed.theorem}`)).ok, true);
}

for (const [target, commands] of [
    ["Πf:True→True×True,True", ["intro f", "cases (f true)", "exact true"]],
    ["Πf:True→(Σn:nat,n=n),True", ["intro f", "cases (f true)", "exact true"]],
    ["Πf:True→True+True,True", ["intro f", "cases (f true)", "exact true", "exact true"]],
    ["Πf:Bool→Bool,Πb:Bool,Πp:(f b)=(f b),Πq:p=p,True",
        ["intros f b p q", "cases (f b) generalizing p q", "exact true", "exact true"]],
    ["Πf:Bool→Bool,Πb:Bool,Πb:Bool,b=b",
        ["intros f b", "cases (f b)", "intro x", "rfl", "intro x", "rfl"]],
    ["Πf:Bool→Bool,Πb:Bool,Πcase:Bool,(f b)=(f b)",
        ["intros f b", "cases (f b)", "intro x", "rfl", "intro x", "rfl"]]
]) {
    const engine = new TTAssistEngine();
    engine.configure(config);
    engine.start(target, options);
    for (const command of commands) engine.apply(command);
    const result = engine.qed();
    const fresh = new TTCoreSession();
    fresh.configure(config);
    const checked = fresh.validate(0, parser.parseSurface(`${result.proof} : ${result.theorem}`));
    assert.equal(checked.ok, true, checked.error);
}
console.log("arbitrary term elimination regression passed");
