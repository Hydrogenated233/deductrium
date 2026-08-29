import assert from "node:assert/strict";

import { ASTParser } from "../js/fs/astparser.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();
const lockedRules = ["mp", "a1", "a2"];

function addObtainRules(fs) {
    fs.addDeduction("myAndLeft", parser.parse("$0&$1⊢$0"), "test");
    fs.addDeduction("myAndRight", parser.parse("$0&$1⊢$1"), "test");
    fs.addDeduction("myIffLeft", parser.parse("⊢($0<>$1)>($0>$1)"), "test");
    fs.addDeduction("myIffRight", parser.parse("⊢($0<>$1)>($1>$0)"), "test");
    fs.addDeduction("myAnd", parser.parse("$0,$1⊢$0&$1"), "test");
    fs.addDeduction("myOrElim", parser.parse("$0>$2,$1>$2⊢($0|$1)>$2"), "test");
    fs.addDeduction("myOrLeft", parser.parse("$0⊢$0|$1"), "test");
    fs.addDeduction("myOrRight", parser.parse("$1⊢$0|$1"), "test");
    return [...lockedRules, "myAndLeft", "myAndRight", "myIffLeft", "myIffRight", "myAnd",
        "myOrElim", "myOrLeft", "myOrRight"];
}

// Existential strategies stay hidden and report the exact prerequisite when
// their constructor/elimination rules are outside the current unlock scope.
{
    const fs = initFormalSystem(false).fs;
    const useAssistant = new InferenceProofAssistant(fs, "Ex:(x=1)", { ruleNames: lockedRules });
    assert.equal(useAssistant.recommendations().some(command => command.startsWith("use ")), false);
    assert.throws(() => useAssistant.apply("use 1"), /\.Erp|存在量词构造规则/);

    const obtainAssistant = new InferenceProofAssistant(fs, "(Ex:(x=1))>(1=1)", { ruleNames: lockedRules });
    obtainAssistant.apply("intro h");
    assert.equal(obtainAssistant.recommendations().some(command => command.endsWith(":= h")), false);
    assert.throws(() => obtainAssistant.apply("obtain <x,hx> := h"), /\.Emp|存在量词消去规则/);
}

// `use` introduces a concrete witness through the canonical `.Erp` rule and
// leaves the instantiated predicate as the next goal.
{
    const fs = initFormalSystem(false).fs;
    const assistant = new InferenceProofAssistant(fs, "Ex:(x=1)");
    assert.ok(assistant.recommendations().includes("use ??"));
    assistant.apply("use 1");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "1=1");
    assistant.apply("rfl");
    assistant.qed();
    fs.expandMacroWithProp(0);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), parser.stringifyTight(parser.parse("Ex:(x=1)")));
}

// A hidden canonical `.Erp` may be replaced by a structurally equivalent user
// rule, just like the other proof-assistant strategies.
{
    const fs = initFormalSystem(false).fs;
    fs.addDeduction("myErp", parser.parse("⊢#rp($1,$0,$2)>(E$0:$1)"), "test");
    const assistant = new InferenceProofAssistant(fs, "Ex:(x=1)", {
        ruleNames: ["myErp", "a7"]
    });
    assert.ok(assistant.recommendations().includes("use ??"));
    assistant.apply("use 1");
    assistant.apply("rfl");
    assistant.qed();
    fs.expandMacroWithProp(0);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), parser.stringifyTight(parser.parse("Ex:(x=1)")));
}

// Existential obtain introduces a scoped witness and proof, consumes the
// source hypothesis, and materializes through `.Emp` followed by `.Ee`.
{
    const fs = initFormalSystem(false).fs;
    const assistant = new InferenceProofAssistant(fs, "(Ex:(x=1))>(1=1)");
    assistant.apply("intro h");
    assert.ok(assistant.recommendations().some(command => command.endsWith(":= h")));
    assistant.apply("obtain <x,hx> := h");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "1=1");
    assert.equal(assistant.currentGoal.hypotheses.some(item => item.name === "h"), false);
    assert.equal(assistant.currentGoal.hypotheses.find(item => item.name === "x")?.kind, "variable");
    assert.equal(parser.stringifyTight(assistant.currentGoal.hypotheses.find(item => item.name === "hx").proposition), "x=1");
    assistant.apply("rfl");
    assistant.qed();
    fs.expandMacroWithProp(0);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "(Ex:(x=1))>(1=1)");
}

// Locked elimination rules neither recommend nor execute obtain.
{
    const fs = initFormalSystem(false).fs;
    const assistant = new InferenceProofAssistant(fs, "(A&B)>A", { ruleNames: lockedRules });
    assistant.apply("intro h");
    assert.equal(assistant.recommendations().some(command => command.startsWith("obtain ")), false);
    assert.throws(() => assistant.apply("obtain <ha,hb> := h"), /需要解锁|等价推理规则/);
}

// Conjunction obtain creates two real have nodes and survives deferred replay.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addObtainRules(fs);
    const assistant = new InferenceProofAssistant(fs, "(A&B)>(B&A)", { ruleNames });
    assistant.apply("intro h");
    assert.ok(assistant.recommendations().some(command => command.endsWith(":= h")));
    assistant.apply("obtain <ha,hb> := h");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "B&A");
    assert.deepEqual(assistant.currentGoal.hypotheses.slice(-2).map(item => [item.name, parser.stringifyTight(item.proposition)]), [
        ["ha", "A"],
        ["hb", "B"]
    ]);
    assistant.apply("constructor");
    assistant.apply("exact hb");
    assistant.apply("exact ha");
    assert.equal(assistant.snapshot().complete, true);
    assistant.qed();
    fs.expandMacroWithProp(0);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "(A&B)>(B&A)");
}

// Equivalence obtain exposes both implication directions.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addObtainRules(fs);
    const assistant = new InferenceProofAssistant(fs, "(A<>B)>((A>B)&(B>A))", { ruleNames });
    assistant.apply("intro h");
    assistant.apply("obtain <hab,hba> := h");
    assistant.apply("constructor");
    assistant.apply("exact hab");
    assistant.apply("exact hba");
    assert.equal(assistant.snapshot().complete, true);
}

// Reverting and re-introducing a hypothesis must not duplicate discharge rows.
{
    const fs = initFormalSystem(false).fs;
    const assistant = new InferenceProofAssistant(fs, "A>A", { ruleNames: lockedRules });
    assistant.apply("intro h");
    assert.equal(assistant.recommendations().includes("revert h"), false,
        "a direct exact/assumption candidate should suppress the fallback revert suggestion");
    assistant.apply("revert h");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "A>A");
    assert.equal(assistant.currentGoal.hypotheses.some(item => item.name === "h"), false);
    assistant.apply("intro h2");
    assistant.apply("exact h2");
    assistant.qed();
    fs.expandMacroWithProp(0);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "A>A");
}

// Revert remains available as a fallback when no direct strategy matches, but
// it is capped so contexts with many hypotheses do not flood the UI.
{
    const fs = initFormalSystem(false).fs;
    const assistant = new InferenceProofAssistant(fs, "A>(B>(C>goal))", { ruleNames: lockedRules });
    assistant.apply("intros ha hb hc");
    const recommendations = assistant.recommendations();
    assert.deepEqual(recommendations, ["revert ha", "revert hb", "revert hc"]);
}

// A completed have is reverted through an explicit wrapper node: prove A -> B,
// then MP it with the existing A proof so the original theorem stays unchanged.
{
    const fs = initFormalSystem(false).fs;
    const assistant = new InferenceProofAssistant(fs, "A>(A>A)", { ruleNames: lockedRules });
    assistant.apply("intro ha");
    assistant.apply("have hx : A");
    assistant.apply("exact ha");
    assistant.apply("revert hx");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "A>(A>A)");
    assistant.apply("exact a1");
    assert.equal(assistant.snapshot().complete, true);
    assistant.qed();
    fs.expandMacroWithProp(0);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "A>(A>A)");
}

// Reverting an intro inherited from a parent proof node uses the same wrapper
// instead of incorrectly deleting an ancestor's discharge binding.
{
    const fs = initFormalSystem(false).fs;
    const assistant = new InferenceProofAssistant(fs, "A>(A>A)", { ruleNames: lockedRules });
    assistant.apply("intro ha");
    assistant.apply("have hx : A");
    assistant.apply("exact ha");
    assistant.apply("revert ha");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "A>(A>A)");
    assistant.apply("exact a1");
    assistant.qed();
    fs.expandMacroWithProp(0);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "A>(A>A)");
}

// Disjunction obtain creates two independent continuation branches, then uses
// the original source as the final premise of the elimination implication.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addObtainRules(fs);
    const assistant = new InferenceProofAssistant(fs, "(A|B)>(B|A)", { ruleNames });
    assistant.apply("intro h");
    assert.ok(assistant.recommendations().some(command => command.includes(" | ") && command.endsWith(":= h")));
    assistant.apply("obtain ha | hb := h");
    assert.equal(assistant.snapshot().goals.length, 2);
    assert.equal(assistant.currentGoal.hypotheses.at(-1).name, "ha");
    assistant.apply("right");
    assistant.apply("exact ha");
    assert.equal(assistant.currentGoal.hypotheses.at(-1).name, "hb");
    assistant.apply("left");
    assistant.apply("exact hb");
    assert.equal(assistant.snapshot().complete, true);
    assistant.qed();
    fs.expandMacroWithProp(0);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "(A|B)>(B|A)");
}

// The two branch names occupy separate scopes and may intentionally match.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addObtainRules(fs);
    const assistant = new InferenceProofAssistant(fs, "(A|A)>A", { ruleNames });
    assistant.apply("intro source");
    assistant.apply("obtain h | h := source");
    assistant.apply("exact h");
    assistant.apply("exact h");
    assert.equal(assistant.snapshot().complete, true);
}

console.log("inference proof-assistant obtain/revert regression passed");
