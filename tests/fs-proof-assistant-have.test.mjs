import assert from "node:assert/strict";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { ASTParser } from "../js/fs/astparser.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();

// Lean-style declaration opens the same proof subgoal as legacy
// `have proposition name`, while binding the name before the continuation.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assistant.apply("intro h");
    assistant.apply("have hp : A");
    assert.equal(assistant.snapshot().goals.length, 2);
    assistant.apply("exact h");
    assistant.apply("exact hp");
    assert.equal(assistant.snapshot().complete, true);
}

// `have name := source arg...` specializes universal quantifiers of a local
// hypothesis immediately, without opening a new goal.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "(Vx:Vy:(x=y))>(A=B)");
    assistant.apply("intro h");
    assistant.apply("have hab := h A B");
    assert.equal(assistant.snapshot().goals.length, 1);
    assert.equal(parser.stringifyTight(assistant.currentGoal.hypotheses.at(-1).proposition), "A=B");
    assistant.apply("exact hab");
    assert.equal(assistant.snapshot().complete, true);
}

// A rule with explicit replacement arguments can be introduced as a local
// fact.  The argument order is the rule's declared replacement order, and
// `$`-named expressions remain valid surface terms.
{
    const fs = initFormalSystem(true).fs;
    const target = "(E$0:(E$1:$2))<>~(V$0:(V$1:~$2))";
    const assistant = new InferenceProofAssistant(fs, target);
    assistant.apply("have h := .nVVn $0 $1 $2");
    assert.equal(parser.stringifyTight(assistant.currentGoal.hypotheses.at(-1).proposition), target);
    assistant.apply("exact h");
    assistant.qed();
    fs.expandMacroWithProp(0);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), target);
}

// Rules with premises open a normal `have` subgoal and bind the instantiated
// conclusion only after that subgoal has been solved.
{
    const fs = initFormalSystem(false).fs;
    fs.addDeduction("deriveB", parser.parse("A⊢B"), "test");
    fs.addHypothese(parser.parse("A"));
    const assistant = new InferenceProofAssistant(fs, "B");
    assistant.apply("have h := deriveB");
    assert.equal(assistant.snapshot().goals.length, 2);
    assistant.apply("exact p0");
    assert.equal(parser.stringifyTight(assistant.currentGoal.hypotheses.at(-1).proposition), "B");
    assistant.apply("exact h");
    assistant.qed();
    fs.expandMacroWithProp(1);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "B");
}

// The same inferred declaration works for a page proposition and remains
// expandable after qed's deferred assistant row is materialized.
{
    const fs = initFormalSystem(true).fs;
    for (let index = 0; index < 5; index++) fs.addHypothese(parser.parse("A=A"));
    fs.addHypothese(parser.parse("Vx:Vy:(x=y)"));
    const assistant = new InferenceProofAssistant(fs, "A=B");
    assistant.apply("have hab := p5 A B");
    assistant.apply("exact hab");
    const result = assistant.qed();
    assert.equal(result.committed, true);
    assert.equal(fs.propositions.length, 7);
    fs.expandMacroWithProp(6);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "A=B");
}

// Lean-style have can consume implication premises from the local context.
// Each proof argument is materialized as an `mp` step, so a curried
// proposition such as p0 : $0 > ($1 > $2) can be applied as `p0 b a`.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "($0>($1>$2))>($1>($0>$2))");
    assistant.apply("intro p0");
    assistant.apply("intro a");
    assistant.apply("intro b");
    assistant.apply("have h := p0 b a");
    assert.equal(parser.stringifyTight(assistant.currentGoal.hypotheses.at(-1).proposition), "$2");
    assistant.apply("exact h");
    assert.equal(assistant.snapshot().complete, true);
    const result = assistant.qed();
    assert.equal(result.committed, true);
    fs.expandMacroWithProp(fs.propositions.length - 1);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "($0>($1>$2))>($1>($0>$2))");
}

// Applications may mix universal specialization and implication elimination
// across successive local facts.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "(Vx:(A>(x=x)))>(A>(B=B))");
    assistant.apply("intro p0");
    assistant.apply("intro hA");
    assistant.apply("have hAB := p0 B");
    assistant.apply("have hB := hAB hA");
    assert.equal(parser.stringifyTight(assistant.currentGoal.hypotheses.at(-1).proposition), "B=B");
    assistant.apply("exact hB");
    assert.equal(assistant.snapshot().complete, true);
    assistant.qed();
}

// Page propositions used as implication arguments are included in the lazy
// payload and all pN references are remapped during deferred replay.
{
    const fs = initFormalSystem(true).fs;
    fs.addHypothese(parser.parse("A>B"));
    fs.addHypothese(parser.parse("A"));
    const assistant = new InferenceProofAssistant(fs, "B");
    assistant.apply("have h := p0 p1");
    assistant.apply("exact h");
    assistant.qed();
    fs.expandMacroWithProp(2);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "B");
}

console.log("inference proof-assistant Lean have regression passed");
