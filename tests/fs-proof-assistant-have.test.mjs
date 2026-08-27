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

console.log("inference proof-assistant Lean have regression passed");
