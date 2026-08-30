import assert from "node:assert/strict";

import { ASTParser } from "../js/fs/astparser.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();

// `simpa using` is the Lean spelling for simplifying a goal and closing it
// with a local fact.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assistant.apply("intro h");
    assistant.apply("simpa using h");
    assert.equal(assistant.snapshot().complete, true);
}

// `cases h` destructs a conjunction using generated local names; the named
// form follows Lean's compact `cases h with ha hb` convention.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "(A&B)>A");
    assistant.apply("intro h");
    assistant.apply("cases h with ha hb");
    assert.ok(assistant.currentGoal.hypotheses.some(hypothesis => hypothesis.name === "ha"));
    assistant.apply("exact ha");
    assert.equal(assistant.snapshot().complete, true);
}

// `rcases` accepts the Unicode Lean pattern spelling as an alias.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "(A&B)>B");
    assistant.apply("intro h");
    assistant.apply("rcases h with ⟨ha,hb⟩");
    assistant.apply("exact hb");
    assert.equal(assistant.snapshot().complete, true);
}

// Existing Lean-style `rw [h1, h2]` remains sequential and supports the
// reverse arrow notation.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "(A=B)>(B=A)");
    assistant.apply("intro h");
    assistant.apply("rw [← h]");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "A=A");
}

console.log("inference proof-assistant Lean-style strategy regression passed");
