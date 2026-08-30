import assert from "node:assert/strict";

import { ASTParser } from "../js/fs/astparser.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();

// A deduction rule can transform a local hypothesis in place.  The generated
// row is then used when the same hypothesis name is referenced again.
{
    const fs = initFormalSystem(false).fs;
    fs.addDeduction("deriveB", parser.parse("A⊢B"), "test");
    const assistant = new InferenceProofAssistant(fs, "A>B");
    assistant.apply("intro h");
    const snapshot = assistant.apply("apply deriveB at h");
    assert.equal(parser.stringifyTight(snapshot.goals[0].hypotheses[0].proposition), "B");
    assistant.apply("exact h");
    assert.equal(assistant.snapshot().complete, true);
    assistant.qed();
    fs.expandMacroWithProp(fs.propositions.length - 1);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "A>B");
}

console.log("inference proof-assistant apply-at regression passed");

// `specialize h a` is the direct local-fact form of the same transformation.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "(Vx:(A>(x=x)))>(A>(B=B))");
    assistant.apply("intro h");
    assistant.apply("specialize h B");
    assert.equal(parser.stringifyTight(assistant.currentGoal.hypotheses[0].proposition), "A>(B=B)");
    assistant.apply("intro hA");
    assistant.apply("have hB := h hA");
    assistant.apply("exact hB");
    assert.equal(assistant.snapshot().complete, true);
}
