import assert from "node:assert/strict";
import { initFormalSystem } from "../js/fs/initial.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { ASTParser } from "../js/fs/astparser.js";

const parser = new ASTParser();
const fs = initFormalSystem(true).fs;
const seed = new InferenceProofAssistant(fs, "Vx:x=x", { allowMcpt: false });
seed.apply("intro x");
seed.apply("rfl");
seed.qed("identity");

// Search must not replay a checked closed source just to form c/u candidates
// (or to reject >). Count structural work, not machine-dependent milliseconds.
let replays = 0;
const original = InferenceProofAssistant.prototype.materializeForDeferred;
InferenceProofAssistant.prototype.materializeForDeferred = function (...args) {
    replays++;
    return original.apply(this, args);
};
try {
    const assistant = new InferenceProofAssistant(fs,
        "Va:Vb:(a=a>b=b>a=a)", { allowMcpt: false });
    for (const command of ["intros a b ha hb", "have h := identity",
        "specialize h a", "exact h"]) assistant.apply(command);
    assert.equal(assistant.snapshot().complete, true);
    assistant.qed("outer");
    assert.equal(replays, 1, "validate the current proof once, without replaying checked source macros");
    assert.equal(fs.deductions.identity.steps, undefined, "source proof stays deferred");
} finally {
    InferenceProofAssistant.prototype.materializeForDeferred = original;
}

fs.deduct({ deductionIdx: "outer", conditionIdxs: [], replaceValues: [] });
fs.expandMacroWithProp(0);
assert.equal(parser.stringifyTight(fs.propositions.at(-1).value),
    parser.stringifyTight(parser.parse("Va:Vb:(a=a>b=b>a=a)")));
assert.ok(fs.propositions.every(row => row.from));

console.log("GitHub issue #46 closed-source generalization regression passed");
