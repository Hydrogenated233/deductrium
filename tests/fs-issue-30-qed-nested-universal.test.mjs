import assert from "node:assert/strict";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { ASTParser } from "../js/fs/astparser.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();

// GitHub issue #30: a no-premise proof with nested universal intros reaches
// no open goals, but named qed failed while replay materialized the graph.
const fs = initFormalSystem(true).fs;
// Small stand-ins for the user-recorded arithmetic facts from the original
// save. Their shapes are enough to exercise the same nested `have`/specialize
// and universal-lifting path without depending on a large save file.
fs.addDeduction(
    "xAddNat",
    parser.parse("⊢Va:Vb:(a@N>(b@N>((a+b)@N)))"),
    "test fixture"
);
fs.addDeduction(
    "succCong",
    parser.parse("⊢Vx:Vy:(x=y>S(x)=S(y))"),
    "test fixture"
);
const target = "Va:Vb:Vc:(a@N>(b@N>(c@N>(((a+b)+c)=(a+(b+c))))))";
const assistant = new InferenceProofAssistant(fs, target);

const commands = [
    "intros a b c ha hb hc",
    "have hab := xAddNat",
    "specialize hab a",
    "specialize hab b",
    "specialize hab ha",
    "specialize hab hb",
    "have hInd : Vx:(x@N>(((a+b)+x)=(a+(b+x))))",
    "have induction := apn5 (((a+b)+z)=(a+(b+z))) z",
    "apply induction",
    "have hl0 := d+1 (a+b)",
    "specialize hl0 hab",
    "have hb0 := d+1 b",
    "specialize hb0 hb",
    "rw [hl0,hb0]",
    "rfl",
    "intros z hz ih",
    "have hl := d+2 (a+b) z",
    "specialize hl hab",
    "specialize hl hz",
    "have hbz := d+2 b z",
    "specialize hbz hb",
    "specialize hbz hz",
    "have hbzn := xAddNat",
    "specialize hbzn b",
    "specialize hbzn z",
    "specialize hbzn hb",
    "specialize hbzn hz",
    "have hr := d+2 a (b+z)",
    "specialize hr ha",
    "specialize hr hbzn",
    "have hi := succCong",
    "specialize hi ((a+b)+z)",
    "specialize hi (a+(b+z))",
    "specialize hi ih",
    "rw [hl,hbz,hr]",
    "exact hi",
    "specialize hInd c",
    "specialize hInd hc",
    "exact hInd"
];

for (const command of commands) assistant.apply(command);
assert.equal(assistant.snapshot().complete, true);
const result = assistant.qed("issue30NestedUniversal");
assert.equal(result.committed, true);
assert.deepEqual(fs.deductions.issue30NestedUniversal.conditions, []);
const materialized = fs.materializeDeferredDeduction("issue30NestedUniversal");
assert.equal(parser.stringifyTight(materialized.conclusion), parser.stringifyTight(parser.parse(target)));
assert.ok(
    materialized.steps.some(step => step.deductionIdx !== "a4" && step.deductionIdx.endsWith("a4")),
    "nested universal materialization must retain the capture-safe fallback for prefixed a4 rules"
);

console.log("GitHub issue #30 nested universal qed regression passed");
