import assert from "node:assert/strict";
import { ASTParser } from "../js/fs/astparser.js";
import { FSGui } from "../js/fs/gui.js";
import { InferencePageStore } from "../js/fs/inference-pages.js";

const parser = new ASTParser();
const target = parser.parse("(A>B)");
const hypothesis = { value: target, from: null };
const completed = {
    value: target,
    from: { deductionIdx: "proof", conditionIdxs: [], replaceValues: [] }
};

// A page may begin with hypotheses, but a later completed proposition on the
// same page must still be visible to #p gate matching.
const pageStore = new InferencePageStore([
    { name: "主表", propositions: [hypothesis, completed] },
    { name: "空页", propositions: [] }
]);
const gui = Object.create(FSGui.prototype);
gui.formalSystem = {};
gui.pageStore = pageStore;
assert.equal(gui.hasPropositionForGate(parser.parse("A>B")), true);

// Hypotheses alone are not completed proofs and must not open a gate.
pageStore.setPropositions([hypothesis], "空页");
assert.equal(gui.hasPropositionForGate(parser.parse("A>B")), true,
    "the completed theorem on 主表 remains available");
pageStore.setPropositions([hypothesis], "主表");
assert.equal(gui.hasPropositionForGate(parser.parse("A>B")), false,
    "a hypothesis-only page must not satisfy a #p gate");

console.log("#p gate matching with leading hypotheses regression passed");
