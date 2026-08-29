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

// A page that begins with hypotheses is intentionally ineligible for #p gates,
// even when a later proposition has a completed proof.
const pageStore = new InferencePageStore([
    { name: "主表", propositions: [hypothesis, completed] },
    { name: "空页", propositions: [] }
]);
const gui = Object.create(FSGui.prototype);
gui.formalSystem = {};
gui.pageStore = pageStore;
assert.equal(gui.hasPropositionForGate(parser.parse("A>B")), false);

// A hypothesis-free page with a completed proposition can open the gate.
pageStore.setPropositions([completed], "空页");
assert.equal(gui.hasPropositionForGate(parser.parse("A>B")), true,
    "a completed theorem on a hypothesis-free page opens the gate");
pageStore.setPropositions([hypothesis], "空页");
pageStore.setPropositions([hypothesis], "主表");
assert.equal(gui.hasPropositionForGate(parser.parse("A>B")), false,
    "a page containing hypotheses must not satisfy a #p gate");

console.log("#p gate matching with leading hypotheses regression passed");
