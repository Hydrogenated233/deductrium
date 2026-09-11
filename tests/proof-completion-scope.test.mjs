import assert from "node:assert/strict";
import { TTGui } from "../js/tt/gui.js";
import { FSGui } from "../js/fs/gui.js";
import { TheoremWorkspace } from "../js/tt/theorem-workspace.js";

const workspace = new TheoremWorkspace([
    { kind: "folder", id: "outer", name: "Outer", length: 3, open: true, disabled: false },
    { kind: "theorem", id: "outerDef", value: "", local: true },
    { kind: "folder", id: "inner", name: "Inner", length: 1, open: true, disabled: false },
    { kind: "theorem", id: "innerDef", value: "", local: true },
    { kind: "theorem", id: "target", value: "", local: false },
    { kind: "theorem", id: "globalDef", value: "", local: false }
]);
let syncs = 0;
const tt = Object.assign(Object.create(TTGui.prototype), {
    mode: [], tacticBusy: false, tacticScopeFolderId: "outer",
    core: { state: { sysTypes: { True: {}, "?private": {} } } },
    assistSnapshot: { goals: [{ context: [["hyp", {}]] }] },
    userDefinedConsts: [["outerDef"], ["innerDef"], ["target"], ["globalDef"]],
    unlockedTactics: new Set(["destruct", "qed"]),
    syncTheoremWorkspaceFromDom() { syncs++; return workspace; },
    getTacticDefinitionEnd() { return 2; },
    getInhabitatArray() { return [{}, {}, {}, {}]; },
    isTheoremInputDisabled() { return false; }
});
const completion = tt.getTacticCompletionContext();
assert.deepEqual(completion.locals, ["hyp"]);
assert.deepEqual(completion.constants, ["True", "outerDef", "globalDef"]);
assert.ok(completion.commands.includes("cases"));
assert.ok(!completion.commands.includes("rw"));
assert.equal(syncs, 1, "scope is read once per completion, not once per theorem");
workspace.setFolderDisabled("outer", true);
assert.deepEqual(tt.getTacticCompletionContext().constants, ["True", "globalDef"]);
tt.tacticBusy = true;
assert.deepEqual(tt.getTacticCompletionContext().locals, []);
assert.deepEqual(tt.getTacticCompletionContext().constants, []);

const fs = Object.assign(Object.create(FSGui.prototype), {
    formalSystem: { deductions: { lemma: {}, unavailable: {} } },
    inferenceProofAssistant: {}, inferenceProofBusy: false,
    inferenceProofSnapshot: { pageId: "selected", goals: [{ hypotheses: [{ name: "h" }] }] },
    pageStore: { page(id) { assert.equal(id, "selected"); return { propositions: [{}, {}] }; } },
    deductions: ["<f>#Folder", "lemma"],
    metarules: []
});
const fsCompletion = fs.getInferenceCompletionContext();
assert.deepEqual(fsCompletion.constants, ["lemma", "p0", "p1"]);
assert.deepEqual(fsCompletion.locals, ["h"]);
assert.ok(!fsCompletion.commands.includes("tauto"));
assert.ok(fsCompletion.commands.includes("rw"));
assert.ok(fsCompletion.aliases.some(entry => entry.alias === "and"));
assert.ok(!completion.aliases.some(entry => entry.alias === "and"));
fs.inferenceProofBusy = true;
assert.deepEqual(fs.getInferenceCompletionContext().constants, []);
console.log("proof completion workspace and layer scope regression passed");
