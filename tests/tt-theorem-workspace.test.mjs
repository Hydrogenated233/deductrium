import assert from "node:assert/strict";

import { TheoremWorkspace } from "../js/tt/theorem-workspace.js";

const workspace = new TheoremWorkspace([
    { kind: "folder", id: "outer", name: "Outer", length: 3, open: true, disabled: false },
    { kind: "theorem", id: "outerDef", value: "outerDef", local: true },
    { kind: "folder", id: "inner", name: "Inner", length: 1, open: true, disabled: false },
    { kind: "theorem", id: "innerDef", value: "innerDef", local: true },
    { kind: "theorem", id: "globalAfter", value: "globalAfter", local: false }
]);

assert.equal(workspace.theoremCount, 3);
assert.deepEqual(workspace.folderRange("outer"), {
    startIndex: 0,
    endIndex: 4,
    startTheoremIndex: 0,
    endTheoremIndex: 2
});
assert.equal(workspace.folderPath("inner"), "Outer / Inner");
assert.equal(workspace.folderAppendIndex("outer"), 4);

assert.equal(workspace.isTheoremInScope(0, "outer"), true);
assert.equal(workspace.isTheoremInScope(1, "inner"), true,
    "an inner folder sees a local constant from its ancestor");
assert.equal(workspace.isTheoremInScope(1, "outer"), false,
    "a parent folder must not see a child folder's local constant");
assert.equal(workspace.isTheoremVisible(0, 2, "inner"), true);
assert.equal(workspace.isTheoremVisible(2, 2, "outer"), false,
    "a definition is unavailable at or before its own ordered position");

let mutation = workspace.setFolderDisabled("outer", true);
assert.equal(mutation.revalidateFrom, 0);
assert.equal(workspace.isTheoremDisabled(0), true);
assert.equal(workspace.isTheoremInScope(1, "inner"), false);
assert.equal(workspace.isTheoremInScope(2, "inner"), true,
    "disabling a folder must not disable following global theorems");

mutation = workspace.setFolderDisabled("outer", false);
assert.equal(mutation.revalidateFrom, 0);
mutation = workspace.setFolderOpen("outer", false);
assert.equal(mutation.revalidateFrom, null,
    "folding changes drop visibility but do not invalidate theorem validation");
assert.equal(workspace.move("globalAfter", "inside:outer").changed, false,
    "a folded folder is not a valid drop target");
workspace.setFolderOpen("outer", true);

mutation = workspace.move("globalAfter", "inside:outer");
assert.equal(mutation.changed, true);
assert.equal(mutation.revalidateFrom, 2);
assert.deepEqual(workspace.snapshot().map(item => item.id), [
    "outer", "outerDef", "inner", "innerDef", "globalAfter"
], "dropping on an expanded folder inserts at its bottom");

mutation = workspace.updateTheorem("globalAfter", { value: "globalAfter2" });
assert.equal(mutation.definitionsChanged, true,
    "changing theorem text must invalidate definition consumers");
assert.equal(mutation.revalidateFrom, 2);
assert.deepEqual(workspace.snapshot().map(item => item.id), [
    "outer", "outerDef", "inner", "innerDef", "globalAfter"
]);

mutation = workspace.insertTheorem({
    kind: "theorem", id: "new", value: "newDef", local: false
}, workspace.folderAppendIndex("inner"));
assert.equal(mutation.revalidateFrom, 2);
assert.equal(workspace.removeTheorem("new").changed, true);
assert.equal(workspace.removeFolder("inner").changed, true);
assert.equal(workspace.folderPath("outer"), "Outer");

const saved = workspace.serialize();
assert.ok(saved.every(item => item.kind === "folder" || !("id" in item)),
    "the serialized shape must remain compatible with existing saves");
const restored = new TheoremWorkspace(saved);
assert.deepEqual(
    restored.serialize().map(item => item.kind === "folder"
        ? [item.kind, item.id, item.length]
        : [item.kind, item.value, item.local]),
    saved.map(item => item.kind === "folder"
        ? [item.kind, item.id, item.length]
        : [item.kind, item.value, item.local])
);

const hiddenDestination = new TheoremWorkspace([
    { kind: "folder", id: "moving", name: "Moving", length: 1, open: true, disabled: false },
    { kind: "theorem", id: "movingChild", value: "movingChild", local: false },
    { kind: "folder", id: "closed", name: "Closed", length: 1, open: false, disabled: false },
    { kind: "folder", id: "hidden", name: "Hidden", length: 0, open: true, disabled: false }
]);
assert.equal(hiddenDestination.move("moving", "hidden").changed, false,
    "a row hidden below a collapsed folder is not a valid move destination");
assert.equal(hiddenDestination.move("moving", "inside:hidden").changed, false,
    "an open folder hidden below a collapsed ancestor is not a valid drop target");
assert.deepEqual(hiddenDestination.snapshot().map(item => item.id), [
    "moving", "movingChild", "closed", "hidden"
]);

const boundaryWorkspace = new TheoremWorkspace([
    { kind: "folder", id: "folder", name: "Folder", length: 1, open: true, disabled: false },
    { kind: "theorem", id: "folderChild", value: "folderChild", local: true },
    { kind: "theorem", id: "anchor", value: "anchor", local: false },
    { kind: "theorem", id: "moved", value: "moved", local: false }
]);
const boundaryMove = boundaryWorkspace.move("moved", "anchor");
assert.equal(boundaryMove.changed, true);
assert.deepEqual(boundaryWorkspace.snapshot().map(item => item.id), [
    "folder", "folderChild", "moved", "anchor"
]);
assert.equal(boundaryWorkspace.folderRange("folder")?.endIndex, 2,
    "dropping before a sibling after a folder must not extend that folder");

const collapsedAncestorWorkspace = new TheoremWorkspace([
    { kind: "theorem", id: "source", value: "source", local: false },
    { kind: "folder", id: "closedParent", name: "Closed parent", length: 2, open: false, disabled: false },
    { kind: "folder", id: "visibleChild", name: "Visible child", length: 1, open: true, disabled: false },
    { kind: "theorem", id: "hiddenChild", value: "hiddenChild", local: false },
    { kind: "theorem", id: "after", value: "after", local: false }
]);
assert.equal(collapsedAncestorWorkspace.move("source", "visibleChild").changed, false,
    "a destination row hidden by a collapsed ancestor is invalid");
assert.equal(collapsedAncestorWorkspace.move("source", "inside:visibleChild").changed, false,
    "an open child inside a collapsed ancestor is not an insertion target");
assert.equal(collapsedAncestorWorkspace.move("source", "after").changed, true,
    "the insertion boundary after a collapsed subtree remains valid");
assert.equal(collapsedAncestorWorkspace.folderRange("closedParent")?.endIndex, 3,
    "moving after a collapsed subtree must not cross its folder range");

const largeFolderTheoremCount = 2048;
const largeFolderWorkspace = new TheoremWorkspace([
    { kind: "folder", id: "large", name: "Large", length: largeFolderTheoremCount, open: true, disabled: false },
    ...Array.from({ length: largeFolderTheoremCount }, (_, index) => ({
        kind: "theorem",
        id: `large-${index}`,
        value: `large_${index}`,
        local: false
    })),
    { kind: "folder", id: "target", name: "Target", length: 0, open: true, disabled: false }
]);
const largeFolderMove = largeFolderWorkspace.move("large", "inside:target");
assert.equal(largeFolderMove.changed, true);
assert.equal(largeFolderMove.revalidateFrom, 0);
assert.equal(largeFolderMove.revalidateTo, largeFolderTheoremCount,
    "folder-move metadata is calculated from prefix indices, not each theorem row");
assert.equal(largeFolderWorkspace.folderRange("target")?.endIndex, largeFolderTheoremCount + 2);
assert.equal(largeFolderWorkspace.folderRange("large")?.endTheoremIndex, largeFolderTheoremCount);

console.log("theorem workspace model regression passed");
