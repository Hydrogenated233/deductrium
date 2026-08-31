import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

import {
    filterDragCandidates,
    ListDragger,
    resolveDragDestination
} from "../js/fs/itemdragger.js";
import { TheoremWorkspace } from "../js/tt/theorem-workspace.js";
import { applyWorkspaceLayout, setWorkspaceRowData } from "../js/tt/theorem-workspace-view.js";

const workspace = new TheoremWorkspace([
    { kind: "theorem", id: "before", value: "before", local: false },
    { kind: "folder", id: "folder", name: "Folder", length: 3, open: true, disabled: false },
    { kind: "theorem", id: "first", value: "first", local: false },
    { kind: "folder", id: "nested", name: "Nested", length: 1, open: true, disabled: false },
    { kind: "theorem", id: "nested-child", value: "nested-child", local: false },
    { kind: "theorem", id: "after", value: "after", local: false }
]);

assert.deepEqual(workspace.dragBlockIds("folder"), [
    "folder", "first", "nested", "nested-child"
], "dragging a folder must treat its complete subtree as one block");
assert.deepEqual(workspace.dragBlockIds("first"), ["first"]);

const dragBlock = new Set(workspace.dragBlockIds("folder"));
assert.deepEqual(
    filterDragCandidates(workspace.snapshot(), item => item.id, dragBlock).map(item => item.id),
    ["before", "after"],
    "the dragged folder and descendants must not be offered as drop candidates"
);

const ordinaryEightColumnCandidates = Array.from({ length: 16 }, (_, index) => `cell-${index}`);
const ordinaryDragger = new ListDragger({});
assert.equal(ordinaryDragger.queryDraggedNames, null,
    "legacy multi-column lists must opt in before any candidate rows are filtered");
assert.deepEqual(
    filterDragCandidates(ordinaryEightColumnCandidates, name => name, new Set()),
    ordinaryEightColumnCandidates,
    "the drag-block filter must not regroup ordinary eight-column lists"
);
const hitRows = [
    { name: "open-folder", top: 100, bottom: 128, folder: true, folderOpen: true, depth: 0 },
    { name: "declaration", top: 128, bottom: 156, depth: 1 },
    { name: "closed-folder", top: 156, bottom: 184, folder: true, folderOpen: false, depth: 0 },
    { name: "after", top: 184, bottom: 212, depth: 0 }
];
assert.deepEqual(
    resolveDragDestination(hitRows, 102),
    { destination: "after:open-folder", kind: "after" },
    "the expanded folder header is a stable first-child insertion target"
);
assert.deepEqual(
    resolveDragDestination(hitRows, 99),
    { destination: "open-folder", kind: "top" },
    "moving above the folder header remains an explicit before target"
);
assert.deepEqual(
    resolveDragDestination(hitRows, 116),
    { destination: "after:open-folder", kind: "after" },
    "the main body of a folder is an after boundary, not an implicit tail append"
);
assert.deepEqual(
    resolveDragDestination(hitRows, 130),
    { destination: "after:open-folder", kind: "after" },
    "the first-child top band must remain attached to the expanded folder"
);
assert.deepEqual(
    resolveDragDestination(hitRows, 170),
    { destination: "after-subtree:closed-folder", kind: "after" },
    "a collapsed folder only offers the sibling boundary after its hidden subtree"
);
assert.deepEqual(
    resolveDragDestination([], 500),
    { destination: " ", kind: "bottom" },
    "an empty candidate list resolves to the list-bottom sentinel"
);

const row = {
    dataset: {},
    classList: { toggles: [], toggle(name, value) { this.toggles.push([name, value]); } },
    style: { values: new Map(), setProperty(name, value) { this.values.set(name, value); } }
};
setWorkspaceRowData(row, "sandbox-row", { folder: true, folderOpen: true });
applyWorkspaceLayout([row], [{
    id: "sandbox-row",
    depth: 2,
    hidden: true,
    disabled: true,
    canBeLocal: false
}]);
assert.equal(row.dataset.dragRow, "true", "shared view marks rows for drag hit testing");
assert.equal(row.dataset.dragId, "sandbox-row");
assert.equal(row.dataset.dragFolder, "true");
assert.equal(row.dataset.dragFolderOpen, "true");
assert.equal(row.dataset.dragDepth, "2");
assert.equal(row.style.values.get("--tt-folder-depth"), "2");
assert.deepEqual(row.classList.toggles, [
    ["hide", true],
    ["tt-folder-disabled", true]
], "shared view applies the common layout state");

const nestedHitRows = [
    { name: "outer", top: 100, bottom: 128, folder: true, folderOpen: true, depth: 0 },
    { name: "inner", top: 128, bottom: 156, folder: true, folderOpen: true, depth: 1 },
    { name: "first", top: 156, bottom: 184, depth: 2 },
    { name: "second", top: 184, bottom: 212, depth: 2 },
    { name: "sibling", top: 212, bottom: 240, depth: 0 }
];
assert.deepEqual(
    resolveDragDestination(nestedHitRows, 157),
    { destination: "after:inner", kind: "after" },
    "a small movement around an inner folder's first child must stay inside"
);
assert.deepEqual(
    resolveDragDestination(nestedHitRows, 127),
    { destination: "after:outer", kind: "after" },
    "moving above an inner folder only exits that inner folder, not its parent"
);
assert.deepEqual(
    resolveDragDestination(nestedHitRows, 99),
    { destination: "outer", kind: "top" },
    "moving above the outer folder exits the complete folder scope"
);
const overlappingHitRows = [
    { name: "overlap-outer", top: 100, bottom: 200, folder: true, folderOpen: true, depth: 0 },
    { name: "overlap-inner", top: 120, bottom: 148, folder: true, folderOpen: true, depth: 1 },
    { name: "overlap-first", top: 148, bottom: 176, depth: 2 }
];
assert.deepEqual(
    resolveDragDestination(overlappingHitRows, 130),
    { destination: "after:overlap-inner", kind: "after" },
    "an overlapping outer folder must not capture a pointer over the inner title"
);

const sandboxGui = await readFile(new URL("../src/tt/sandbox-gui.ts", import.meta.url), "utf8");
assert.doesNotMatch(sandboxGui, /moveDeclarationByOffset|上移声明|下移声明/,
    "sandbox declarations must use the same drag-only ordering UI as type-layer theorems");
assert.match(sandboxGui, /refreshDisplays\(\)/,
    "sandbox rows must expose a refresh path for delayed type-layer highlighting");
assert.match(sandboxGui, /renderDeclarationDisplay\(declaration, display\)/,
    "sandbox display rendering must be reusable after the row is mounted");
assert.match(sandboxGui, /source && !source\.classList\.contains\("hide"\)/,
    "refreshing sandbox highlights must preserve an actively edited row");
assert.match(sandboxGui, /queryDraggedNames[\s\S]*dragBlockIds/,
    "sandbox drag/drop must exclude the source workspace subtree");
assert.doesNotMatch(sandboxGui, /tt-folder-toggle/,
    "sandbox folders use the title as the fold control instead of a separate button");
assert.match(sandboxGui, /title\.addEventListener\("click", toggleFolder\)/,
    "sandbox folder titles must toggle the folder state");
const foldedWorkspace = new TheoremWorkspace([
    { kind: "folder", id: "folded", name: "Folded", length: 2, open: true, disabled: false },
    { kind: "folder", id: "nested", name: "Nested", length: 1, open: true, disabled: false },
    { kind: "theorem", id: "nested-theorem", value: "nested-theorem", local: false }
]);
foldedWorkspace.setFolderOpen("folded", false);
assert.deepEqual(
    foldedWorkspace.layout().map(item => [item.id, item.hidden]),
    [["folded", false], ["nested", true], ["nested-theorem", true]],
    "folding a sandbox folder must hide its complete recursive subtree"
);

const nestedDropWorkspace = new TheoremWorkspace([
    { kind: "folder", id: "folder1", name: "Folder 1", length: 2, open: true, disabled: false },
    { kind: "folder", id: "folder3", name: "Folder 3", length: 1, open: true, disabled: false },
    { kind: "theorem", id: "tri", value: "tri", local: false },
    { kind: "folder", id: "folder2", name: "Folder 2", length: 0, open: true, disabled: false }
]);
const nestedDrop = nestedDropWorkspace.move("folder2", "after:tri");
assert.equal(nestedDrop.changed, true,
    "dropping below the last child must be a real move even when the flat row stays nearby");
assert.deepEqual(nestedDropWorkspace.snapshot().map(item => item.id), [
    "folder1", "folder3", "tri", "folder2"
]);
assert.equal(nestedDropWorkspace.folderRange("folder3")?.endIndex, 4,
    "an after-child drop must extend the containing folder subtree");
assert.equal(nestedDropWorkspace.folderScopesForItem("folder2").at(-1)?.id, "folder2",
    "a moved folder remains its own scope after an after-child drop");

const firstChildDropWorkspace = new TheoremWorkspace([
    { kind: "folder", id: "folder1", name: "Folder 1", length: 2, open: true, disabled: false },
    { kind: "folder", id: "folder2", name: "Folder 2", length: 1, open: true, disabled: false },
    { kind: "theorem", id: "child", value: "child", local: false },
    { kind: "folder", id: "folder3", name: "Folder 3", length: 0, open: true, disabled: false }
]);
assert.equal(firstChildDropWorkspace.move("folder3", "after:folder1").changed, true,
    "dropping under an expanded folder title must insert the first child");
assert.deepEqual(firstChildDropWorkspace.snapshot().map(item => item.id), [
    "folder1", "folder3", "folder2", "child"
]);
assert.equal(firstChildDropWorkspace.layout().find(item => item.id === "folder3")?.depth, 1,
    "the title-bottom boundary must nest the moved folder without appending to the tail");

const collapsedSiblingWorkspace = new TheoremWorkspace([
    { kind: "folder", id: "moving", name: "Moving", length: 0, open: true, disabled: false },
    { kind: "folder", id: "closed", name: "Closed", length: 1, open: false, disabled: false },
    { kind: "theorem", id: "hidden", value: "hidden", local: false }
]);
assert.equal(collapsedSiblingWorkspace.move("moving", "after-subtree:closed").changed, true);
assert.deepEqual(collapsedSiblingWorkspace.snapshot().map(item => item.id), [
    "closed", "hidden", "moving"
]);
assert.equal(collapsedSiblingWorkspace.layout().find(item => item.id === "moving")?.depth, 0,
    "a collapsed folder must not accept a dragged child");

const staleNestedLengths = new TheoremWorkspace([
    { kind: "folder", id: "outer", name: "Outer", length: 1, open: true, disabled: false },
    { kind: "folder", id: "inner", name: "Inner", length: 2, open: true, disabled: false },
    { kind: "theorem", id: "inner-a", value: "inner-a", local: false },
    { kind: "theorem", id: "inner-b", value: "inner-b", local: false }
]);
assert.equal(staleNestedLengths.folderRange("outer")?.endIndex, 4,
    "parent folder lengths must include nested folder descendants from old saves");
staleNestedLengths.setFolderOpen("outer", false);
assert.deepEqual(staleNestedLengths.layout().map(item => [item.id, item.hidden]), [
    ["outer", false], ["inner", true], ["inner-a", true], ["inner-b", true]
]);

const typeGui = await readFile(new URL("../src/tt/gui.ts", import.meta.url), "utf8");
assert.match(typeGui, /onTypeListUpdated\s*=\s*\(\)\s*=>/,
    "type-layer GUI must expose a notification after rebuilding highlight tables");
assert.match(typeGui, /renderSandboxAst\(ast: AST\)/,
    "sandbox AST rendering must use a neutral theorem scope");
assert.match(typeGui, /theoremDragger\.queryDraggedNames[\s\S]*dragBlockIds/,
    "type-layer drag/drop must share the same source-subtree filtering contract");
assert.match(typeGui, /createWorkspaceDragHandle[\s\S]*syncWorkspaceDomOrder[\s\S]*applyWorkspaceLayout/,
    "type-layer rows must use the same workspace view helpers as the sandbox");
const gameSource = await readFile(new URL("../src/game.ts", import.meta.url), "utf8");
assert.match(gameSource, /onTypeListUpdated\s*=\s*\(\)\s*=>\s*this\.sandboxGui\?\.refreshDisplays\(\)/,
    "game startup must refresh sandbox displays after type-layer tables are rebuilt");
assert.match(gameSource, /renderSandboxAst\(ast\)/,
    "sandbox rows must render through the neutral type-layer AST entry point");

const guiCss = await readFile(new URL("../gui.css", import.meta.url), "utf8");
const indexHtml = await readFile(new URL("../index.html", import.meta.url), "utf8");
assert.match(indexHtml, /<details class="sandbox-help">[\s\S]*如何添加公理类型/,
    "sandbox must include a collapsible axiom-type guide at the bottom");
assert.match(indexHtml, /inductive tri : U[\s\S]*ind_tri/,
    "sandbox guide must document the stage-2 ordinary-inductive example");
assert.match(indexHtml, /iota[\s\S]*ind_tri C cnt c0t cpt nt[\s\S]*cnt/,
    "sandbox guide must explain generated constructor computation rules");
assert.match(indexHtml, /不能[\s\S]*直接注册任意[\s\S]*计算规则/,
    "sandbox guide must make unchecked custom computation rules explicit");
const sandboxRowDisplay = guiCss.indexOf(".sandbox-declaration-row {");
const sandboxHiddenRowDisplay = guiCss.indexOf(".sandbox-declaration-row.hide {");
assert.ok(sandboxRowDisplay >= 0, "sandbox declaration rows must define their layout");
assert.ok(sandboxHiddenRowDisplay > sandboxRowDisplay,
    "the collapsed-row display override must follow the flex row rule");
assert.match(guiCss.slice(sandboxHiddenRowDisplay, sandboxHiddenRowDisplay + 180),
    /display:\s*none\s*;/,
    "collapsed sandbox declarations must be removed from layout and hit testing");
assert.match(guiCss, /\.dragging-inside\s*\{[\s\S]*?border-bottom:\s*2px solid orange/,
    "dropping into an expanded folder should reuse the normal insertion-line marker");
assert.doesNotMatch(guiCss, /\.dragging-inside\s*\{[\s\S]*?box-shadow:/,
    "folder nesting should not introduce a second visual drag state");

console.log("sandbox drag ordering regression passed");
