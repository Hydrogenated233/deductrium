import assert from "node:assert/strict";

import { TTGui } from "../js/tt/gui.js";
import { TTCoreSession } from "../js/tt/core-session.js";

// TTGui's scope calculation is presentation-independent.  Build only the
// theorem/folder records it consumes so this regression stays runnable in the
// Node test suite without a DOM implementation.
const variable = name => ({
    type: "var",
    name,
    nodes: undefined,
    checked: null,
    err: null,
    bondVarId: null
});

const input = name => ({ value: name, dataset: {}, parentElement: null });
const theorem = (id, value, local) => {
    const inputElement = input(value);
    return {
        kind: "theorem",
        id,
        wrapper: {},
        input: inputElement,
        localCheckbox: { checked: local }
    };
};
const folder = (id, name, length) => ({
    kind: "folder",
    id,
    name,
    length,
    open: true,
    disabled: false,
    wrapper: {},
    title: {},
    checkbox: { checked: false }
});

// Layout (folder lengths count all following descendants):
//
//   global
//   A
//     f (local)
//     B
//       f (local)
//       B-target
//     A-target
//   C
//     f (local)
//     C-target
//   outside-target
//
// The repeated `f` names intentionally model the common left/right helper
// names used independently in proof folders.
const global = theorem("global", "shared:=true", false);
const folderA = folder("folder-a", "A", 5);
const aF = theorem("a-f", "f:=true", true);
const folderB = folder("folder-b", "B", 2);
const bF = theorem("b-f", "f:=false", true);
const bTarget = theorem("b-target", "b-target", false);
const aTarget = theorem("a-target", "a-target", false);
const folderC = folder("folder-c", "C", 2);
const cF = theorem("c-f", "f:=c-local", true);
const cTarget = theorem("c-target", "c-target", false);
const outsideTarget = theorem("outside-target", "outside-target", false);

const items = [global, folderA, aF, folderB, bF, bTarget, aTarget, folderC, cF, cTarget, outsideTarget];
const inputs = items.filter(item => item.kind === "theorem").map(item => item.input);
const cache = scope => ({ scope });

const gui = Object.create(TTGui.prototype);
gui.theoremItems = items;
gui.userDefinedConsts = [
    ["shared", variable("true"), cache("global")],
    ["f", variable("true"), cache("a")],
    ["f", variable("false"), cache("b")],
    null,
    null,
    ["f", variable("c-local"), cache("c")],
    null,
    null
];
gui.getInhabitatArray = () => inputs;
gui.isTheoremInputDisabled = () => false;
gui.unlockedTypes = new Set();
gui.disableSimpleFn = false;
gui.disableSimpleEq = false;
gui.inferDisplayMode = "_";
gui.core = {
    state: { userDefs: { stale: variable("stale") }, defTypes: { stale: variable("stale") } },
    restoreDefinitionCache() { }
};

const ids = records => records.map(record => record.id);
const names = slots => slots.filter(Boolean).map(slot => slot[0]);

assert.deepEqual(ids(gui.getFolderScopeForInput(bTarget.input)), ["folder-a", "folder-b"]);
assert.deepEqual(ids(gui.getFolderScopeForInput(aTarget.input)), ["folder-a"]);
assert.deepEqual(ids(gui.getFolderScopeForInput(cTarget.input)), ["folder-c"]);
assert.equal(gui.getDefaultTacticScope(bTarget.input), "folder-b");
assert.equal(gui.getDefaultTacticScope(outsideTarget.input), null);
assert.equal(gui.getFolderPath("folder-b"), "A / B");
assert.equal(gui.isKnownTheoremName("f", 1), true,
    "the declaration name on the current theorem row remains highlighted");

// A theorem proof can only select one of its lexical ancestor folders. A
// #t-gate proof has no theorem position, so it exposes every folder and lets
// the user choose an explicit local-constant context before starting.
gui.tacticTargetInput = bTarget.input;
gui.tacticScopeFolderId = null;
assert.deepEqual(ids(gui.getTacticScopeOptions()), ["folder-a", "folder-b"]);
assert.equal(gui.getTacticDefinitionEnd(), 3);
assert.equal(gui.getTacticOutputInsertPosition(), bTarget.wrapper);
assert.equal(gui.getActiveTacticScopeId(), "folder-b",
    "an unselected scope follows the target theorem's innermost folder");

// `null` has two distinct meanings in the UI: before the user picks a
// scope, it inherits the target folder; after choosing "do not use local
// constants", it is an explicit global scope and must remain global across
// proof-assistant rerenders.
gui.tacticScopeExplicit = true;
assert.equal(gui.getActiveTacticScopeId(), null,
    "an explicitly selected global scope must not fall back to the default folder");

// Rebuilding the picker happens after each proof-assistant response.  Its
// global option must stay selected instead of being overwritten by B.
const oldDocument = globalThis.document;
const createFakeElement = () => ({
    children: [],
    value: "",
    innerText: "",
    innerHTML: "",
    appendChild(child) {
        this.children.push(child);
        return child;
    },
    classList: { toggle() { } }
});
const scopeSelect = createFakeElement();
const scopeLabel = createFakeElement();
globalThis.document = {
    getElementById(id) {
        return id === "tactic-scope" ? scopeSelect : scopeLabel;
    },
    createElement: createFakeElement
};
try {
    gui.mode = ["target"];
    gui.renderTacticScopeOptions();
    assert.equal(scopeSelect.value, "",
        "rerendering the picker preserves the explicit global option");
    assert.equal(gui.getActiveTacticScopeId(), null,
        "the rebuilt picker still configures the proof assistant globally");
} finally {
    gui.mode = null;
    if (oldDocument === undefined) delete globalThis.document;
    else globalThis.document = oldDocument;
}
gui.tacticScopeExplicit = false;

gui.tacticTargetInput = null;
gui.tacticScopeFolderId = "folder-b";
assert.deepEqual(ids(gui.getTacticScopeOptions()), ["folder-a", "folder-b", "folder-c"]);
assert.equal(gui.getTacticDefinitionEnd(), inputs.length);
assert.equal(gui.getTacticOutputInsertPosition(), undefined);
assert.equal(gui.getTacticOutputFolder(), folderB);

// Folder-level plus buttons append after the complete nested subtree, rather
// than accidentally placing the new theorem inside the final child folder.
assert.equal(gui.getFolderAppendIndex(folderA), 7);
assert.equal(gui.getFolderAppendIndex(folderB), 6);

// A target in B inherits A's local definition and then shadows it with B's
// same-named definition.  A and C must never receive each other's `f`.
const bSlots = gui.getWorkerDefinitionSlots(3, "folder-b");
assert.deepEqual(names(bSlots), ["shared", "f", "f"]);
assert.equal(bSlots[1][1].name, "true");
assert.equal(bSlots[2][1].name, "false");
assert.equal(gui.hasDefinitionNameConflict("f", 2, "folder-b"), false,
    "a child folder may shadow an ancestor's local helper");

const aSlots = gui.getWorkerDefinitionSlots(4, "folder-a");
assert.deepEqual(names(aSlots), ["shared", "f"]);
assert.equal(aSlots[1][1].name, "true");

const cSlots = gui.getWorkerDefinitionSlots(6, "folder-c");
assert.deepEqual(names(cSlots), ["shared", "f"]);
assert.equal(cSlots.filter(Boolean)[1][1].name, "c-local");
assert.equal(cSlots.some(slot => slot && slot[1].name === "false"), false);

const outsideSlots = gui.getWorkerDefinitionSlots(7, null);
assert.deepEqual(names(outsideSlots), ["shared"]);

// Definition-cache snapshots follow the exact same filter.  This is what
// prevents a Worker reconfigured for C from reviving the same-named `f` cache
// that was created while working in A or B.
const cachedScopes = config => config.userDefinitionCaches.map(([name, snapshot]) => [name, snapshot.scope]);
assert.deepEqual(cachedScopes(gui.getWorkerConfig(3, "folder-b")), [
    ["shared", "global"],
    ["f", "a"],
    ["f", "b"]
]);
assert.deepEqual(cachedScopes(gui.getWorkerConfig(6, "folder-c")), [
    ["shared", "global"],
    ["f", "c"]
]);

// The main-thread context uses the same visibility predicate as Worker slots;
// stale definitions from an earlier scope must be removed before rebuilding.
gui.getHottDefCtxt(4, "folder-a");
assert.deepEqual(Object.keys(gui.core.state.userDefs), ["shared", "f"]);
assert.equal(gui.core.state.userDefs.f.name, "true");

gui.getHottDefCtxt(6, "folder-c");
assert.deepEqual(Object.keys(gui.core.state.userDefs), ["shared", "f"]);
assert.equal(gui.core.state.userDefs.f.name, "c-local");
assert.equal(gui.core.state.userDefs.stale, undefined);

// Save data must preserve the checkbox while remaining backward-compatible
// with records that omit the optional field (handled by restore as false).
const serialized = gui.serializeTheoremItems();
assert.equal(serialized.find(item => item.kind === "theorem" && item.value === "f:=c-local").local, true);
assert.equal(serialized.find(item => item.kind === "theorem" && item.value === "b-target").local, false);

// Persistent Worker sessions retain slots by source position. Truncating a
// child definition with the same name must restore its parent definition.
const session = new TTCoreSession();
session.configure({ unlockedTypes: [] }, [
    ["f", variable("parent")],
    ["f", variable("child")]
]);
assert.equal(session.engine.core.state.userDefs.f.name, "child");
session.truncate(1);
assert.equal(session.engine.core.state.userDefs.f.name, "parent");

console.log("local theorem constant scope regression passed");
