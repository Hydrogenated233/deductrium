import assert from "node:assert/strict";

import { TTGui } from "../js/tt/gui.js";

function makeNode(tagName) {
    const node = {
        tagName: tagName.toUpperCase(),
        children: [],
        parentElement: null,
        nextSibling: null,
        dataset: {},
        value: "",
        checked: false,
        disabled: false,
        innerText: "",
        title: "",
        type: "",
        rows: 0,
        style: { setProperty() { }, height: "" },
        classList: {
            values: new Set(),
            add(...names) { for (const name of names) this.values.add(name); },
            remove(...names) { for (const name of names) this.values.delete(name); },
            toggle(name, enabled) {
                if (enabled) this.values.add(name);
                else this.values.delete(name);
                return enabled;
            },
            contains(name) { return this.values.has(name); }
        },
        appendChild(child) {
            if (child.parentElement) child.parentElement.removeChild(child);
            child.parentElement = node;
            node.children.push(child);
            node.refreshSiblings();
            return child;
        },
        insertBefore(child, before) {
            if (child.parentElement) child.parentElement.removeChild(child);
            child.parentElement = node;
            const index = before ? node.children.indexOf(before) : -1;
            if (index < 0) node.children.push(child);
            else node.children.splice(index, 0, child);
            node.refreshSiblings();
            return child;
        },
        removeChild(child) {
            const index = node.children.indexOf(child);
            if (index >= 0) node.children.splice(index, 1);
            child.parentElement = null;
            child.nextSibling = null;
            node.refreshSiblings();
        },
        refreshSiblings() {
            for (let index = 0; index < node.children.length; index++) {
                node.children[index].nextSibling = node.children[index + 1] ?? null;
            }
        },
        remove() {
            if (node.parentElement) node.parentElement.removeChild(node);
        },
        setAttribute(name, value) {
            node[name] = String(value);
        },
        addEventListener() { }
    };
    return node;
}

const previousDocument = globalThis.document;
const inhabitList = makeNode("div");
const addButton = makeNode("button");
inhabitList.appendChild(addButton);
globalThis.document = {
    createElement: makeNode,
    createTextNode(text) { return { textContent: text, parentElement: null }; },
    getElementById(id) {
        if (id === "add-btn") return addButton;
        return null;
    }
};

try {
    const gui = Object.create(TTGui.prototype);
    gui.inhabitList = inhabitList;
    gui.theoremItems = [];
    gui.theoremItemSequence = 0;
    gui.theoremInputsCacheRevision = -1;
    gui.theoremStructureRevision = 0;
    gui.definitionRevision = 0;
    gui.gatePreviewStructureRevision = 0;
    gui.restoringTheoremItems = false;
    gui.skipRendering = true;
    gui.theoremDragger = { attachIdxListener() { } };
    gui.userDefinedConsts = [];
    gui.core = { state: { defTypes: {} } };
    gui.gateQueryCache = { clear() { } };
    gui.invalidateHottDefCtxt = () => { };
    gui.refreshUserConstNames = () => { };
    gui.onStateChange = () => { };
    gui.getInhabitatArray = function () {
        return this.theoremItems
            .filter(item => item.kind === "theorem")
            .map(item => item.input);
    };
    gui.invalidateTheoremChecks = () => { };

    gui.restoreTheoremItems([
        { kind: "folder", id: "outer", name: "Outer", length: 3, open: false, disabled: true },
        { kind: "theorem", value: "outer-local", local: true },
        { kind: "folder", id: "inner", name: "Inner", length: 1, open: false, disabled: false },
        { kind: "theorem", value: "inner-local", local: true },
        { kind: "theorem", value: "outside", local: false }
    ]);

    const serialized = gui.serializeTheoremItems();
    assert.deepEqual(serialized.map(item => item.kind === "folder"
        ? [item.kind, item.id, item.length, item.open, item.disabled]
        : [item.kind, item.value, item.local]), [
        ["folder", "outer", 3, false, true],
        ["theorem", "outer-local", true],
        ["folder", "inner", 1, false, false],
        ["theorem", "inner-local", true],
        ["theorem", "outside", false]
    ]);

    const workspace = gui.theoremWorkspace;
    assert.deepEqual(workspace.folderRange("outer"), {
        startIndex: 0,
        endIndex: 4,
        startTheoremIndex: 0,
        endTheoremIndex: 2
    });
    assert.equal(workspace.folderRange("inner").endIndex, 4);
    assert.deepEqual(workspace.folderScopesForItem(
        gui.theoremItems.find(item => item.kind === "theorem" && item.input.value === "inner-local").id
    ).map(folder => folder.id), ["outer", "inner"]);

    const layout = new Map(workspace.layout().map(item => [item.id, item]));
    const outerLocal = gui.theoremItems.find(item => item.kind === "theorem" && item.input.value === "outer-local");
    const inner = gui.theoremItems.find(item => item.kind === "folder" && item.id === "inner");
    const innerLocal = gui.theoremItems.find(item => item.kind === "theorem" && item.input.value === "inner-local");
    const outside = gui.theoremItems.find(item => item.kind === "theorem" && item.input.value === "outside");
    assert.equal(layout.get(outerLocal.id).hidden, true);
    assert.equal(layout.get(outerLocal.id).disabled, true);
    assert.equal(layout.get(inner.id).hidden, true);
    assert.equal(layout.get(innerLocal.id).hidden, true);
    assert.equal(layout.get(innerLocal.id).disabled, true);
    assert.equal(layout.get(outside.id).hidden, false);
    assert.equal(layout.get(outside.id).disabled, false);

    const legacy = new (workspace.constructor)([
        { kind: "folder", id: "legacy", name: "Legacy", length: 1 },
        { kind: "theorem", value: "legacy-child" }
    ]);
    assert.deepEqual(legacy.serialize(), [
        { kind: "folder", id: "legacy", name: "Legacy", length: 1, open: true, disabled: false },
        { kind: "theorem", value: "legacy-child", local: false }
    ]);
} finally {
    if (previousDocument === undefined) delete globalThis.document;
    else globalThis.document = previousDocument;
}

console.log("save restore folder structure regression passed");
