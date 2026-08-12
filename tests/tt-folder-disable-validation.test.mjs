import assert from "node:assert/strict";

import { TTGui } from "../js/tt/gui.js";

const makeNode = tagName => {
    const classes = new Set();
    const listeners = new Map();
    const node = {
        tagName: tagName.toUpperCase(),
        children: [],
        parentElement: null,
        dataset: {},
        className: "",
        innerText: "",
        title: "",
        type: "",
        value: "",
        isConnected: true,
        style: { setProperty() { } },
        classList: {
            add(...names) { names.forEach(name => classes.add(name)); },
            remove(...names) { names.forEach(name => classes.delete(name)); },
            toggle(name, enabled) {
                if (enabled === undefined) enabled = !classes.has(name);
                if (enabled) classes.add(name);
                else classes.delete(name);
            },
            contains(name) { return classes.has(name); }
        },
        appendChild(child) {
            child.parentElement = node;
            node.children.push(child);
            return child;
        },
        removeChild(child) {
            const index = node.children.indexOf(child);
            if (index >= 0) node.children.splice(index, 1);
            child.parentElement = null;
            return child;
        },
        addEventListener(type, listener) {
            listeners.set(type, listener);
        },
        dispatch(type) {
            listeners.get(type)?.({ type, target: node });
        },
        setAttribute(name, value) {
            node[name] = value;
        },
        focus() { },
        remove() {
            node.isConnected = false;
        }
    };
    Object.defineProperty(node, "firstChild", {
        get() { return node.children[0] ?? null; }
    });
    return node;
};

const previousDocument = globalThis.document;
const previousFocusEvent = globalThis.FocusEvent;
const documentMock = {
    createElement: makeNode,
    createTextNode(text) { return { textContent: text, parentElement: null }; },
    getElementById() { return makeNode("div"); }
};
globalThis.document = documentMock;
globalThis.FocusEvent = class FocusEvent { };

try {
    const folderGui = Object.create(TTGui.prototype);
    folderGui.theoremItems = [];
    folderGui.theoremItemSequence = 0;
    folderGui.restoringTheoremItems = false;
    folderGui.theoremDragger = { attachIdxListener() { } };
    folderGui.definitionRevision = 0;
    folderGui.theoremStructureRevision = 0;
    folderGui.gatePreviewStructureRevision = 0;
    folderGui.renderTheoremStructure = () => { };
    folderGui.onStateChange = () => { };
    const validationStarts = [];
    folderGui.revalidateTheorems = index => validationStarts.push(index);

    const folder = folderGui.addTheoremFolder("Top", {
        id: "folder-top",
        length: 0,
        open: true,
        disabled: false
    }, true);
    folderGui.theoremItems.push({
        kind: "theorem",
        id: "outside",
        wrapper: makeNode("div"),
        input: makeNode("input"),
        localCheckbox: { checked: false }
    });

    folder.checkbox.checked = true;
    folder.checkbox.dispatch("change");
    assert.deepEqual(validationStarts, [],
        "disabling an empty top folder must not restart every theorem");

    folder.length = 1;
    folder.checkbox.checked = false;
    folder.checkbox.dispatch("change");
    assert.deepEqual(validationStarts, [0],
        "a non-empty folder still revalidates from its first child");

    const gui = Object.create(TTGui.prototype);
    gui.theoremItems = [];
    gui.theoremItemSequence = 0;
    gui.restoringTheoremItems = false;
    gui.theoremDragger = { attachIdxListener() { } };
    gui.userDefinedConsts = [];
    gui.definitionRevision = 0;
    gui.theoremStructureRevision = 0;
    gui.gatePreviewStructureRevision = 0;
    gui.workerRequestId = 0;
    gui.gateQueryCache = { clear() { } };
    gui.coreWorker = null;
    gui.core = { state: { disableSimpleFn: false, disableSimpleEq: false } };
    gui.onStateChange = () => { };
    gui.renderTheoremStructure = () => { };
    gui.syncTheoremDomOrder = () => { };
    gui.realignUserDefinitions = function () {
        this.userDefinedConsts = this.getInhabitatArray().map(() => null);
    };
    gui.getInhabitatArray = function () {
        return this.theoremItems
            .filter(item => item.kind === "theorem")
            .map(item => item.input);
    };
    gui.getHottDefCtxt = () => 0;
    gui.invalidateTheoremTypeTags = () => { };
    gui.refreshUserConstNames = () => { };

    const input = gui.updateInhabitList();
    input.value = "kept:=true";
    input.dataset.ttDisabled = "true";
    const cachedDefinition = ["kept", { type: "var", name: "true" }, { cache: true }];
    gui.userDefinedConsts[0] = cachedDefinition;

    input.onblur({});

    assert.equal(gui.userDefinedConsts[0], cachedDefinition,
        "a disabled theorem keeps its last verified definition cache");
    assert.equal(gui.isDefinitionVisible(0, 1, null), false,
        "the retained disabled definition remains unavailable to later theorems");
    assert.deepEqual(gui.getWorkerDefinitionSlots(1, null), [null],
        "the retained disabled definition is not sent to the Worker");

    input.dataset.ttDisabled = "false";
    assert.equal(gui.isDefinitionVisible(0, 1, null), true,
        "re-enabling makes the retained record available for orderly revalidation");
} finally {
    if (previousDocument === undefined) delete globalThis.document;
    else globalThis.document = previousDocument;
    if (previousFocusEvent === undefined) delete globalThis.FocusEvent;
    else globalThis.FocusEvent = previousFocusEvent;
}

console.log("folder disable validation regression passed");
