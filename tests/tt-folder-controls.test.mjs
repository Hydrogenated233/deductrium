import assert from "node:assert/strict";

import { TTGui } from "../js/tt/gui.js";

const makeNode = tagName => {
    const node = {
        tagName: tagName.toUpperCase(),
        children: [],
        parentElement: null,
        dataset: {},
        className: "",
        innerText: "",
        title: "",
        type: "",
        style: { setProperty() { } },
        classList: {
            add() { },
            remove() { },
            toggle() { },
            contains() { return false; }
        },
        appendChild(child) {
            child.parentElement = node;
            node.children.push(child);
            return child;
        },
        addEventListener() { },
        remove() { }
    };
    return node;
};

const previousDocument = globalThis.document;
const documentMock = {
    createElement: makeNode,
    createTextNode(text) { return { textContent: text, parentElement: null }; },
    getElementById() { return null; }
};
globalThis.document = documentMock;

try {
    const gui = Object.create(TTGui.prototype);
    gui.theoremItems = [];
    gui.theoremItemSequence = 0;
    gui.restoringTheoremItems = false;
    gui.theoremDragger = { attachIdxListener() { } };
    gui.renderTheoremStructure = () => { };
    gui.onStateChange = () => { };

    const folder = gui.addTheoremFolder("A", {
        id: "folder-a",
        length: 0,
        open: true,
        disabled: false
    }, true);
    const controls = folder.wrapper.children.filter(child => child.tagName === "BUTTON");
    assert.equal(controls[0].innerText, "↕", "the drag handle remains the first folder control");
    assert.equal(controls[1].innerText, "+",
        "the add-at-folder-bottom button is immediately right of the drag handle");
} finally {
    if (previousDocument === undefined) delete globalThis.document;
    else globalThis.document = previousDocument;
}

console.log("folder theorem control placement regression passed");
