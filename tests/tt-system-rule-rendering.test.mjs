import assert from "node:assert/strict";

import { TTGui } from "../js/tt/gui.js";

const makeNode = tagName => {
    const node = {
        tagName: tagName.toUpperCase(),
        children: [],
        className: "",
        innerText: "",
        style: {},
        classList: {
            add() { },
            remove() { },
            toggle() { },
            contains() { return false; }
        },
        appendChild(child) {
            node.children.push(child);
            return child;
        },
        removeChild(child) {
            const index = node.children.indexOf(child);
            if (index >= 0) node.children.splice(index, 1);
            return child;
        }
    };
    Object.defineProperty(node, "lastChild", {
        get() { return node.children.at(-1) ?? null; }
    });
    return node;
};

const previousDocument = globalThis.document;
globalThis.document = {
    createElement: makeNode
};

try {
    const checkedKinds = [];
    const gui = Object.create(TTGui.prototype);
    gui.typeList = makeNode("div");
    gui.unlockedTypes = new Set(["eq.transleftright"]);
    gui.inferDisplayMode = "_";
    gui.disableSimpleEq = false;
    gui.disableSimpleFn = false;
    gui.ast2HTML = () => makeNode("span");
    gui.core = {
        state: {
            eagerInferRel: false,
            disableSimpleEq: false,
            disableSimpleFn: false
        },
        desugar(ast) { return ast; },
        setSystemType() { },
        setSystemDefinition() { },
        clearDefinitionCache() { },
        registerSystemDefinition() { },
        checkType(ast) { checkedKinds.push(ast.type); },
        elaborateSemanticSystemTypes() { },
        syncSemanticDefinitions() { }
    };

    gui.updateTypeList(gui.unlockedTypes);

    assert.ok(checkedKinds.length > 0,
        "ordinary built-in declarations still receive display annotations");
    assert.equal(checkedKinds.includes("==="), false,
        "trusted built-in compute equations must not be synchronously revalidated while rendering");
} finally {
    if (previousDocument === undefined) delete globalThis.document;
    else globalThis.document = previousDocument;
}

console.log("system compute-rule rendering regression passed");
