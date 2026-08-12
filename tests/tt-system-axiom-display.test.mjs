import assert from "node:assert/strict";

import { TTGui } from "../js/tt/gui.js";
import { Core } from "../js/tt/core.js";
import { ASTParser } from "../js/tt/astparser.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();

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
const previousLog = console.log;
globalThis.document = {
    createElement: makeNode
};
console.log = () => { };

try {
    const rules = initTypeSystem();
    const rendered = [];
    const gui = Object.create(TTGui.prototype);
    gui.typeList = makeNode("div");
    gui.unlockedTypes = new Set(rules.map(rule => rule.id));
    gui.inferDisplayMode = "_";
    gui.disableSimpleEq = false;
    gui.disableSimpleFn = false;
    gui.core = new Core();
    gui.ast2HTML = (_idx, ast) => {
        rendered.push(ast);
        return makeNode("span");
    };

    gui.updateTypeList(gui.unlockedTypes);

    for (const ast of rendered) {
        assert.doesNotMatch(
            parser.stringify(ast),
            /\?nbe[0-9]+/,
            "the system type list must not expose solver-private inference names"
        );
    }

    const displayedTypes = new Map(rendered
        .filter(ast => ast?.type === ":" && ast.nodes?.[0]?.type === "var")
        .map(ast => [ast.nodes[0].name, ast.nodes[1]]));
    for (const name of [
        "eqvrefl",
        "LEM",
        "rec_S1",
        "trunc",
        "ind_Trunc",
        "apd_trunc"
    ]) {
        const displayedType = displayedTypes.get(name);
        assert.ok(displayedType,
            `${name} must be rendered only after its inferred system type is available`);
        const text = parser.stringify(displayedType);
        assert.notEqual(text, "_", `${name} must not use a missing-type placeholder`);
        assert.doesNotMatch(text, /\?nbe/, `${name} must not expose an internal NbE metavariable`);
    }
} finally {
    console.log = previousLog;
    if (previousDocument === undefined) delete globalThis.document;
    else globalThis.document = previousDocument;
}

console.log("deferred system-axiom display regression passed");
