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
            values: new Set(),
            add(...names) { names.forEach(name => node.classList.values.add(name)); },
            remove(...names) { names.forEach(name => node.classList.values.delete(name)); },
            toggle(name, force) {
                const next = force === undefined ? !node.classList.values.has(name) : !!force;
                if (next) node.classList.values.add(name); else node.classList.values.delete(name);
                return next;
            },
            contains(name) { return node.classList.values.has(name); }
        },
        appendChild(child) {
            node.children.push(child);
            return child;
        },
        removeChild(child) {
            const index = node.children.indexOf(child);
            if (index >= 0) node.children.splice(index, 1);
            return child;
        },
        setAttribute(name, value) {
            node.attributes ??= new Map();
            node.attributes.set(name, String(value));
        },
        getAttribute(name) {
            return node.attributes?.get(name) ?? null;
        },
        addEventListener() { },
        querySelectorAll() { return []; }
    };
    Object.defineProperty(node, "childNodes", {
        get() { return node.children; }
    });
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

    // Trusted sandbox names must be registered before the first AST render;
    // otherwise the initial frame incorrectly receives the freeVar class.
    const sandboxName = "sandboxDisplayUnique";
    const renderGui = Object.create(TTGui.prototype);
    renderGui.typeList = makeNode("div");
    renderGui.sandboxAxioms = [[sandboxName, parser.parse("U")]];
    renderGui.ast2HTML = TTGui.prototype.ast2HTML;
    renderGui.getInhabitatArray = () => [];
    renderGui.getTheoremItemForInput = () => null;
    renderGui.isKnownTheoremName = () => false;
    renderGui.floatTypeDiv = makeNode("div");
    renderGui.disableSimpleEq = false;
    renderGui.displayPi = true;
    renderGui.theoremItems = [];
    renderGui.renderSandboxAxioms();
    const findNode = (node, text) => {
        if (node?.innerText === text) return node;
        for (const child of node?.children ?? []) {
            const match = findNode(child, text);
            if (match) return match;
        }
        return undefined;
    };
    const renderedName = findNode(renderGui.typeList, sandboxName);
    assert.ok(renderedName, "sandbox axiom name should be rendered");
    assert.equal(renderedName.classList.contains("constant"), true,
        "sandbox axiom name must be highlighted as a constant on first render");
    assert.equal(renderedName.classList.contains("freeVar"), false,
        "sandbox axiom name must not be highlighted as a free variable");
} finally {
    console.log = previousLog;
    if (previousDocument === undefined) delete globalThis.document;
    else globalThis.document = previousDocument;
}

console.log("deferred system-axiom display regression passed");
