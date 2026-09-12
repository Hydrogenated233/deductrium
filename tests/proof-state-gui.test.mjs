import assert from "node:assert/strict";
import { FSGui } from "../js/fs/gui.js";
import { TTGui } from "../js/tt/gui.js";

class FakeText {
    constructor(text) { this.textContent = String(text); this.parentElement = null; }
}

class FakeElement extends EventTarget {
    constructor(tag = "div") {
        super();
        this.tagName = tag.toUpperCase();
        this.children = [];
        this.parentElement = null;
        this.className = "";
        this.attributes = new Map();
        this.open = false;
        this.checked = false;
        this.type = "";
        this._text = "";
        this.classList = {
            add: (...names) => {
                const values = new Set(this.className.split(/\s+/u).filter(Boolean));
                names.forEach(name => values.add(name));
                this.className = [...values].join(" ");
            },
            contains: name => this.className.split(/\s+/u).includes(name)
        };
    }
    get textContent() { return this._text + this.children.map(child => child.textContent ?? "").join(""); }
    set textContent(value) { this.replaceChildren(); this._text = String(value ?? ""); }
    append(...items) { items.forEach(item => this.appendChild(item)); }
    appendChild(item) {
        if (item?.parentElement) item.parentElement.removeChild(item);
        this.children.push(item);
        if (item && typeof item === "object") item.parentElement = this;
        return item;
    }
    removeChild(item) {
        const index = this.children.indexOf(item);
        if (index >= 0) this.children.splice(index, 1);
        if (item?.parentElement === this) item.parentElement = null;
        return item;
    }
    replaceChildren(...items) {
        for (const child of this.children) if (child?.parentElement === this) child.parentElement = null;
        this.children = [];
        this._text = "";
        this.append(...items);
    }
    setAttribute(name, value) { this.attributes.set(name, String(value)); }
    getAttribute(name) { return this.attributes.get(name) ?? null; }
    hasAttribute(name) { return this.attributes.has(name); }
    removeAttribute(name) { this.attributes.delete(name); }
    contains(node) { return node === this || this.children.some(child => child?.contains?.(node)); }
    querySelector(selector) { return this.querySelectorAll(selector)[0] ?? null; }
    querySelectorAll(selector) {
        const result = [];
        const className = selector.startsWith(".") ? selector.slice(1) : null;
        const visit = element => {
            for (const child of element.children ?? []) {
                if (className && child.classList?.contains(className)) result.push(child);
                visit(child);
            }
        };
        visit(this);
        return result;
    }
}

const previousDocument = globalThis.document;
globalThis.document = {
    elements: new Map(),
    createElement: tag => new FakeElement(tag),
    createTextNode: text => new FakeText(text),
    getElementById(id) { return this.elements.get(id) ?? null; }
};

const register = (id, element = new FakeElement()) => {
    element.setAttribute("id", id);
    document.elements.set(id, element);
    return element;
};
const text = value => new FakeText(value);
const goalIds = host => host.querySelectorAll(".proof-goal").map(goal => goal.getAttribute("data-proof-goal-id"));

try {
    const ttHost = register("tactic-state");
    const ttError = register("tactic-errmsg");
    const tt = Object.create(TTGui.prototype);
    tt.tacticTextMode = false;
    tt.proofSessions = { activeId: "tt-session" };
    tt.getInhabitatArray = () => [];
    tt.ast2HTML = (_index, ast) => text(`tt:${ast.name ?? ast.type}`);
    tt.updateTacticStateDisplay({ theorem: { type: "var", name: "Theorem" }, goals: [
        { id: "goal-1", holeName: "?goal-1", context: [["n", { type: "var", name: "Nat" }]], type: { type: "var", name: "P" } },
        { id: "goal-2", holeName: "?goal-2", context: [], type: { type: "var", name: "Q" } }
    ] }, ttHost);
    assert.deepEqual(goalIds(ttHost), ["goal-1", "goal-2"]);
    assert.equal(ttHost.querySelector(".proof-goal-name"), null, "internal hole markers are not case names");
    assert.ok(ttHost.querySelectorAll(".proof-goal")[0].classList.contains("proof-goal-current"));
    assert.ok(ttHost.querySelectorAll(".proof-goal")[1].classList.contains("proof-goal-secondary"));
    assert.equal(ttHost.querySelector(".proof-target-turnstile").textContent, "⊢");
    assert.equal(ttHost.querySelector(".proof-local-name").textContent, "n");
    assert.equal(ttHost.querySelector(".proof-messages-content").children[0], ttError,
        "TTGui must pass through the existing tactic error node");
    ttHost.querySelector(".proof-goal").open = false;
    tt.updateTacticStateDisplay({ theorem: { type: "var", name: "Theorem" }, goals: [
        { id: "goal-2", holeName: "?goal-1", context: [], type: { type: "var", name: "Q" } }
    ] }, ttHost);
    assert.equal(ttHost.querySelector(".proof-goal").open, true, "a promoted goal keeps its own fold state");

    const fsHost = register("fs-proof-state");
    const fsError = register("fs-proof-errmsg");
    const fs = Object.create(FSGui.prototype);
    fs.ast2HTML = (_index, ast) => text(`fs:${ast.name ?? ast.type}`);
    fs.renderInferenceProofState({
        pageId: "page-1",
        theorem: { type: "var", name: "Theorem" },
        goals: [
            { id: 17, target: { type: "var", name: "P" }, hypotheses: [] },
            { id: 23, target: { type: "var", name: "Q" }, hypotheses: [
                { name: "h", kind: "page", proposition: { type: "var", name: "P" } }
            ] }
        ],
        history: [],
        complete: false
    }, fsHost, fsError);
    assert.deepEqual(goalIds(fsHost), ["17", "23"]);
    assert.equal(fsHost.querySelector(".proof-messages-content").children[0], fsError,
        "FSGui must pass through the existing inference error node");
    assert.equal(fsHost.querySelector(".proof-expected-content").textContent, "fs:Theorem");
    assert.equal(fsHost.querySelectorAll(".proof-goal")[0].children[1].className, "proof-goal-body",
        "both GUI adapters must use the shared goal body structure");
} finally {
    if (previousDocument === undefined) delete globalThis.document;
    else globalThis.document = previousDocument;
}

console.log("proof-state TTGui/FSGui adapter regression passed");
