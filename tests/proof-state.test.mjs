import assert from "node:assert/strict";
import { clearProofState, renderProofState } from "../js/proof-state.js";

class FakeText {
    constructor(text) { this._text = String(text); this.parentElement = null; }
    get textContent() { return this._text; }
    set textContent(value) { this._text = String(value ?? ""); }
}

class FakeElement extends EventTarget {
    constructor(tagName = "div") {
        super();
        this.tagName = tagName.toUpperCase();
        this.children = [];
        this.parentElement = null;
        this.attributes = new Map();
        this.className = "";
        this.style = { setProperty() {} };
        this.open = false;
        this.checked = false;
        this.type = "";
        this._text = "";
        this.classList = {
            add: (...names) => {
                const current = new Set(this.className.split(/\s+/u).filter(Boolean));
                names.forEach(name => current.add(name));
                this.className = [...current].join(" ");
            },
            remove: (...names) => {
                const remove = new Set(names);
                this.className = this.className.split(/\s+/u).filter(name => name && !remove.has(name)).join(" ");
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
    contains(node) {
        if (node === this) return true;
        return this.children.some(child => child?.contains?.(node));
    }
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

class FakeMutationObserver {
    static instances = [];
    constructor(callback) {
        this.callback = callback;
        this.active = false;
        this.target = null;
        FakeMutationObserver.instances.push(this);
    }
    observe(target) { this.target = target; this.active = true; }
    disconnect() { this.active = false; }
    fire() { if (this.active) this.callback([]); }
}

const previousDocument = globalThis.document;
const previousMutationObserver = globalThis.MutationObserver;
globalThis.document = {
    createElement: tag => new FakeElement(tag),
    createTextNode: text => new FakeText(text)
};
globalThis.MutationObserver = FakeMutationObserver;

const text = value => {
    const element = new FakeElement("span");
    element.textContent = value;
    return element;
};
const find = (root, className) => root.querySelector(`.${className}`);
const all = (root, className) => root.querySelectorAll(`.${className}`);
const inputFor = (root, setting) => find(root, `proof-setting-${setting}`).children[0];
const goals = (root) => all(root, "proof-goal");

try {
    const host = new FakeElement();
    const error = new FakeElement();
    error.setAttribute("id", "existing-error");
    const options = {
        scope: "proof-state-test-scope",
        contextKey: "proof-a",
        goals: [
            { id: "goal-1", name: "first", hypotheses: [
                { name: "A", isType: true, content: () => text("Type") },
                { name: "h", content: () => text("A") }
            ], target: () => text("A") },
            { id: "goal-2", hypotheses: [], target: () => text("B") }
        ],
        expected: () => text("A -> A"),
        error,
        completedText: "Proof complete"
    };
    renderProofState(host, options);

    const root = find(host, "proof-state-root");
    assert.ok(root, "Tactic state must use a native details root");
    assert.equal(find(root, "proof-state-title").textContent, "Tactic state");
    assert.equal(find(root, "proof-goal-count").textContent, "2 goals");
    assert.deepEqual(goals(host).map(goal => goal.getAttribute("data-proof-goal-id")), ["goal-1", "goal-2"]);
    assert.ok(goals(host)[0].classList.contains("proof-goal-current"));
    assert.ok(goals(host)[1].classList.contains("proof-goal-secondary"));
    assert.equal(find(host, "proof-case-label").textContent, "case");
    assert.equal(find(host, "proof-target-turnstile").textContent, "⊢");
    assert.equal(find(host, "proof-goal-name").textContent, "first");
    assert.equal(find(host, "proof-local-name").textContent, "A");
    assert.ok(find(host, "proof-expected-type"));
    assert.ok(find(host, "proof-messages"));
    assert.equal(find(host, "proof-messages").querySelector(".proof-messages-content").children[0], error,
        "the existing error element must move into Messages without replacement");
    assert.equal(error.getAttribute("id"), "existing-error");
    assert.equal(find(host, "proof-message-count").textContent, "(0)");

    const observer = FakeMutationObserver.instances.at(-1);
    error.textContent = "type mismatch";
    observer.fire();
    assert.equal(find(host, "proof-message-count").textContent, "(1)");
    error.textContent = "";
    observer.fire();
    assert.equal(find(host, "proof-message-count").textContent, "(0)");

    root.open = false;
    root.removeAttribute("open");
    goals(host)[0].open = false;
    goals(host)[0].removeAttribute("open");
    find(host, "proof-expected-type").open = false;
    find(host, "proof-expected-type").removeAttribute("open");
    find(host, "proof-messages").open = false;
    find(host, "proof-messages").removeAttribute("open");
    find(host, "proof-state-settings").open = true;
    find(host, "proof-state-settings").setAttribute("open", "");
    const oldObserver = observer;
    renderProofState(host, options);
    assert.equal(find(host, "proof-state-root").open, false, "root fold survives rerender");
    assert.equal(goals(host)[0].open, false, "goal fold survives rerender");
    assert.equal(find(host, "proof-expected-type").open, false, "Expected type fold survives rerender");
    assert.equal(find(host, "proof-messages").open, false, "Messages fold survives rerender");
    assert.equal(find(host, "proof-state-settings").open, true, "settings fold survives rerender");
    assert.equal(find(host, "proof-messages").querySelector(".proof-messages-content").children[0], error);
    assert.equal(oldObserver.active, false, "rerender must disconnect the old error observer");

    const currentCount = find(host, "proof-message-count");
    error.textContent = "stale observer check";
    oldObserver.fire();
    assert.equal(currentCount.textContent, "(0)", "the old observer must not update detached message state");
    const newObserver = FakeMutationObserver.instances.at(-1);
    newObserver.fire();
    assert.equal(find(host, "proof-message-count").textContent, "(1)");

    const settingsHost = new FakeElement();
    renderProofState(settingsHost, {
        scope: options.scope,
        contextKey: "settings-proof",
        goals: options.goals
    });
    inputFor(host, "targetFirst").checked = true;
    inputFor(host, "targetFirst").dispatchEvent(new Event("change"));
    renderProofState(settingsHost, {
        scope: options.scope,
        contextKey: "settings-proof",
        goals: options.goals
    });
    assert.equal(inputFor(settingsHost, "targetFirst").checked, true,
        "settings must sync from the first host to the second host on rerender");
    inputFor(settingsHost, "targetFirst").checked = false;
    inputFor(settingsHost, "targetFirst").dispatchEvent(new Event("change"));
    renderProofState(host, options);
    assert.equal(inputFor(host, "targetFirst").checked, false,
        "settings must sync back to the first host on rerender");

    const contextHost = new FakeElement();
    renderProofState(contextHost, { ...options, scope: "context-isolation", contextKey: "first" });
    find(contextHost, "proof-goal").open = false;
    find(contextHost, "proof-goal").removeAttribute("open");
    renderProofState(contextHost, { ...options, scope: "context-isolation", contextKey: "second" });
    assert.equal(find(contextHost, "proof-goal").open, true,
        "changing contextKey must not reuse the previous proof goal fold");

    const completeHost = new FakeElement();
    renderProofState(completeHost, {
        scope: "complete-proof-state",
        goals: [],
        completedText: "Proof complete"
    });
    assert.equal(find(completeHost, "proof-state-completed").textContent, "Proof complete");
    assert.equal(find(completeHost, "proof-goal-count").textContent, "0 goals");

    const beforeClearObserver = FakeMutationObserver.instances.at(-1);
    clearProofState(contextHost);
    assert.deepEqual(contextHost.children, [error], "clearing keeps the diagnostic node attached");
    assert.equal(beforeClearObserver.active, false, "clearing disconnects diagnostics observation");
    clearProofState(contextHost);
    assert.deepEqual(contextHost.children, [error], "repeated clearing must keep the caller's error node");
    renderProofState(contextHost, { ...options, scope: "context-isolation", contextKey: "second" });
    assert.equal(find(contextHost, "proof-goal").open, true, "a cleared proof starts with expanded goals");
    assert.equal(find(contextHost, "proof-messages").contains(error), true);
    clearProofState(completeHost);
    assert.deepEqual(completeHost.children, [], "clearing without an error node empties the host");
} finally {
    if (previousDocument === undefined) delete globalThis.document;
    else globalThis.document = previousDocument;
    if (previousMutationObserver === undefined) delete globalThis.MutationObserver;
    else globalThis.MutationObserver = previousMutationObserver;
}

console.log("shared proof-state DOM regression passed");
