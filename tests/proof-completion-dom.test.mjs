import assert from "node:assert/strict";
import { installProofCompletion } from "../js/proof-completion.js";

// Exercise the controller's public DOM events without a browser dependency.
class Element extends EventTarget {
    children = [];
    attributes = new Map();
    style = {};
    hidden = false;
    disabled = false;
    scrollHeight = 280;
    value = "";
    selectionStart = 0;
    selectionEnd = 0;
    append(...children) { this.children.push(...children); }
    appendChild(child) { this.append(child); }
    replaceChildren() { this.children = []; }
    setAttribute(name, value) { this.attributes.set(name, value); }
    removeAttribute(name) { this.attributes.delete(name); }
    getBoundingClientRect() { return { left: 300, top: 500, bottom: 530 }; }
    setSelectionRange(start, end) { this.selectionStart = start; this.selectionEnd = end; }
    setRangeText(text, start, end) {
        this.value = this.value.slice(0, start) + text + this.value.slice(end);
        this.setSelectionRange(start + text.length, start + text.length);
    }
}

const originalDocument = globalThis.document;
const originalWindow = globalThis.window;
try {
    globalThis.document = { body: new Element(), createElement: () => new Element(), activeElement: null };
    globalThis.window = Object.assign(new EventTarget(), { innerWidth: 390, innerHeight: 600 });
    const input = new Element();
    document.activeElement = input;
    let context = { commands: ["exact", "intro", "intros"], locals: ["h", "hyp"],
        constants: [], aliases: [{ alias: "to", symbol: "→" }] };
    installProofCompletion(input, () => context, true);
    const popup = document.body.children[0];
    const type = text => {
        input.value = text;
        input.setSelectionRange(text.length, text.length);
        input.dispatchEvent(new Event("input"));
    };
    const key = (value, properties = {}) => {
        const event = new Event("keydown", { cancelable: true });
        Object.assign(event, { key: value, ...properties });
        input.dispatchEvent(event);
        return event.defaultPrevented;
    };
    let executions = 0;
    input.addEventListener("keydown", event => { if (event.key === "Enter") executions++; });
    type("intr");
    assert.equal(popup.hidden, false);
    assert.equal(popup.style.left, "22px", "popup fits a narrow viewport");
    assert.equal(popup.style.top, "256px", "popup flips above the editor when necessary");
    key("ArrowDown");
    assert.equal(key("Tab"), true);
    assert.equal(input.value, "intros");
    assert.equal(popup.hidden, true);
    type("exa");
    key("Enter");
    assert.equal(input.value, "exact");
    assert.equal(executions, 0, "accepting a suggestion does not execute a tactic");
    key("Enter");
    assert.equal(executions, 1);
    type("exact hy");
    key("Escape");
    assert.equal(input.value, "exact hy");
    assert.equal(popup.hidden, true);
    type("\\t");
    key("Tab");
    assert.equal(input.value, "→");
    type("");
    key(" ", { ctrlKey: true });
    assert.equal(popup.children.length, 3, "explicit completion works at an empty command position");
    type("exact h");
    const staleRow = popup.children[0];
    context = { ...context, locals: [] };
    staleRow.dispatchEvent(new Event("mousedown", { cancelable: true }));
    assert.equal(input.value, "exact h", "a stale mouse candidate cannot insert an out-of-scope name");
    assert.equal(popup.hidden, true);
    context = { ...context, locals: ["hyp"] };
    type("exact hy");
    input.dispatchEvent(new Event("compositionstart"));
    assert.equal(key("Tab", { isComposing: true }), false);
    assert.equal(input.value, "exact hy", "IME input is never intercepted");
    input.dispatchEvent(new Event("compositionend"));
    key("Tab");
    assert.equal(input.value, "exact hyp");
    type("  exact h\n  exact h\n");
    input.setSelectionRange(0, input.value.length);
    key("Tab", { shiftKey: true });
    assert.equal(input.value, "exact h\nexact h\n");
    assert.equal(input.selectionStart, 0);
    assert.equal(input.selectionEnd, 15);
    key("Tab");
    assert.equal(input.value, "  exact h\n  exact h\n");
    type("exact hy");
    input.dispatchEvent(new Event("blur"));
    assert.equal(popup.hidden, true);
    assert.equal(input.attributes.get("aria-expanded"), "false");
} finally {
    if (originalDocument === undefined) delete globalThis.document;
    else globalThis.document = originalDocument;
    if (originalWindow === undefined) delete globalThis.window;
    else globalThis.window = originalWindow;
}
console.log("proof completion keyboard, scope and IME regression passed");
