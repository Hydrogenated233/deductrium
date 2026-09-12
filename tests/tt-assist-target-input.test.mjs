import assert from "node:assert/strict";
import { TTGui } from "../js/tt/gui.js";
import { TTProofSessionStore } from "../js/tt/proof-sessions.js";

class Element extends EventTarget {
    value = "";
    innerText = "";
    disabled = false;
    focused = false;
    selectionStart = 0;
    selectionEnd = 0;
    focus() { this.focused = true; }
    setSelectionRange(start, end) { this.selectionStart = start; this.selectionEnd = end; }
}

const previousDocument = globalThis.document;
const elements = new Map();
const element = id => {
    if (!elements.has(id)) elements.set(id, new Element());
    return elements.get(id);
};
globalThis.document = { getElementById: element };

try {
    const gui = Object.create(TTGui.prototype);
    gui.tacticBusy = false;
    gui.proofSessions = new TTProofSessionStore();
    const existing = gui.proofSessions.openManual({ target: "True", history: ["exact true"] });
    const openings = [];
    gui.executeTactic = async (...args) => { openings.push(args); };
    gui.initTacticTargetInput();
    const target = element("tactic-target");
    const begin = element("tactic-target-begin");
    const error = element("tactic-target-error");
    const key = (key, properties = {}) => {
        const event = new Event("keydown", { cancelable: true });
        Object.assign(event, { key, ...properties });
        target.dispatchEvent(event);
        return event.defaultPrevented;
    };

    target.value = "   ";
    await gui.startTacticFromInput();
    assert.equal(openings.length, 0);
    assert.ok(error.innerText);
    assert.equal(gui.proofSessions.activeId, existing.id);

    target.value = "(";
    await gui.startTacticFromInput();
    assert.equal(openings.length, 0, "invalid syntax must not replace an active proof");
    assert.equal(target.value, "(", "failed startup retains the input");
    assert.deepEqual(gui.proofSessions.active.history, ["exact true"]);

    target.value = "True";
    target.dispatchEvent(new Event("input"));
    assert.equal(error.innerText, "");
    assert.equal(openings.length, 0, "typing a proposition must not start the assistant");
    key("Enter", { isComposing: true });
    key("Enter", { keyCode: 229 });
    target.dispatchEvent(new Event("compositionstart"));
    key("Enter");
    target.dispatchEvent(new Event("compositionend"));
    assert.equal(openings.length, 0, "IME confirmation must not start a proof");
    assert.equal(key("Enter"), true);
    assert.deepEqual(openings, [["True"]], "Enter starts an unbound manual proof");

    gui.tacticBusy = true;
    begin.dispatchEvent(new Event("click"));
    assert.equal(openings.length, 1, "busy sessions reject duplicate startup");
    gui.tacticBusy = false;
    target.value = " False ";
    begin.dispatchEvent(new Event("click"));
    assert.deepEqual(openings[1], ["False"], "the startup button uses only its own target input");

    target.value = "\\lambda";
    target.setSelectionRange(target.value.length, target.value.length);
    key(" ");
    assert.equal(target.value, "\u03bb", "the target input supports type-theory Unicode aliases");

    Object.assign(gui, {
        mode: ["missing_target"],
        tacticTextMode: true,
        tacticRequestId: 0,
        assistSnapshot: null,
        onStateChange() {},
        renderTacticSessionTabs() {},
        async startAssistSession() { throw new Error("Unknown target: missing_target"); }
    });
    gui.proofSessions.openManual({ target: "missing_target" });
    element("tactic-script").value = "";
    await gui.replayTacticText();
    assert.match(error.innerText, /missing_target/,
        "text-mode startup errors must be visible even before the first proof snapshot");
    assert.equal(gui.tacticBusy, false);
    assert.equal(gui.proofSessions.active.target, "missing_target");
    assert.deepEqual(gui.proofSessions.session(existing.id).history, ["exact true"]);
} finally {
    if (previousDocument === undefined) delete globalThis.document;
    else globalThis.document = previousDocument;
}

console.log("type-theory independent proof target input regression passed");
