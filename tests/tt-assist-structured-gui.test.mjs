import assert from "node:assert/strict";
import { TTGui } from "../js/tt/gui.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { TTProofSessionStore } from "../js/tt/proof-sessions.js";
import { initTypeSystem } from "../js/tt/initial.js";

const engine = new TTAssistEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_", timeout: 30_000, language: "zh"
});
const options = {
    disableMultipleApply: false, disableDestructConds: false, disableDestructEq: false
};
const target = "True→True";
const history = ["intro h", "have k : True := by\n  exact h", "exact k"];
const previousDocument = globalThis.document;
const previousWindow = globalThis.window;
const elements = new Map();
const getElement = id => {
    if (!elements.has(id)) elements.set(id, {
        value: "", innerText: "", focus() {},
        classList: { add() {}, remove() {} },
        parentElement: { classList: { add() {}, remove() {} } }
    });
    return elements.get(id);
};
globalThis.document = { getElementById: getElement };
globalThis.window = { localStorage: { setItem() {} } };
try {
    const gui = Object.create(TTGui.prototype);
    Object.assign(gui, {
        mode: [target, ...history],
        tacticBusy: false, tacticRequestId: 0,
        tacticTextMode: false, tacticScriptDirty: true,
        tacticScript: `by\n  ${history.join("\n").replaceAll("\n", "\n  ")}`,
        tacticDefinitionsRevision: 0, definitionRevision: 0,
        assistWorker: null, proofSessions: new TTProofSessionStore(),
        assistSnapshot: engine.start(target, options, history),
        onStateChange() {}, renderTacticSessionTabs() {},
        setTacticBusy(busy) { this.tacticBusy = busy; },
        renderAssistSnapshot(snapshot) { this.assistSnapshot = snapshot; },
        async startAssistSession(source, history) { return engine.start(source, options, history); },
        async applyAssistCommand(command) { return engine.apply(command); },
        renderTacticTextSnapshot(snapshot, error, line) {
            this.lastRender = { snapshot, error, line };
        }
    });
    gui.proofSessions.openManual({ target, history, script: gui.tacticScript });
    getElement("tactic-script").value = gui.tacticScript;
    await gui.removeTactic();
    const expectedHistory = history.slice(0, -1);
    assert.deepEqual(gui.mode, [target, ...expectedHistory]);
    assert.equal(gui.tacticScriptDirty, false);
    assert.equal(gui.tacticScript, expectedHistory.join("\n"));
    assert.deepEqual(gui.proofSessions.active.history, expectedHistory);
    assert.equal(gui.proofSessions.active.script, expectedHistory.join("\n"));
    gui.toggleTacticTextMode();
    assert.equal(getElement("tactic-script").value, expectedHistory.join("\n"),
        "returning to text mode must not resurrect an undone block");
    assert.equal(gui.lastRender.snapshot.goals.length, 1);

    // Parse errors are caught before restarting or truncating the live session.
    const before = gui.mode.slice();
    getElement("tactic-script").value = "by\n  have k : True := by";
    await gui.replayTacticText(true);
    assert.deepEqual(gui.mode, before);
    assert.match(gui.lastRender.error, /第 2 行.*子证明不能为空/);
    assert.equal(gui.tacticBusy, false);

    // Runtime failures commit only preceding top-level blocks and preserve the draft.
    getElement("tactic-script").value = "by\n  intro h\n  have k : True := by\n    exact 0";
    await gui.replayTacticText(true);
    assert.deepEqual(gui.mode, [target, "intro h"]);
    assert.equal(gui.lastRender.line, 4);
    assert.match(gui.lastRender.error, /exact/);
    assert.ok(!gui.assistSnapshot.goals[0].context.some(([name]) => name === "k"));
    assert.equal(gui.proofSessions.active.script, getElement("tactic-script").value);
    assert.deepEqual(gui.proofSessions.active.history, ["intro h"]);
    assert.equal(gui.tacticBusy, false);
} finally {
    if (previousDocument === undefined) delete globalThis.document;
    else globalThis.document = previousDocument;
    if (previousWindow === undefined) delete globalThis.window;
    else globalThis.window = previousWindow;
}
console.log("type-theory structured script GUI recovery and undo regression passed");
