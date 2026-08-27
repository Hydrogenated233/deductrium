import assert from "node:assert/strict";

import { TTGui } from "../js/tt/gui.js";
import { TTProofSessionStore } from "../js/tt/proof-sessions.js";

const previousDocument = globalThis.document;
const hint = { innerText: "" };
globalThis.document = {
    getElementById(id) {
        if (id === "tactic-hint") return hint;
        if (id === "tactic-script") return { value: "" };
        return null;
    }
};

try {
    const gui = Object.create(TTGui.prototype);
    gui.proofSessions = new TTProofSessionStore();
    const page = gui.proofSessions.openTheorem({
        target: "P",
        theoremItemId: "theorem-p",
        targetTheoremIndex: 0,
        history: ["intro h", "exact h"],
        script: "intro h\nexact h"
    });
    gui.mode = ["P", "intro h", "exact h"];
    gui.tacticTextMode = false;
    gui.tacticScriptDirty = false;
    gui.tacticScript = "intro h\nexact h";
    gui.tacticScopeFolderId = null;
    gui.tacticScopeExplicit = false;
    gui.tacticSessionReplayId = null;
    gui.tacticCaptureBlockedSessionId = null;
    gui.clearTacticRuntime = () => { gui.mode = null; };
    gui.renderTacticSessionTabs = () => { };
    gui.onStateChange = () => { };

    gui.resetTacticPage();
    assert.equal(gui.proofSessions.size, 1, "clearing a proof page must not delete it");
    assert.equal(gui.proofSessions.activeId, page.id);
    assert.equal(gui.proofSessions.active?.target, "");
    assert.deepEqual(gui.proofSessions.active?.history, []);
    assert.equal(gui.mode, "tactic-begin");
    assert.equal(gui.tacticSelectingTarget, true);
    assert.ok(hint.innerText.length > 0, "a cleared page must ask the user to select a new target");

    let activatedId = null;
    gui.activateTacticSession = id => { activatedId = id; };
    gui.selectTacticSession(page.id);
    assert.equal(activatedId, null, "clicking the current page must not replay it");
    gui.proofSessions.openBlank();
    gui.selectTacticSession(page.id);
    assert.equal(activatedId, page.id, "clicking another page must still activate it lazily");

    const replayStore = new TTProofSessionStore();
    const replayPage = replayStore.openManual({
        target: "P",
        history: ["intro h", "exact h"],
        script: "intro h\nexact h"
    });
    gui.proofSessions = replayStore;
    gui.mode = ["P", "intro h"];
    gui.getInhabitatArray = () => [];
    gui.reconcileProofSessionBindings = () => { };

    gui.tacticSessionReplayId = replayPage.id;
    assert.deepEqual(gui.serializeProofSessions().sessions[0].history, ["intro h", "exact h"],
        "autosave during replay must preserve the complete stored history");

    gui.tacticSessionReplayId = null;
    gui.tacticCaptureBlockedSessionId = replayPage.id;
    assert.deepEqual(gui.serializeProofSessions().sessions[0].history, ["intro h", "exact h"],
        "autosave after a failed replay must not replace the draft with its accepted prefix");
} finally {
    if (previousDocument === undefined) delete globalThis.document;
    else globalThis.document = previousDocument;
}

console.log("type-theory proof-page lifecycle regression passed");
