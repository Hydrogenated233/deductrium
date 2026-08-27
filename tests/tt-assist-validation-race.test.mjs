import assert from "node:assert/strict";

import { TTGui } from "../js/tt/gui.js";
import { TTProofSessionStore } from "../js/tt/proof-sessions.js";
import { TheoremValidationCoordinator } from "../js/tt/theorem-validation.js";

const variable = name => ({
    type: "var",
    name,
    nodes: undefined,
    checked: null,
    err: null,
    bondVarId: null
});

const previousDocument = globalThis.document;
const elements = new Map();
const getElement = id => {
    if (!elements.has(id)) {
        elements.set(id, {
            classList: { add() { }, remove() { } },
            innerText: "",
            value: "",
            focus() { },
            parentElement: { scrollTo() { } }
        });
    }
    return elements.get(id);
};
globalThis.document = { getElementById: getElement };

try {
    const gui = Object.create(TTGui.prototype);
    gui.tacticBusy = false;
    gui.tacticRequestId = 0;
    gui.tacticTextReplayRevision = 0;
    gui.tacticTextReplayTimer = null;
    gui.tacticTextMode = false;
    gui.tacticScript = "";
    gui.tacticScriptDirty = false;
    gui.tacticSelectingTarget = false;
    gui.tacticTargetInput = null;
    gui.tacticScopeFolderId = null;
    gui.tacticScopeExplicit = false;
    gui.tacticDefinitionsRevision = -1;
    gui.definitionRevision = 0;
    gui.proofSessions = new TTProofSessionStore();
    gui.assistFallback = { clear() { } };
    gui.assistWorkerSessionReady = false;
    gui.assistSnapshot = null;
    gui.onStateChange = () => { };
    gui.userDefinedConsts = [
        ["zero_add", variable("true")],
        null
    ];
    let directBlurCalls = 0;
    const pendingInput = {
        parentElement: {
            classList: {
                contains(name) { return name === "checking"; }
            }
        },
        onblur() { directBlurCalls++; }
    };
    gui.getInhabitatArray = () => [pendingInput];
    gui.isTheoremInputDisabled = () => false;
    gui.theoremValidation = new TheoremValidationCoordinator();
    gui.renderTacticScopeOptions = () => { };
    gui.renderTacticSessionTabs = () => { };
    gui.renderAssistSnapshot = () => { };
    gui.resizeTacticInput = () => { };
    gui.setTacticBusy = busy => { gui.tacticBusy = busy; };

    let scheduledValidationStart = null;
    gui.revalidateTheorems = startIndex => {
        scheduledValidationStart = startIndex;
        assert.equal(gui.theoremValidation.request(startIndex), null,
            "the pending suffix must be queued behind the active validation");
    };

    let configuredNames = null;
    gui.startAssistSession = async () => {
        configuredNames = gui.userDefinedConsts
            .filter(Boolean)
            .map(definition => definition[0]);
        return { history: [] };
    };

    const validation = gui.theoremValidation.request(1);
    assert.ok(validation);

    let sessionStarts = 0;
    const originalStartAssistSession = gui.startAssistSession;
    gui.startAssistSession = async (...args) => {
        sessionStarts++;
        return originalStartAssistSession(...args);
    };

    const opening = gui.executeTactic("True", null, null);
    const duplicateOpening = gui.executeTactic("False", null, null);
    await Promise.resolve();
    assert.equal(configuredNames, null,
        "opening the proof assistant must wait for an in-flight theorem validation");
    assert.equal(gui.tacticBusy, true,
        "the proof assistant must become busy before waiting so rapid clicks cannot start duplicate sessions");
    assert.equal(scheduledValidationStart, 0,
        "opening the proof assistant must schedule the checking suffix through the validation coordinator");
    assert.equal(directBlurCalls, 0,
        "opening the proof assistant must not start an untracked validation chain directly");

    const followup = gui.theoremValidation.complete(validation.id);
    assert.ok(followup,
        "the invalidated active run must promote the queued proof-assistant validation");
    await Promise.resolve();
    assert.equal(configuredNames, null,
        "the proof assistant must keep waiting after the old validation run settles");
    gui.userDefinedConsts[1] = ["add_assoc", variable("true")];
    gui.definitionRevision++;
    gui.theoremValidation.complete(followup.id);
    await Promise.all([opening, duplicateOpening]);

    assert.deepEqual(configuredNames, ["zero_add", "add_assoc"],
        "the proof-assistant snapshot must include a definition committed by the pending validation");
    assert.equal(sessionStarts, 1,
        "rapid theorem clicks while validation is pending must start only one proof-assistant session");
} finally {
    if (previousDocument === undefined) delete globalThis.document;
    else globalThis.document = previousDocument;
}

console.log("proof-assistant pending-validation race regression passed");
