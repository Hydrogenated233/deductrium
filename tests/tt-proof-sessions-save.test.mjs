import assert from "node:assert/strict";

import { TTProofSessionStore } from "../js/tt/proof-sessions.js";
import { SavesParser } from "../js/tt/savesparser.js";

function makeRestoreGui() {
    const calls = [];
    return {
        calls,
        items: null,
        proofSessions: null,
        resetProofAssistantForSaveLoad() {
            calls.push("reset");
        },
        restoreTheoremItems(items) {
            calls.push("items");
            this.items = items;
        },
        queueProofSessionsRestore(proofSessions) {
            calls.push("sessions");
            this.proofSessions = proofSessions;
        }
    };
}

const sessions = new TTProofSessionStore();
const bound = sessions.openTheorem({
    target: "Bound proposition",
    theoremItemId: "old-row-id",
    targetTheoremIndex: 1,
    scopeFolderId: "folder-a",
    history: ["intro x"],
    script: "intro x\nexact x"
});
const manual = sessions.openManual({
    target: "Manual proposition",
    title: "自定义证明页",
    history: ["rfl"],
    script: "rfl"
});
const detached = sessions.openTheorem({
    target: "Deleted proposition",
    theoremItemId: "deleted-row-id",
    targetTheoremIndex: 2,
    scopeFolderId: "folder-b",
    history: ["intro h"],
    script: "intro h"
});
sessions.detachTheorem("deleted-row-id");
sessions.reorder(detached.id, bound.id);
sessions.activate(manual.id);

const expectedSessions = sessions.serialize();
const items = [
    { kind: "theorem", value: "First proposition", local: false },
    { kind: "theorem", value: "Bound proposition", local: false },
    { kind: "theorem", value: "Replacement proposition", local: false }
];
const parser = new SavesParser();
const text = parser.serialize({
    serializeTheoremItems: () => items,
    serializeProofSessions: () => expectedSessions
});
const envelope = JSON.parse(text);

assert.equal(envelope.version, 3);
assert.deepEqual(envelope.items, items);
assert.deepEqual(envelope.proofSessions, expectedSessions,
    "v3 saves must preserve tab order, active tab and every session draft");

const restoredGui = makeRestoreGui();
parser.deserialize(restoredGui, text);
assert.deepEqual(restoredGui.calls, ["reset", "items", "sessions"],
    "the old assistant state must be reset before theorem rows and sessions are restored");
assert.deepEqual(restoredGui.items, items);

const restored = TTProofSessionStore.deserialize(restoredGui.proofSessions);
assert.deepEqual(restored.serialize(), expectedSessions,
    "v3 proof-session state must roundtrip through SavesParser");
assert.equal(restored.activeId, manual.id);
assert.deepEqual(restored.sessions.map(session => session.id),
    expectedSessions.sessions.map(session => session.id));

const rebound = restored.rebindTheoremByIndex({
    target: "Bound proposition",
    theoremItemId: "rebuilt-row-id",
    targetTheoremIndex: 1,
    scopeFolderId: "folder-a"
});
assert.equal(rebound?.id, bound.id,
    "a restored theorem tab must rebind by theorem index when row ids are regenerated");
assert.equal(rebound?.theoremItemId, "rebuilt-row-id");
assert.equal(rebound?.detached, false);

const restoredDetached = restored.session(detached.id);
assert.equal(restoredDetached?.detached, true,
    "a detached saved tab must remain detached during theorem-index rebinding");
assert.equal(restoredDetached?.theoremItemId, null);
assert.equal(restoredDetached?.targetTheoremIndex, null);
assert.deepEqual(restoredDetached?.history, ["intro h"]);

for (const legacy of [
    JSON.stringify({
        version: 2,
        items,
        proofSessions: expectedSessions
    }),
    JSON.stringify(items.map(item => item.value))
]) {
    const legacyGui = makeRestoreGui();
    parser.deserialize(legacyGui, legacy);
    assert.deepEqual(legacyGui.calls, ["reset", "items", "sessions"]);
    assert.equal(TTProofSessionStore.deserialize(legacyGui.proofSessions).size, 0,
        "v2 and array saves must migrate with no proof sessions");
}

const arrayGui = makeRestoreGui();
parser.deserialize(arrayGui, JSON.stringify(["Legacy A", "Legacy B"]));
assert.deepEqual(arrayGui.items, [
    { kind: "theorem", value: "Legacy A" },
    { kind: "theorem", value: "Legacy B" }
]);

console.log("type-theory proof-session save migration regression passed");
