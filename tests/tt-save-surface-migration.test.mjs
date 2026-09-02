import assert from "node:assert/strict";

import {
    SavesParser,
    migrateLegacyTTSave
} from "../js/tt/savesparser.js";

const legacy = {
    version: 3,
    items: [
        { kind: "theorem", value: "id:=Lx:U.x", local: true },
        { kind: "folder", id: "folder-1", name: "L/P/S/X folder", length: 1, open: true, disabled: false },
        { kind: "theorem", value: "List:=Lx:U.x", local: false },
        { kind: "theorem", value: "xXy:=aXb", local: false }
    ],
    proofSessions: {
        activeId: "page-1",
        sessions: [{
            id: "page-1",
            kind: "manual",
            title: "legacy page",
            target: "Pa:U,Pb:U,aXb->a",
            history: ["intro a .", "exact Lx:U.x"],
            script: "intro a .\nexact Lx:U.x",
            scopeFolderId: "folder-1",
            scopeExplicit: true,
            theoremItemId: null,
            targetTheoremIndex: null,
            stale: false,
            detached: false
        }]
    }
};

const migrated = migrateLegacyTTSave(legacy);
assert.deepEqual(migrated.items, [
    { kind: "theorem", value: "id:=λx:U.x", local: true },
    { kind: "folder", id: "folder-1", name: "L/P/S/X folder", length: 1, open: true, disabled: false },
    { kind: "theorem", value: "List:=λx:U.x", local: false },
    { kind: "theorem", value: "xXy:=a×b", local: false }
]);
const session = migrated.proofSessions.sessions[0];
assert.equal(session.target, "Πa:U,Πb:U,a×b→a");
assert.deepEqual(session.history, ["intro a .", "exact λx:U.x"]);
assert.equal(session.script, "intro a .\nexact λx:U.x");
assert.equal(session.scopeFolderId, "folder-1");
assert.equal(migrated.proofSessions.activeId, "page-1");

// Loading a save that has already been migrated must be a no-op.  This keeps
// migration at the load boundary and prevents syntax drift on repeated saves.
assert.deepEqual(migrateLegacyTTSave(migrated), migrated);

const calls = [];
const gui = {
    resetProofAssistantForSaveLoad() { calls.push("reset"); },
    restoreTheoremItems(items) { calls.push(["items", items]); },
    queueProofSessionsRestore(proofSessions) { calls.push(["sessions", proofSessions]); }
};
new SavesParser().deserialize(gui, JSON.stringify(legacy));
assert.equal(calls[0], "reset");
assert.deepEqual(calls[1][1], migrated.items);
assert.deepEqual(calls[2][1], migrated.proofSessions);

// Legacy array saves are still accepted at the boundary, while declaration
// names containing marker letters remain unchanged.
const arraySave = migrateLegacyTTSave(["Pfoo:=Lx:U.x", "S1:=aXb"]);
assert.deepEqual(arraySave.items, [
    { kind: "theorem", value: "Pfoo:=λx:U.x" },
    { kind: "theorem", value: "S1:=a×b" }
]);

console.log("type-theory save surface migration regression passed");
