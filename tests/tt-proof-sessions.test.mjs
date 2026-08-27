import assert from "node:assert/strict";
import { TTProofSessionStore } from "../js/tt/proof-sessions.js";

const store = new TTProofSessionStore();
assert.equal(store.size, 0);
assert.equal(store.activeId, null);

const pageStore = new TTProofSessionStore();
const blankPage = pageStore.openBlank();
pageStore.update(blankPage.id, { title: "交换律" });
const filledPage = pageStore.openTheorem({
    target: "Page proposition",
    theoremItemId: "page-theorem",
    targetTheoremIndex: 0,
    history: ["intro h"],
    script: "intro h"
}, true);
assert.equal(filledPage.id, blankPage.id,
    "selecting a target must fill the active blank page instead of adding another page");
assert.equal(pageStore.size, 1);
const resetPage = pageStore.reset();
assert.equal(resetPage?.id, blankPage.id, "qed/reset must preserve the page id");
assert.equal(resetPage?.title, "交换律", "qed/reset must preserve the user-defined page name");
assert.equal(pageStore.activeId, blankPage.id, "qed/reset must keep the page active");
assert.equal(resetPage?.kind, "manual");
assert.equal(resetPage?.target, "");
assert.deepEqual(resetPage?.history, []);
assert.equal(resetPage?.script, "");
assert.equal(resetPage?.theoremItemId, null);
assert.equal(pageStore.size, 1, "qed/reset must not delete the page");
assert.equal(TTProofSessionStore.deserialize(pageStore.serialize()).active?.title, "交换律",
    "blank pages and their custom names must survive save restoration");

const gatePage = pageStore.openGate({ target: "Gate proposition" }, true);
assert.equal(gatePage.id, blankPage.id, "a gate target must also reuse the active blank page");

const emptyPages = new TTProofSessionStore();
const emptyA = emptyPages.openBlank();
const emptyB = emptyPages.openBlank();
assert.notEqual(emptyA.id, emptyB.id, "users must be able to keep multiple empty proof pages");
assert.equal(emptyPages.size, 2);
assert.deepEqual(TTProofSessionStore.deserialize(emptyPages.serialize()).serialize(), emptyPages.serialize(),
    "multiple empty proof pages must survive save restoration");

const theorem = store.openTheorem({
    target: "P",
    theoremItemId: "theorem-a",
    targetTheoremIndex: 2,
    scopeFolderId: "folder-a"
});
const manual = store.openManual({ target: "Q" });
const gate = store.openGate({ target: "R", scopeFolderId: "folder-b" });
assert.deepEqual(store.sessions.map(session => session.id), [theorem.id, manual.id, gate.id]);
assert.equal(new Set(store.sessions.map(session => session.id)).size, 3);
assert.equal(store.activeId, gate.id);

const reused = store.openTheorem({
    target: "P",
    theoremItemId: "theorem-a",
    targetTheoremIndex: 3,
    scopeFolderId: "folder-a"
});
assert.equal(reused.id, theorem.id, "opening the same theorem must reuse its tab");
assert.equal(store.size, 3);
assert.equal(store.activeId, theorem.id);
assert.equal(reused.targetTheoremIndex, 3);

const inserted = store.openTheorem({
    target: "Inserted",
    theoremItemId: "theorem-inserted",
    targetTheoremIndex: 3,
    scopeFolderId: "folder-a"
});
assert.notEqual(inserted.id, theorem.id,
    "a live insertion at an old theorem index must not steal the existing session");
assert.equal(store.session(theorem.id)?.theoremItemId, "theorem-a");
const moved = store.openTheorem({
    target: "P",
    theoremItemId: "theorem-a",
    targetTheoremIndex: 4,
    scopeFolderId: "folder-a"
});
assert.equal(moved.id, theorem.id, "live reorder must follow the stable theorem id");
assert.equal(moved.targetTheoremIndex, 4);
const relocated = store.updateTheoremLocation("theorem-a", 5, "folder-moved");
assert.equal(relocated.targetTheoremIndex, 5);
assert.equal(relocated.scopeFolderId, "folder-moved");
assert.equal(relocated.stale, true, "moving to a different reference scope must require replay");
store.update(theorem.id, { stale: false });

const secondManual = store.openManual({ target: "Q" });
const secondGate = store.openGate({ target: "R" });
assert.notEqual(secondManual.id, manual.id, "manual goals always open a new tab");
assert.notEqual(secondGate.id, gate.id, "gate goals always open a new tab");

const closeStore = new TTProofSessionStore();
const first = closeStore.openManual({ target: "first" });
const middle = closeStore.openManual({ target: "middle" });
const last = closeStore.openManual({ target: "last" });
closeStore.activate(middle.id);
closeStore.close(middle.id);
assert.equal(closeStore.activeId, first.id, "closing an active tab should prefer the previous tab");
closeStore.close(first.id);
assert.equal(closeStore.activeId, last.id, "closing the first active tab should select the next tab");
const background = closeStore.openGate({ target: "background" });
closeStore.activate(last.id);
closeStore.close(background.id);
assert.equal(closeStore.activeId, last.id, "closing a background tab must keep the active tab");

const editable = store.openTheorem({
    target: "Old",
    theoremItemId: "theorem-edit",
    targetTheoremIndex: 8,
    scopeFolderId: "folder-old",
    history: ["intro x"],
    script: "intro x\nexact x"
});
store.update(editable.id, {
    history: ["intro y"],
    script: "intro y\nexact y",
    scopeFolderId: "folder-new",
    scopeExplicit: true,
    stale: false,
    detached: false
});
const explicitMove = store.updateTheoremLocation("theorem-edit", 10, "folder-default");
assert.equal(explicitMove.scopeFolderId, "folder-new",
    "an explicitly selected scope must not follow theorem movement");
assert.equal(explicitMove.scopeExplicit, true);
const changed = store.markTheoremTargetChanged("theorem-edit", "New", 9);
assert.deepEqual(changed, {
    ...editable,
    target: "New",
    history: ["intro y"],
    script: "intro y\nexact y",
    scopeFolderId: "folder-new",
    scopeExplicit: true,
    targetTheoremIndex: 9,
    stale: true
});
assert.equal(store.detachTheorem("theorem-edit")?.detached, true);
assert.equal(store.session(editable.id)?.history[0], "intro y", "detaching must retain the draft");
assert.equal(store.session(editable.id)?.theoremItemId, null, "a detached session must release its row id");
assert.equal(store.session(editable.id)?.targetTheoremIndex, null,
    "a detached session must release its theorem-index fallback");

const reordered = store.sessions.map(session => session.id);
store.reorder(secondGate.id, reordered[0]);
assert.equal(store.sessionAt(0)?.id, secondGate.id);

const serialized = store.serialize();
const restored = TTProofSessionStore.deserialize(serialized);
assert.deepEqual(restored.serialize(), serialized, "serialization must preserve order, activity and every field");

const migrated = TTProofSessionStore.deserialize({
    activeId: "proof-session-7",
    sessions: [{
        id: "proof-session-7",
        kind: "theorem",
        target: "Saved",
        history: ["intro h"],
        script: "intro h\nexact h",
        scopeFolderId: "saved-folder",
        theoremItemId: "old-row-id",
        targetTheoremIndex: 4,
        stale: false,
        detached: false
    }]
});
const rebound = migrated.rebindTheoremByIndex({
    target: "Saved",
    theoremItemId: "new-row-id",
    targetTheoremIndex: 4,
    scopeFolderId: "saved-folder"
});
assert.equal(rebound.id, "proof-session-7", "the theorem index should recover a regenerated row id");
assert.equal(rebound.theoremItemId, "new-row-id");
assert.equal(rebound.stale, false, "identity migration alone must not force replay");
assert.equal(migrated.size, 1);
assert.equal(migrated.openTheorem({
    target: "Saved",
    theoremItemId: "new-row-id",
    targetTheoremIndex: 4,
    scopeFolderId: "saved-folder"
}).id, "proof-session-7");
assert.equal(migrated.openManual({ target: "fresh" }).id, "proof-session-8");

const updateStore = new TTProofSessionStore();
const updateSession = updateStore.openTheorem({
    target: "Before",
    theoremItemId: "row-update",
    targetTheoremIndex: 0,
    scopeFolderId: "folder-before"
});
assert.equal(updateSession.scopeExplicit, false);
assert.equal(updateStore.update(updateSession.id, { target: "After" }).stale, true,
    "changing a theorem target through update must mark its proof stale");
updateStore.update(updateSession.id, { stale: false });
assert.equal(updateStore.update(updateSession.id, { scopeFolderId: "folder-after" }).stale, true,
    "changing a theorem scope through update must mark its proof stale");

const liveReorder = new TTProofSessionStore();
const reorderA = liveReorder.openTheorem({
    target: "A",
    theoremItemId: "row-a",
    targetTheoremIndex: 0
});
liveReorder.openTheorem({
    target: "B",
    theoremItemId: "row-b",
    targetTheoremIndex: 1
});
liveReorder.openTheorem({
    target: "A",
    theoremItemId: "row-a",
    targetTheoremIndex: 1
});
assert.equal(liveReorder.session(reorderA.id)?.targetTheoremIndex, 1);
assert.equal(new Set(liveReorder.sessions.map(session => session.targetTheoremIndex)).size, 2,
    "live reorder must keep theorem indexes unique");
assert.doesNotThrow(() => TTProofSessionStore.deserialize(liveReorder.serialize()),
    "a live reorder snapshot must remain deserializable");

assert.throws(() => new TTProofSessionStore([
    { id: "duplicate", kind: "manual", target: "A" },
    { id: "duplicate", kind: "gate", target: "B" }
]), /已存在/);
assert.throws(() => new TTProofSessionStore([
    {
        id: "bound-a",
        kind: "theorem",
        target: "A",
        theoremItemId: "same-row",
        targetTheoremIndex: 0
    },
    {
        id: "bound-b",
        kind: "theorem",
        target: "B",
        theoremItemId: "same-row",
        targetTheoremIndex: 1
    }
]), /同一定理/);
assert.throws(() => new TTProofSessionStore([
    {
        id: "index-a",
        kind: "theorem",
        target: "A",
        theoremItemId: "row-a",
        targetTheoremIndex: 0
    },
    {
        id: "index-b",
        kind: "theorem",
        target: "B",
        theoremItemId: "row-b",
        targetTheoremIndex: 0
    }
]), /同一定理/);

const singleton = new TTProofSessionStore();
const only = singleton.openManual({ target: "Only" });
assert.equal(singleton.close(only.id)?.id, only.id);
assert.equal(singleton.activeId, null);
assert.equal(singleton.size, 0);

console.log("type-theory proof-session store regression passed");
