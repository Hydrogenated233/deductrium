import assert from "node:assert/strict";

import {
    createSandboxDeclaration,
    SandboxEnvironment
} from "../js/tt/sandbox.js";
import { SandboxWorkerSession } from "../js/tt/sandbox-worker.js";
import { SandboxWorkerClient } from "../js/tt/sandbox-worker-client.js";

const checked = result => result.validationStats?.checkedDeclarations;
const replayed = result => result.validationStats?.replayedDeclarations;

const sandbox = new SandboxEnvironment();
let result = sandbox.add("A : U");
const aTypeId = result.declarations[0].id;
assert.equal(checked(result), 1, "the first declaration is checked once");
assert.equal(replayed(result), 0);

result = sandbox.add("a : A");
const aId = result.declarations[1].id;
assert.equal(checked(result), 1, "append validates only the new declaration");
assert.equal(replayed(result), 0, "append keeps the live engine prefix in place");

result = sandbox.add("keep : A");
const keepId = result.declarations[2].id;
assert.equal(checked(result), 1);

result = sandbox.add("tail : A");
assert.equal(checked(result), 1);

result = sandbox.replace("keep2 : A", keepId);
assert.equal(checked(result), 2, "editing declaration k validates k and its suffix only");
assert.equal(replayed(result), 2, "the two validated prefix declarations are replayed, not rechecked");
assert.equal(result.declarations[0].status, "valid");
assert.equal(result.declarations[1].status, "valid");

result = sandbox.setEnabled(aId, false);
assert.equal(checked(result), 3, "disabling declaration k validates only the affected suffix");
assert.equal(replayed(result), 1, "the declaration before k is restored without validation");
assert.equal(result.declarations[0].id, aTypeId);

result = sandbox.setEnabled(aId, true);
assert.equal(checked(result), 3);
assert.equal(replayed(result), 1);

result = sandbox.remove(keepId);
assert.equal(checked(result), 1, "deleting declaration k validates the remaining suffix only");
assert.equal(replayed(result), 2);

const inductive = new SandboxEnvironment();
inductive.add("A : U");
const triResult = inductive.add("inductive tri : U | nt : tri | 0t : tri | pt : tri");
const triId = triResult.declarations[1].id;
inductive.add("triPoint : tri");
result = inductive.replace("inductive bit : U | ff : bit | tt : bit", triId);
assert.equal(checked(result), 2);
assert.equal(replayed(result), 1);
for (const oldName of ["tri", "nt", "0t", "pt", "ind_tri"]) {
    assert.equal(inductive.check(oldName).ok, false, `${oldName} must disappear after truncation`);
}
for (const newName of ["bit", "ff", "tt", "ind_bit"]) {
    assert.equal(inductive.check(newName).ok, true, `${newName} must be available after suffix rebuild`);
}

const save = sandbox.toJSON();
assert.ok(save.validationCache, "a validated sandbox save must include its versioned validation cache");
assert.equal(typeof save.validationCache.version, "number");
assert.ok(save.validationCache.version > 0);
const firstWorker = new SandboxWorkerSession();
assert.throws(
    () => firstWorker.handle({ id: 1, kind: "check", source: "A" }),
    /尚未加载|先加载|先校验/,
    "check must not implicitly load a save into an empty worker session"
);
const loaded = firstWorker.handle({ id: 2, kind: "load", save });
assert.equal(loaded.ok, true);
assert.equal(checked(loaded), 0,
    "a fresh worker must not recheck an unmodified persisted validation cache");
assert.equal(replayed(loaded), save.declarations.length,
    "a fresh worker replays every cached declaration into its new Core");
assert.ok(loaded.validationCache,
    "a cache hit must return the cache that can be persisted with the next save");
assert.equal(firstWorker.handle({ id: 3, kind: "check", source: "A" }).ok, true);

const appendedSave = structuredClone(save);
const appendedDeclaration = createSandboxDeclaration("workerTail : A", "sandbox-worker-tail");
appendedSave.declarations.push(appendedDeclaration);
appendedSave.order.push(appendedDeclaration.id);
const appended = firstWorker.handle({ id: 4, kind: "validate", save: appendedSave });
assert.equal(checked(appended), 1, "the persistent Worker validates an appended declaration only");
assert.equal(replayed(appended), 0);

const restartedWorker = new SandboxWorkerSession();
const restored = restartedWorker.handle({ id: 5, kind: "load", save: appendedSave });
assert.equal(restored.ok, true, "a restarted worker restores from the same save");
assert.equal(restartedWorker.handle({ id: 6, kind: "check", source: "workerTail" }).ok, true);
const unchanged = restartedWorker.handle({ id: 7, kind: "validate", save: appendedSave });
assert.equal(checked(unchanged), 0, "validating an unchanged save does not recheck its prefix");

class FakeSandboxWorker {
    listeners = new Map();
    session = new SandboxWorkerSession();

    addEventListener(type, listener) {
        const listeners = this.listeners.get(type) ?? [];
        listeners.push(listener);
        this.listeners.set(type, listeners);
    }

    postMessage(request) {
        try {
            const result = this.session.handle(request);
            this.emit("message", { data: { id: request.id, ok: true, result } });
        } catch (error) {
            this.emit("message", { data: { id: request.id, ok: false, error: String(error) } });
        }
    }

    terminate() { }

    emit(type, event) {
        for (const listener of this.listeners.get(type) ?? []) listener(event);
    }
}

const previousWorker = globalThis.Worker;
globalThis.Worker = FakeSandboxWorker;
try {
    const client = new SandboxWorkerClient();
    const clientValidation = await client.validate(save);
    assert.equal(checked(clientValidation), 0);
    assert.equal(replayed(clientValidation), save.declarations.length);
    assert.equal((await client.check(save, "A")).ok, true);
    client.terminate();
    assert.equal((await client.check(save, "A")).ok, true,
        "the client restores its persisted save once after Worker restart");
    client.terminate();
} finally {
    if (previousWorker === undefined) delete globalThis.Worker;
    else globalThis.Worker = previousWorker;
}

console.log("sandbox persistent incremental-session regression passed");
