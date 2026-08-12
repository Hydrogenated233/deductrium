import assert from "node:assert/strict";

import { TTGui } from "../js/tt/gui.js";
import { TTWorkerMutationQueue } from "../js/tt/worker-mutation-queue.js";

const variable = name => ({
    type: "var",
    name,
    nodes: undefined,
    checked: null,
    err: null,
    bondVarId: null
});
const waitUntil = async predicate => {
    for (let attempt = 0; attempt < 20; attempt++) {
        if (predicate()) return;
        await new Promise(resolve => setTimeout(resolve, 0));
    }
    throw new Error("timed out waiting for mocked Worker request");
};

const definitions = Array.from({ length: 12 }, (_, index) => [
    `definition${index}`,
    variable("true")
]);

const coreEvents = [];
const assistEvents = [];
let resolveOldSetDefinition;
let delayedSetDefinitionIndex = -1;
let resolveOldValidate;
let delayedValidateIndex = -1;
let rejectOldTruncate;
let rejectedTruncateIndex = -1;
const coreWorker = {
    generation: 1,
    async configure(_config, slots) {
        coreEvents.push({ kind: "configure", slots: slots.length });
    },
    async truncate(startIndex) {
        coreEvents.push({ kind: "truncate", startIndex });
        if (startIndex === rejectedTruncateIndex) {
            await new Promise((_resolve, reject) => rejectOldTruncate = reject);
        }
    },
    async validate(index) {
        coreEvents.push({ kind: "validate", index });
        if (index === delayedValidateIndex) {
            await new Promise(resolve => resolveOldValidate = resolve);
        }
        return { ok: true };
    },
    async setDefinition(index) {
        coreEvents.push({ kind: "set-definition", index });
        if (index === delayedSetDefinitionIndex) {
            await new Promise(resolve => resolveOldSetDefinition = resolve);
        }
    }
};
const assistWorker = {
    generation: 1,
    async configure(_config, slots) {
        assistEvents.push({ kind: "configure", slots: slots.length });
    },
    async truncate(startIndex) {
        assistEvents.push({ kind: "truncate", startIndex });
    }
};

const gui = Object.create(TTGui.prototype);
gui.unlockedTypes = new Set(["True"]);
gui.disableSimpleFn = false;
gui.disableSimpleEq = false;
gui.inferDisplayMode = "_";
gui.userDefinedConsts = definitions;
gui.definitionRevision = 0;
gui.coreWorker = coreWorker;
gui.coreWorkerGeneration = -1;
gui.coreWorkerConfigKey = "";
gui.coreWorkerConfigurePromise = null;
gui.coreWorkerLoadedThrough = 0;
gui.coreWorkerStateRevision = 0;
gui.coreWorkerMutations = new TTWorkerMutationQueue();
gui.assistWorker = assistWorker;
gui.assistWorkerGeneration = -1;
gui.assistWorkerConfigKey = "";
gui.assistWorkerConfigurePromise = null;
gui.assistWorkerMutations = new TTWorkerMutationQueue();
gui.assistWorkerSessionReady = false;
gui.getWorkerDefinitionSlots = definitionEnd => definitions.slice(0, definitionEnd);

let coordinatedValidationStarts = 0;
gui.skipRendering = false;
gui.updateTypeList = () => { };
gui.revalidateTheorems = () => { coordinatedValidationStarts++; };
gui.updateAfterUnlock();
assert.equal(coordinatedValidationStarts, 1,
    "an unlock refresh must enter the coordinated validation chain exactly once");

// Initial save loading has no configured suffix to discard.
gui.invalidateWorkerDefinitions(0);
await gui.coreWorkerMutations.wait();
assert.equal(coreEvents.length, 0,
    "initial validation must not truncate an unconfigured Worker session");

for (let index = 0; index < definitions.length; index++) {
    if (index > 0) gui.invalidateWorkerDefinitions(index);
    await gui.prepareCoreWorker(index, null);
    await gui.validateCoreWorker(index, definitions[index][1]);
}

assert.deepEqual(coreEvents.filter(event => event.kind === "configure"), [
    { kind: "configure", slots: 0 }
], "sequential validation in one scope must configure the core Worker once");
assert.equal(coreEvents.filter(event => event.kind === "validate").length, definitions.length);
assert.deepEqual(assistEvents, [],
    "loading the theorem list must not initialize or synchronize the proof-assistant Worker");

coreEvents.length = 0;
for (let index = 0; index < definitions.length; index++) {
    gui.invalidateWorkerDefinitions(index);
    await gui.prepareCoreWorker(index, null);
    await gui.validateCoreWorker(index, definitions[index][1]);
}
assert.equal(coreEvents.filter(event => event.kind === "configure").length, 0,
    "a complete same-scope revalidation must reuse the persistent core configuration");
assert.equal(coreEvents.filter(event => event.kind === "truncate").length, 1,
    "a complete revalidation must truncate once at the start, not once per theorem");

gui.invalidateWorkerDefinitions(5);
await gui.coreWorkerMutations.wait();
assert.deepEqual(coreEvents.filter(event => event.kind === "truncate").slice(-1), [
    { kind: "truncate", startIndex: 5 }
], "editing a suffix must truncate the configured core Worker exactly once");

await gui.prepareCoreWorker(5, null);
assert.equal(coreEvents.filter(event => event.kind === "configure").length, 0,
    "suffix validation after truncate must reuse the existing core configuration");

// A validate request is not part of the mutation queue. If it finishes after
// a same-scope truncate, its result belongs to the old logical Worker state.
gui.coreWorkerLoadedThrough = 6;
delayedValidateIndex = 5;
const oldValidate = gui.validateCoreWorker(5, definitions[5][1]);
gui.invalidateWorkerDefinitions(2);
await gui.coreWorkerMutations.wait();
assert.equal(gui.coreWorkerLoadedThrough, 2);
resolveOldValidate();
await oldValidate;
assert.equal(gui.coreWorkerLoadedThrough, 2,
    "an old same-scope validate completion must not restore a truncated prefix");
delayedValidateIndex = -1;

// setDefinition is serialized with truncate, but its completion handler may
// run after invalidation has already lowered the UI's prefix marker.
gui.coreWorkerLoadedThrough = 6;
delayedSetDefinitionIndex = 5;
gui.syncCoreWorkerDefinition(5, definitions[5]);
await waitUntil(() => typeof resolveOldSetDefinition === "function");
gui.invalidateWorkerDefinitions(2);
resolveOldSetDefinition();
await gui.coreWorkerMutations.wait();
assert.equal(gui.coreWorkerLoadedThrough, 2,
    "an old same-scope setDefinition completion must not restore a truncated prefix");
delayedSetDefinitionIndex = -1;

await gui.prepareCoreWorker(definitions.length, "folder-a");
await gui.prepareCoreWorker(definitions.length, "folder-a");
assert.deepEqual(coreEvents.filter(event => event.kind === "configure").map(event => event.slots), [12],
    "a lexical-scope transition may rebuild once, but must remain stable within that scope");

// A queued write from an old lexical configuration must not overwrite the
// loaded-prefix marker after the active scope has changed.
delayedSetDefinitionIndex = 3;
gui.syncCoreWorkerDefinition(3, definitions[3]);
await new Promise(resolve => setTimeout(resolve, 0));
gui.coreWorkerConfigKey = "new-scope";
gui.coreWorkerLoadedThrough = 9;
resolveOldSetDefinition();
await gui.coreWorkerMutations.wait();
assert.equal(gui.coreWorkerLoadedThrough, 9,
    "an old-scope setDefinition completion must not roll back the active loaded prefix");

// A failed truncate from an obsolete revision must not clear a newer
// configuration that was queued behind it.
gui.coreWorkerConfigKey = JSON.stringify({ config: gui.getWorkerSystemConfig(), scopeFolderId: "folder-a" });
gui.coreWorkerLoadedThrough = definitions.length;
rejectedTruncateIndex = 4;
gui.invalidateWorkerDefinitions(4);
const newerConfiguration = gui.prepareCoreWorker(definitions.length, "folder-b");
await waitUntil(() => typeof rejectOldTruncate === "function");
rejectOldTruncate(new Error("simulated obsolete truncate failure"));
await newerConfiguration;
assert.equal(gui.coreWorkerGeneration, coreWorker.generation);
assert.equal(gui.coreWorkerLoadedThrough, definitions.length);
assert.match(gui.coreWorkerConfigKey, /folder-b/,
    "an obsolete truncate failure must not clear the newer Worker configuration");

console.log("GUI incremental Worker synchronization regression passed");
