import assert from "node:assert/strict";

import { TTGui } from "../js/tt/gui.js";

const variable = name => ({
    type: "var",
    name,
    nodes: undefined,
    checked: null,
    err: null,
    bondVarId: null
});

const theorem = (id, local = false) => ({
    kind: "theorem",
    id,
    wrapper: {},
    input: { value: id, dataset: {}, parentElement: null },
    localCheckbox: { checked: local }
});

const folder = (id, name, length) => ({
    kind: "folder",
    id,
    name,
    length,
    open: true,
    disabled: false,
    wrapper: {},
    title: {},
    checkbox: { checked: false }
});

// The target is deliberately above `add_assoc`. Proof-assistant references
// are selected by folder scope, so moving either theorem must not change the
// configured definition pool.
const target = theorem("target");
const folderA = folder("folder-a", "A", 3);
const localA = theorem("local-a", true);
const addAssoc = theorem("add-assoc");
const folderB = folder("folder-b", "B", 1);
const localB = theorem("local-b", true);
const items = [folderA, target, localA, addAssoc, folderB, localB];
const inputs = items.filter(item => item.kind === "theorem").map(item => item.input);

const gui = Object.create(TTGui.prototype);
gui.theoremItems = items;
gui.userDefinedConsts = [
    ["targetSelf", variable("true")],
    ["helperA", variable("true")],
    ["add_assoc", variable("true")],
    ["helperB", variable("true")]
];
gui.getInhabitatArray = () => inputs;
gui.isTheoremInputDisabled = () => false;
gui.unlockedTypes = new Set();
gui.disableSimpleFn = false;
gui.disableSimpleEq = false;
gui.inferDisplayMode = "_";
gui.tacticTargetInput = target.input;
gui.tacticScopeFolderId = "folder-a";
gui.tacticScopeExplicit = true;
gui.assistWorkerGeneration = -1;
gui.assistWorkerConfigKey = "";
gui.assistWorkerSessionReady = false;

let configuredDefinitions = null;
gui.assistWorker = {
    generation: 1,
    async configure(_config, definitions) {
        configuredDefinitions = definitions;
    },
    async start() {
        return { theorem: variable("true"), elem: variable("true"), goals: [], tactics: [], history: [] };
    }
};

let pending = Promise.resolve();
gui.assistWorkerMutations = {
    enqueue(operation) {
        pending = pending.then(operation);
        return pending;
    },
    wait() {
        return pending;
    }
};

await gui.startAssistSession("true");

const names = configuredDefinitions.filter(Boolean).map(definition => definition[0]);
assert.deepEqual(names, ["helperA", "add_assoc"],
    "the proof assistant must use the selected folder scope across the full theorem list");
assert.equal(names.includes("targetSelf"), false,
    "the theorem currently being proved must not be available as its own proof");
assert.equal(names.includes("helperB"), false,
    "local definitions from an unselected folder must stay unavailable");

console.log("proof-assistant position-independent definition scope regression passed");
