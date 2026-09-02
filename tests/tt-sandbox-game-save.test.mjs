import assert from "node:assert/strict";

import { GameSaveLoad } from "../js/saveload.js";
import {
    SandboxEnvironment,
    SANDBOX_SAVE_VERSION,
    creativeSandboxSystemRuleIds
} from "../js/tt/sandbox.js";
import { SandboxWorkerSession } from "../js/tt/sandbox-worker.js";

const loader = Object.create(GameSaveLoad.prototype);
const restored = [];
const sandboxGui = {
    restoreGameSave(value) { restored.push(value); }
};

const encoded = loader.serializeSandbox({
    creative: true,
    sandboxGui: {
        serializeGameSave() {
            return {
                version: SANDBOX_SAVE_VERSION,
                declarations: [],
                folders: [{
                    kind: "folder",
                    id: "sandbox-folder-1",
                    name: "contains-(=)-separator",
                    length: 0,
                    open: true,
                    disabled: false
                }],
                order: ["sandbox-folder-1"]
            };
        }
    }
});
assert.equal(encoded.includes("-(=)-"), false,
    "sandbox user text must not escape into the legacy save-section delimiter");

loader.restoreSandbox({ creative: true, sandboxGui }, JSON.stringify({
    version: SANDBOX_SAVE_VERSION,
    declarations: [{ id: "sandbox-1", source: "A : U" }],
    folders: [],
    order: ["sandbox-1"]
}));
assert.equal(restored.length, 1);
assert.equal(restored[0].declarations[0].source, "A : U",
    "creative saves must restore the embedded sandbox field");

loader.restoreSandbox({ creative: true, sandboxGui }, encoded);
assert.equal(restored[1].folders[0].name, "contains-(=)-separator",
    "the encoded sandbox field must roundtrip arbitrary folder text");

loader.restoreSandbox({ creative: true, sandboxGui }, undefined);
assert.deepEqual(restored[2], {
    version: SANDBOX_SAVE_VERSION,
    declarations: [],
    folders: [],
    order: []
}, "legacy creative saves without a sandbox field must replace it with an empty workspace");

loader.restoreSandbox({ creative: false, sandboxGui }, JSON.stringify({
    version: SANDBOX_SAVE_VERSION,
    declarations: [{ id: "sandbox-2", source: "B : U" }]
}));
assert.equal(restored.length, 3,
    "survival mode must ignore sandbox save data completely");

const { TTSandboxGui } = await import("../js/tt/sandbox-gui.js");
const gui = Object.create(TTSandboxGui.prototype);
gui.declarations = [{
    id: "sandbox-1",
    name: "A",
    kind: "type",
    source: "A : U",
    typeSource: "U",
    enabled: true,
    trusted: true,
    status: "valid",
    dependencies: [],
    folderId: null,
    presentationAst: { type: "var", name: "A", nodes: [] }
}];
gui.folders = [];
gui.order = ["sandbox-1"];
const serializedGuiSave = gui.serializeGameSave();
assert.deepEqual(serializedGuiSave, {
    version: SANDBOX_SAVE_VERSION,
    declarations: [{
        id: "sandbox-1",
        name: "A",
        kind: "type",
        source: "A : U",
        typeSource: "U",
        enabled: true,
        trusted: true,
        status: "valid",
        dependencies: [],
        folderId: null
    }],
    folders: [],
    order: ["sandbox-1"]
}, "the GUI must expose the same versioned snapshot used by standalone export");
assert.equal(Object.hasOwn(serializedGuiSave.declarations[0], "presentationAst"), false,
    "Worker presentation ASTs must never enter the game save");

const hit3Source = "hit SaveCube3 : U "
    + "| saveBase3 : SaveCube3 "
    + "| saveLoopA3 : saveBase3 = saveBase3 "
    + "| saveLoopB3 : saveBase3 = saveBase3 "
    + "| path2 saveFaceA3 : saveLoopA3 = saveLoopB3 "
    + "| path2 saveFaceB3 : saveLoopA3 = saveLoopB3 "
    + "| path3 saveCell3 : saveFaceA3 = saveFaceB3";
const hit3Options = { systemRuleIds: creativeSandboxSystemRuleIds };
const hit3Environment = new SandboxEnvironment(hit3Options);
const hit3Added = hit3Environment.add(hit3Source);
assert.equal(hit3Added.ok, true, hit3Added.error);

const hit3Gui = Object.create(TTSandboxGui.prototype);
hit3Gui.declarations = hit3Environment.getDeclarations();
hit3Gui.folders = [];
hit3Gui.order = hit3Gui.declarations.map(declaration => declaration.id);
hit3Gui.validationCache = undefined;
const hit3Save = hit3Gui.serializeGameSave();
const hit3SavedDeclaration = hit3Save.declarations[0];
for (const derivedField of ["hit", "inductive", "generatedNames"]) {
    assert.equal(Object.hasOwn(hit3SavedDeclaration, derivedField), false,
        `creative game saves must not persist derived HIT field ${derivedField}`);
}
assert.equal(hit3SavedDeclaration.source, hit3Source,
    "the source-only game save must retain the complete third-dimensional HIT declaration");

const persistedHit3Save = JSON.parse(JSON.stringify(hit3Save));
const hit3Worker = new SandboxWorkerSession();
const hit3Restored = hit3Worker.handle({
    id: 1,
    kind: "load",
    save: persistedHit3Save,
    options: hit3Options
});
assert.equal(hit3Restored.ok, true, hit3Restored.error);
const restoredHit3Bundle = hit3Restored.bridge?.inductives.find(bundle =>
    bundle.metadata?.typeName === "SaveCube3"
);
assert.equal(restoredHit3Bundle?.metadata?.kind, "hit3",
    "the Worker must lower and certify the source-only declaration back into a hit3 bridge");
assert.equal(restoredHit3Bundle?.metadata?.dimension, 3);
for (const [id, source] of [
    [2, "apd3_saveCell3"],
    [3, "ap3_saveCell3"]
]) {
    const checked = hit3Worker.handle({
        id,
        kind: "check",
        source,
        options: hit3Options
    });
    assert.equal(checked.ok, true,
        `${source} must be regenerated from source after the creative game-save roundtrip`);
}

const originalDocument = globalThis.document;
const originalLocalStorage = globalThis.localStorage;
const originalWindow = globalThis.window;
const originalAlert = globalThis.alert;
const originalWarn = console.warn;
const stored = new Map();
globalThis.localStorage = {
    getItem(key) { return stored.get(key) ?? null; },
    setItem(key, value) { stored.set(key, value); },
    removeItem(key) { stored.delete(key); }
};
globalThis.document = {
    getElementById() { return { innerText: "" }; },
    querySelectorAll() { return []; }
};
globalThis.window = { location: { reload() { throw new Error("unexpected reload"); } } };
globalThis.alert = message => { throw new Error(String(message)); };

function makeGame() {
    const page = {
        id: "page-1",
        name: "推理表1",
        propositions: [],
        command: { input: "", buffer: [], state: undefined }
    };
    const restoredSandboxes = [];
    const game = {
        creative: true,
        rewards: [],
        deductriums: 0,
        consumed: 0,
        destructedGates: 0,
        parcours: 1,
        maxOrd: [],
        nextOrd: [],
        ordBase: 15,
        fsGui: {
            skipRendering: true,
            enableMIFFT_RP: false,
            formalSystem: {
                deductions: {},
                propositions: page.propositions,
                consts: new Set(),
                fns: new Set(),
                verbs: new Set(),
                fastmetarules: "",
                inferencePages: { active: page, activeId: page.id, pages: [page] }
            },
            deductions: [],
            metarules: [],
            getProps() { return []; },
            updatePropositionList() { },
            updateDeductionList() { },
            updateMetaRuleList() { }
        },
        ttGui: {
            skipRendering: true,
            serializeTheoremItems() { return []; },
            serializeProofSessions() { return []; },
            resetProofAssistantForSaveLoad() { },
            restoreTheoremItems() { },
            queueProofSessionsRestore() { }
        },
        hyperGui: {
            needUpdate: false,
            world: {
                currentTile: [],
                localCamMat: { r: 1, x: 0, y: 0, z: 0 },
                currentOrd: [],
                atlasTile: { generateRotors() { } },
                reload() { },
                onPassOrd() { },
                getNamedBlockHash() { return ""; },
                getBlock() { return {}; },
                hitReward() { }
            }
        },
        sandboxGui: {
            serializeGameSave() {
                return {
                    version: SANDBOX_SAVE_VERSION,
                    declarations: [{ id: "sandbox-1", source: "A : U", enabled: true }],
                    folders: [],
                    order: ["sandbox-1"]
                };
            },
            restoreGameSave(value) {
                if (value?.version !== SANDBOX_SAVE_VERSION) throw new Error("invalid sandbox save");
                restoredSandboxes.push(value);
            }
        },
        finishAchievement() { },
        updateProgressParam() { }
    };
    return { game, restoredSandboxes };
}

try {
    const fullLoader = Object.create(GameSaveLoad.prototype);
    fullLoader.storageKey = "deductrium-creative-save";
    fullLoader.stateChangeTimer = false;
    const { game, restoredSandboxes } = makeGame();
    const fullSave = fullLoader.save(game);
    const sections = fullLoader.deserializeStr(fullSave).split("-(=)-");
    assert.equal(sections.length, 5,
        "creative GameSaveLoad.save must append the sandbox as the fifth section");
    assert.equal(JSON.parse(decodeURIComponent(sections[4])).declarations[0].source, "A : U");

    fullLoader.load(game, fullSave);
    assert.equal(restoredSandboxes.at(-1).declarations[0].source, "A : U",
        "creative GameSaveLoad.load must restore the fifth sandbox section");

    const legacySave = fullLoader.serializeStr(sections.slice(0, 4).join("-(=)-"));
    fullLoader.load(game, legacySave);
    assert.deepEqual(restoredSandboxes.at(-1), {
        version: SANDBOX_SAVE_VERSION,
        declarations: [],
        folders: [],
        order: []
    }, "a legacy four-section creative save must explicitly restore an empty sandbox");

    const invalidSections = [...sections];
    invalidSections[4] = encodeURIComponent(JSON.stringify({ version: 999, declarations: [] }));
    const invalidSave = fullLoader.serializeStr(invalidSections.join("-(=)-"));
    const alertMessages = [];
    let rollbackReloads = 0;
    globalThis.alert = message => alertMessages.push(String(message));
    globalThis.window.location.reload = () => { rollbackReloads++; };
    console.warn = () => undefined;
    fullLoader.load(game, invalidSave);
    console.warn = originalWarn;
    assert.equal(alertMessages.length, 1);
    assert.equal(rollbackReloads, 1);
    assert.equal(restoredSandboxes.at(-1).declarations[0].source, "A : U",
        "an invalid sandbox section must roll the complete game save back atomically");

    const survivalLoader = Object.create(GameSaveLoad.prototype);
    survivalLoader.storageKey = "deductrium-save";
    survivalLoader.stateChangeTimer = false;
    const { game: survivalGame } = makeGame();
    survivalGame.creative = false;
    const survivalSections = survivalLoader.deserializeStr(survivalLoader.save(survivalGame)).split("-(=)-");
    assert.equal(survivalSections.length, 4,
        "survival saves must not serialize or expose a sandbox section");
} finally {
    globalThis.document = originalDocument;
    globalThis.localStorage = originalLocalStorage;
    globalThis.window = originalWindow;
    globalThis.alert = originalAlert;
    console.warn = originalWarn;
}

console.log("sandbox creative game-save integration regression passed");
