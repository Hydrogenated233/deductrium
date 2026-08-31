import assert from "node:assert/strict";

import { GameSaveLoad } from "../js/saveload.js";
import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { TTGui } from "../js/tt/gui.js";
import { initTypeSystem } from "../js/tt/initial.js";
import {
    SandboxEnvironment,
    creativeSandboxSystemRuleIds
} from "../js/tt/sandbox.js";
import {
    TTSandboxGui,
    runAfterSandboxReady
} from "../js/tt/sandbox-gui.js";

const originalConfirm = globalThis.confirm;
const originalLocalStorage = globalThis.localStorage;
const originalWindow = globalThis.window;
const originalSetTimeout = globalThis.setTimeout;
const originalClearTimeout = globalThis.clearTimeout;

const scheduled = new Map();
let nextTimerId = 1;
const removedKeys = [];
let reloads = 0;

globalThis.confirm = () => true;
globalThis.localStorage = {
    getItem() { return null; },
    setItem() { },
    removeItem(key) { removedKeys.push(key); }
};
globalThis.window = {
    location: {
        reload() { reloads++; }
    }
};
globalThis.setTimeout = (callback, delay) => {
    const id = nextTimerId++;
    scheduled.set(id, { callback, delay });
    return id;
};
globalThis.clearTimeout = id => scheduled.delete(id);

try {
    const loader = Object.create(GameSaveLoad.prototype);
    loader.storageKey = "deductrium-creative-save";
    loader.stateChangeTimer = false;
    loader.timeOut = 3_000;
    let saveCalls = 0;
    let sandboxClears = 0;
    loader.save = () => { saveCalls++; };
    const game = {
        sandboxGui: {
            clearPersistedSave() { sandboxClears++; }
        }
    };

    loader.stateChange(game);
    assert.notEqual(loader.stateChangeTimer, false);
    loader.reset(game);
    assert.equal(loader.stateChangeTimer, false,
        "reset must cancel a pending autosave before navigation");
    assert.equal(scheduled.size, 0);
    assert.equal(sandboxClears, 1);
    assert.deepEqual(removedKeys, ["deductrium-creative-save"]);
    assert.equal(reloads, 1);

    loader.stateChange(game);
    loader.flush(game);
    assert.equal(saveCalls, 0,
        "pagehide/state-change callbacks after reset must not recreate the deleted save");

    const events = [];
    const gui = Object.create(TTSandboxGui.prototype);
    gui.input = { value: "A : U" };
    gui.declarations = [];
    gui.folders = [];
    gui.order = [];
    gui.pendingFolderId = null;
    gui.syncWorkspaceFromState = () => gui.workspace;
    gui.persist = () => events.push("persist");
    gui.render = () => events.push("render");
    gui.validate = async () => { events.push("validate"); };
    gui.invalidateBridge = () => events.push("invalidate-bridge");
    gui.addToFolder(null);
    assert.deepEqual(events, ["persist", "render", "invalidate-bridge", "validate"],
        "new declaration source must be persisted before the previous bridge is revoked and revalidated");

    let releaseValidation;
    const delayedValidation = new Promise(resolve => { releaseValidation = resolve; });
    const bridgeEvents = [];
    const delayedGui = Object.create(TTSandboxGui.prototype);
    delayedGui.persistenceSuspended = false;
    delayedGui.validationRequest = 0;
    delayedGui.worker = {
        async validate() {
            bridgeEvents.push("worker-start");
            return delayedValidation;
        }
    };
    delayedGui.toSave = () => ({ version: 1, declarations: [], folders: [], order: [] });
    delayedGui.setStatus = () => undefined;
    delayedGui.syncWorkspaceFromState = () => undefined;
    delayedGui.persist = () => undefined;
    delayedGui.render = () => undefined;
    delayedGui.onAxiomsChange = (bridge, options) => bridgeEvents.push(
        `${bridge.axioms[0]?.[0] ?? "empty"}:${String(options?.revalidate)}`
    );
    const pendingValidation = delayedGui.requestValidation();
    assert.deepEqual(bridgeEvents, ["empty:false", "worker-start"],
        "a stale bridge must be revoked synchronously without starting theorem revalidation");
    releaseValidation({
        ok: true,
        declarations: [],
        bridge: { axioms: [["Fresh", { type: "var", name: "U", nodes: [] }]], inductives: [], definitions: [] },
        validationStats: { checkedDeclarations: 0, replayedDeclarations: 0, validatedThrough: 0 }
    });
    await pendingValidation;
    assert.deepEqual(bridgeEvents, ["empty:false", "worker-start", "Fresh:true"],
        "only the completed validation may publish and revalidate the replacement bridge");

    const parser = new ASTParser();
    const createDeferredTypeGui = () => {
        const gui = Object.create(TTGui.prototype);
        gui.creativeMode = true;
        gui.skipRendering = true;
        gui.core = new Core();
        gui.unlockedTypes = new Set(initTypeSystem().map(rule => rule.id));
        gui.inferDisplayMode = "_";
        gui.disableSimpleEq = false;
        gui.disableSimpleFn = false;
        gui.sandboxAxioms = [];
        gui.sandboxAxiomNames = new Set();
        gui.sandboxInductives = [];
        gui.sandboxDefinitions = [];
        gui.sandboxDefinitionNames = new Set();
        gui.definitionRevision = 0;
        gui.coreWorkerStateRevision = 0;
        gui.invalidateHottDefCtxt = () => undefined;
        gui.initTypeList();
        return gui;
    };
    const deferredTypeGui = createDeferredTypeGui();

    const indexedSandbox = new SandboxEnvironment({
        systemRuleIds: creativeSandboxSystemRuleIds
    });
    indexedSandbox.add("BaseStartup : U");
    indexedSandbox.add(
        "inductive VecStartup (A : U) [n : nat] : U "
        + "| vnilStartup : VecStartup A 0 "
        + "| vconsStartup : Pn:nat,A -> VecStartup A n -> VecStartup A (succ n)"
    );
    const indexedResult = indexedSandbox.add(
        "inductive BoxStartup (x : BaseStartup) : U "
        + "| boxStartup : BoxStartup x"
    );
    assert.equal(indexedResult.ok, true, indexedResult.error);
    assert.doesNotThrow(
        () => deferredTypeGui.setSandboxAxioms(indexedResult.bridge, { revalidate: true }),
        "the creative main Core must have its unlocked types before the first sandbox bridge publication"
    );
    assert.equal(deferredTypeGui.core.hasConst("VecStartup"), true);
    assert.equal(deferredTypeGui.core.hasConst("BoxStartup"), true,
        "sandbox axioms must be installed before inductives that depend on them");

    const axiomDefinitionInductive = new SandboxEnvironment({
        systemRuleIds: creativeSandboxSystemRuleIds
    });
    assert.equal(axiomDefinitionInductive.add("A : U").ok, true);
    assert.equal(axiomDefinitionInductive.add("Alias := A").ok, true);
    const aliasBoxResult = axiomDefinitionInductive.add(
        "inductive BoxA (x : Alias) : U | boxA : BoxA x"
    );
    assert.equal(aliasBoxResult.ok, true, aliasBoxResult.error);

    const inductiveDefinitionInductive = new SandboxEnvironment({
        systemRuleIds: creativeSandboxSystemRuleIds
    });
    const chainBaseResult = inductiveDefinitionInductive.add(
        "inductive ChainBase : U | chainBase : ChainBase"
    );
    assert.equal(chainBaseResult.ok, true, chainBaseResult.error);
    const chainAliasResult = inductiveDefinitionInductive.add("ChainAlias := ChainBase");
    assert.equal(chainAliasResult.ok, true, chainAliasResult.error);
    const wrappedSeedResult = inductiveDefinitionInductive.add(
        "inductive ChainWrap (x : ChainAlias) : U | chainWrap : ChainWrap x"
    );
    assert.equal(wrappedSeedResult.ok, true, wrappedSeedResult.error);

    const crossCategoryFailures = [];
    for (const testCase of [
        {
            label: "axiom -> definition -> inductive",
            bridge: aliasBoxResult.bridge,
            names: ["A", "Alias", "BoxA"]
        },
        {
            label: "inductive -> definition -> inductive",
            bridge: wrappedSeedResult.bridge,
            names: ["ChainBase", "ChainAlias", "ChainWrap"]
        }
    ]) {
        const gui = createDeferredTypeGui();
        try {
            gui.setSandboxAxioms(testCase.bridge, { revalidate: true });
            for (const name of testCase.names) {
                assert.equal(gui.core.hasConst(name), true, `${name} must be published`);
            }
        } catch (error) {
            crossCategoryFailures.push(
                `${testCase.label}: ${error instanceof Error ? error.message : String(error)}`
            );
        }
    }
    assert.deepEqual(crossCategoryFailures, [],
        `sandbox bridge publication must preserve cross-category declaration order:\n${crossCategoryFailures.join("\n")}`);

    for (const testCase of [
        { bridge: aliasBoxResult.bridge, finalName: "BoxA" },
        { bridge: wrappedSeedResult.bridge, finalName: "ChainWrap" }
    ]) {
        const workerEngine = new TTCoreEngine();
        assert.doesNotThrow(() => workerEngine.configure({
            unlockedTypes: creativeSandboxSystemRuleIds,
            trustedAxioms: testCase.bridge.axioms,
            trustedInductives: testCase.bridge.inductives,
            trustedDefinitions: testCase.bridge.definitions,
            trustedDeclarationOrder: testCase.bridge.order
        }), "core and proof-assistant workers must install the same ordered bridge");
        assert.equal(workerEngine.core.hasConst(testCase.finalName), true);
    }
    assert.throws(() => new TTCoreEngine().configure({
        unlockedTypes: creativeSandboxSystemRuleIds,
        trustedAxioms: aliasBoxResult.bridge.axioms,
        trustedInductives: aliasBoxResult.bridge.inductives,
        trustedDefinitions: aliasBoxResult.bridge.definitions,
        trustedDeclarationOrder: []
    }), /顺序缺少声明/,
    "an explicit incomplete order must fail instead of silently reordering declarations");

    const theoremInputs = [{}, {}];
    const typeLayerEvents = [];
    const typeGui = Object.create(TTGui.prototype);
    typeGui.creativeMode = true;
    typeGui.core = new Core();
    typeGui.core.setSystemType("OldSandbox", parser.parse("U"));
    typeGui.sandboxAxioms = [["OldSandbox", parser.parse("U")]];
    typeGui.sandboxAxiomNames = new Set(["OldSandbox"]);
    typeGui.sandboxInductives = [];
    typeGui.sandboxDefinitions = [];
    typeGui.sandboxDefinitionNames = new Set();
    typeGui.userDefinedConsts = [["derived", parser.parse("OldSandbox")], null];
    typeGui.skipRendering = false;
    typeGui.definitionRevision = 0;
    typeGui.coreWorkerStateRevision = 0;
    typeGui.gateQueryCache = { clear: () => typeLayerEvents.push("clear-gates") };
    typeGui.getInhabitatArray = () => theoremInputs;
    typeGui.invalidateHottDefCtxt = () => typeLayerEvents.push("invalidate-context");
    typeGui.invalidateTheoremChecks = () => typeLayerEvents.push("invalidate-theorems");
    typeGui.clearUserDefinitionContext = () => typeLayerEvents.push("clear-user-definitions");
    typeGui.refreshUserConstNames = () => typeLayerEvents.push("refresh-user-names");
    typeGui.updateTypeList = () => typeLayerEvents.push("render-types");
    typeGui.revalidateTheorems = () => typeLayerEvents.push("revalidate-theorems");
    typeGui.restorePendingProofSessionsWhenReady = () => {
        typeLayerEvents.push("restore-proof-sessions");
    };

    typeGui.setSandboxAxioms({ axioms: [], inductives: [], definitions: [] }, {
        revalidate: false
    });
    assert.equal(typeGui.core.hasConst("OldSandbox"), false,
        "provisional revocation must remove old sandbox names synchronously");
    assert.equal(typeLayerEvents.includes("revalidate-theorems"), false,
        "provisional revocation must not start theorem validation");
    assert.equal(typeLayerEvents.includes("invalidate-theorems"), true);
    assert.equal(theoremInputs.every(input => input.validationInvalidated === true), true,
        "theorem rows must stop advertising results derived from the revoked bridge");

    typeGui.setSandboxAxioms({
        axioms: [["FreshSandbox", parser.parse("U")]],
        inductives: [],
        definitions: []
    }, { revalidate: true });
    assert.equal(typeGui.core.hasConst("FreshSandbox"), true,
        "the final bridge must install its validated names");
    assert.equal(typeLayerEvents.filter(event => event === "revalidate-theorems").length, 1,
        "the final bridge must start exactly one theorem revalidation");
    assert.equal(typeLayerEvents.filter(event => event === "restore-proof-sessions").length, 1);

    const bridges = [];
    const failureStatuses = [];
    let fallbackCalls = 0;
    const failingGui = Object.create(TTSandboxGui.prototype);
    failingGui.persistenceSuspended = false;
    failingGui.validationRequest = 0;
    failingGui.worker = { validate: async () => { throw new Error("worker failed"); } };
    failingGui.getFallback = () => {
        fallbackCalls++;
        throw new Error("main-thread fallback must not run");
    };
    failingGui.toSave = () => ({ version: 1, declarations: [], folders: [], order: [] });
    failingGui.setStatus = (message, failed) => failureStatuses.push({ message, failed });
    failingGui.onAxiomsChange = (bridge, options) => bridges.push({ bridge, options });
    await failingGui.validate();
    assert.equal(fallbackCalls, 0,
        "bulk validation must never fall back to the browser main thread");
    assert.deepEqual(bridges.at(-1), {
        bridge: { axioms: [], inductives: [], definitions: [] },
        options: { revalidate: true }
    },
        "a failed validation must revoke the previous trusted bridge");
    assert.deepEqual(failureStatuses, [
        { message: "正在校验沙盒声明…", failed: false },
        { message: "沙盒 Worker 校验失败：worker failed", failed: true }
    ], "worker failure should remain explicit while preserving the editable source state");

    let releaseReady;
    const ready = new Promise(resolve => { releaseReady = resolve; });
    const startupEvents = [];
    const startup = runAfterSandboxReady(
        { whenReady: () => ready },
        () => startupEvents.push("type-validation")
    );
    await Promise.resolve();
    assert.deepEqual(startupEvents, [],
        "type-layer validation must wait for the final sandbox bridge");
    releaseReady();
    await startup;
    assert.deepEqual(startupEvents, ["type-validation"]);
} finally {
    globalThis.confirm = originalConfirm;
    globalThis.localStorage = originalLocalStorage;
    globalThis.window = originalWindow;
    globalThis.setTimeout = originalSetTimeout;
    globalThis.clearTimeout = originalClearTimeout;
}

console.log("sandbox save/startup lifecycle regression passed");
