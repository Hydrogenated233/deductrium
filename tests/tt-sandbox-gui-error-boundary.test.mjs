import assert from "node:assert/strict";

import { TTSandboxGui } from "../js/tt/sandbox-gui.js";

const workerBridgeEvents = [];
const workerStatuses = [];
const workerFailureGui = Object.create(TTSandboxGui.prototype);
workerFailureGui.persistenceSuspended = false;
workerFailureGui.validationRequest = 0;
workerFailureGui.worker = {
    async validate() {
        throw new Error("worker failed");
    }
};
workerFailureGui.toSave = () => ({ version: 1, declarations: [], folders: [], order: [] });
workerFailureGui.setStatus = (message, failed) => workerStatuses.push({ message, failed });
workerFailureGui.onAxiomsChange = (bridge, options) => workerBridgeEvents.push({ bridge, options });

await workerFailureGui.validate();

assert.deepEqual(workerBridgeEvents, [{
    bridge: { axioms: [], inductives: [], definitions: [] },
    options: { revalidate: true }
}], "a Worker validation failure must revoke the previously validated bridge");
assert.deepEqual(workerStatuses, [
    { message: "正在校验沙盒声明…", failed: false },
    { message: "沙盒 Worker 校验失败：worker failed", failed: true }
], "Worker validation errors must retain their distinct error boundary");

const bridgeEvents = [];
const statuses = [];
const gui = Object.create(TTSandboxGui.prototype);
const previousDeclarations = [{ id: "old", source: "Old : U" }];
const previousValidationCache = { version: 1, semanticEpoch: "old", preludeKey: "old", entries: [] };
gui.persistenceSuspended = false;
gui.validationRequest = 0;
gui.declarations = previousDeclarations;
gui.validationCache = previousValidationCache;
gui.worker = {
    async validate() {
        return {
            ok: true,
            declarations: [{ id: "new", source: "Published : U" }],
            validationCache: { version: 1, semanticEpoch: "new", preludeKey: "new", entries: [] },
            bridge: {
                axioms: [["Published", { type: "var", name: "U", nodes: [] }]],
                inductives: [],
                definitions: []
            },
            validationStats: {
                checkedDeclarations: 0,
                replayedDeclarations: 0,
                validatedThrough: 0
            }
        };
    }
};
gui.toSave = () => ({ version: 1, declarations: [], folders: [], order: [] });
gui.setStatus = (message, failed) => statuses.push({ message, failed });
gui.syncWorkspaceFromState = () => undefined;
gui.persist = () => undefined;
gui.render = () => undefined;
gui.onAxiomsChange = (bridge, options) => {
    const name = bridge.axioms[0]?.[0] ?? "empty";
    bridgeEvents.push(`${name}:${String(options?.revalidate)}`);
    if (name === "Published") throw new Error("bridge failed");
};

await gui.validate();

assert.deepEqual(bridgeEvents, ["Published:true", "empty:true"],
    "a failed bridge publication must revoke any partially published type-layer state");
assert.deepEqual(statuses, [
    { message: "正在校验沙盒声明…", failed: false },
    { message: "沙盒类型层发布失败：bridge failed", failed: true }
], "bridge publication errors must not be reported as Worker validation failures");
assert.equal(gui.declarations, previousDeclarations,
    "a failed bridge publication must not commit the Worker's declaration generation");
assert.equal(gui.validationCache, previousValidationCache,
    "a failed bridge publication must not commit the Worker's validation cache");

// An invalid validation result may carry a useful-prefix bridge for
// diagnostics, but GUI publication must revoke it instead of installing a
// partially trusted projection.
const invalidBridgeEvents = [];
const invalidStatuses = [];
const invalidLifecycle = [];
const invalidGui = Object.create(TTSandboxGui.prototype);
invalidGui.persistenceSuspended = false;
invalidGui.validationRequest = 0;
invalidGui.declarations = [{ id: "bad", status: "unchecked" }];
invalidGui.validationCache = { version: 1, entries: ["stale"] };
invalidGui.worker = {
    async validate() {
        return {
            ok: false,
            status: "invalid",
            error: "未知的沙盒名称：Missing",
            declarations: [{ id: "bad", status: "invalid" }],
            bridge: {
                axioms: [["Prefix", { type: "var", name: "U", nodes: [] }]],
                inductives: [],
                definitions: []
            },
            validationStats: {
                checkedDeclarations: 1,
                replayedDeclarations: 0,
                validatedThrough: 2
            }
        };
    }
};
invalidGui.toSave = () => ({ version: 1, declarations: [], folders: [], order: [] });
invalidGui.setStatus = (message, failed) => invalidStatuses.push({ message, failed });
invalidGui.syncWorkspaceFromState = () => invalidLifecycle.push("sync");
invalidGui.persist = () => invalidLifecycle.push("persist");
invalidGui.render = () => invalidLifecycle.push("render");
invalidGui.updateValidationControls = () => undefined;
invalidGui.onAxiomsChange = (bridge, options) => invalidBridgeEvents.push({ bridge, options });
await invalidGui.validate();
assert.deepEqual(invalidBridgeEvents, [{
    bridge: { axioms: [], inductives: [], definitions: [] },
    options: { revalidate: true }
}], "invalid validation must revoke rather than publish a partial bridge");
assert.deepEqual(invalidStatuses.at(-1), {
    message: "沙盒校验失败：未知的沙盒名称：Missing",
    failed: true
});
assert.deepEqual(invalidGui.declarations, [{ id: "bad", status: "invalid" }],
    "invalid validation must retain the Worker's per-row diagnostics");
assert.equal(invalidGui.validationCache, undefined,
    "invalid validation must discard the stale or partial validation cache");
assert.deepEqual(invalidLifecycle, ["sync", "persist", "render"]);

console.log("sandbox GUI error-boundary regression passed");
