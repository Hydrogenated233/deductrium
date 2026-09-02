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

console.log("sandbox GUI error-boundary regression passed");
