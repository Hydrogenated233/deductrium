import assert from "node:assert/strict";

import {
    TTSandboxGui,
    normalizeSandboxCheckInput
} from "../js/tt/sandbox-gui.js";
import { SandboxWorkerCancelledError } from "../js/tt/sandbox-worker-client.js";
import { hasLegacySurfaceSyntax } from "../js/tt/surface-syntax-migration.js";

const empty = { axioms: [], inductives: [], definitions: [] };
const trusted = {
    axioms: [["Trusted", { type: "var", name: "U", nodes: [] }]],
    inductives: [],
    definitions: []
};

// The expression-check input may contain a pasted alias before a keyboard
// Space event runs. It must normalize `\\*` to `▪` before the strict legacy
// guard, while still rejecting the old bare `*` spelling.
assert.equal(normalizeSandboxCheckInput(" f \\* g "), "f ▪ g");
assert.equal(hasLegacySurfaceSyntax(normalizeSandboxCheckInput("f \\* g")), false);
assert.equal(hasLegacySurfaceSyntax(normalizeSandboxCheckInput("f * g")), true);

function deferredHandle(requestId, handles) {
    let resolve;
    let reject;
    let cancelled = false;
    const promise = new Promise((nextResolve, nextReject) => {
        resolve = nextResolve;
        reject = nextReject;
    });
    const handle = {
        requestId,
        promise,
        resolve,
        reject,
        cancel() {
            if (cancelled) return false;
            cancelled = true;
            reject(new SandboxWorkerCancelledError());
            return true;
        },
        get cancelled() { return cancelled; }
    };
    handles.push(handle);
    return handle;
}

function makeGui(worker, events, statuses) {
    const gui = Object.create(TTSandboxGui.prototype);
    gui.persistenceSuspended = false;
    gui.validationRequest = 0;
    gui.validationPromise = Promise.resolve();
    gui.validationHandle = null;
    gui.validationCanRestoreBridge = false;
    gui.lastTrustedBridge = trusted;
    gui.worker = worker;
    gui.toSave = () => ({ version: 1, declarations: [], folders: [], order: [] });
    gui.setStatus = (message, failed) => statuses.push({ message, failed });
    gui.syncWorkspaceFromState = () => undefined;
    gui.persist = () => undefined;
    gui.render = () => undefined;
    gui.validateButton = { disabled: false };
    gui.stopValidationButton = { disabled: true };
    gui.root = { classList: { toggle() {} } };
    gui.onAxiomsChange = (bridge, options) => events.push({ bridge, options });
    return gui;
}

// A manual re-check does not revoke the currently trusted bridge.  Stopping
// it restores that bridge and leaves the editor ready for another request.
{
    const handles = [];
    const worker = {
        validateRequest() {
            return deferredHandle(1, handles);
        },
        validate() { throw new Error("legacy validate path should not run"); }
    };
    const events = [];
    const statuses = [];
    const gui = makeGui(worker, events, statuses);
    const pending = gui.requestValidation(false);
    assert.equal(gui.validateButton.disabled, true);
    assert.equal(gui.stopValidationButton.disabled, false);
    assert.equal(gui.cancelValidation(), true);
    await pending;
    assert.equal(handles[0].cancelled, true);
    assert.deepEqual(events, [],
        "manual cancellation must preserve the last trusted bridge without republishing or clearing it");
    assert.deepEqual(statuses.at(-1), {
        message: "沙盒校验已取消，保留上次可信声明",
        failed: false
    });
    assert.equal(gui.validateButton.disabled, false);
    assert.equal(gui.stopValidationButton.disabled, true);
}

// A source/order/enable mutation revokes the old bridge before checking.  A
// later cancellation must not put that stale bridge back into the type layer.
{
    const handles = [];
    const worker = { validateRequest() { return deferredHandle(1, handles); } };
    const events = [];
    const statuses = [];
    const gui = makeGui(worker, events, statuses);
    const pending = gui.requestValidation(true);
    assert.deepEqual(events, [{ bridge: empty, options: { revalidate: false } }]);
    assert.equal(gui.cancelValidation(), true);
    await pending;
    assert.deepEqual(events, [{ bridge: empty, options: { revalidate: false } }],
        "cancelling a validation for a changed save must not restore the stale bridge");
    assert.equal(statuses.at(-1).message, "沙盒校验已取消");
}

// A newer request cancels the stale Worker request.  Its result is ignored;
// only the newer result may publish a replacement bridge.
{
    const handles = [];
    const worker = {
        validateRequest() {
            return deferredHandle(handles.length + 1, handles);
        }
    };
    const events = [];
    const statuses = [];
    const gui = makeGui(worker, events, statuses);
    const first = gui.requestValidation(false);
    const second = gui.requestValidation(false);
    assert.equal(handles[0].cancelled, true);
    handles[1].resolve({
        ok: true,
        declarations: [],
        bridge: { axioms: [["Fresh", { type: "var", name: "U", nodes: [] }]], inductives: [], definitions: [] },
        validationStats: { checkedDeclarations: 0, replayedDeclarations: 0, validatedThrough: 0 }
    });
    await Promise.all([first, second]);
    assert.deepEqual(events, [{
        bridge: { axioms: [["Fresh", { type: "var", name: "U", nodes: [] }]], inductives: [], definitions: [] },
        options: { revalidate: true }
    }]);
    assert.equal(gui.stopValidationButton.disabled, true);
}

// A bounded manual validation has the same bridge-preservation rule as an
// explicit stop: the partial result is never published, and the prior bridge
// remains available for the current type layer.
{
    const worker = {
        validateRequest() {
            return {
                requestId: 1,
                promise: Promise.resolve({
                    ok: false,
                    status: "budget-exhausted",
                    error: "沙盒验证资源上限：验证步骤过多",
                    declarations: [],
                    validationStats: { checkedDeclarations: 0, replayedDeclarations: 0, validatedThrough: 0 }
                }),
                cancel() { return false; }
            };
        }
    };
    const events = [];
    const statuses = [];
    const gui = makeGui(worker, events, statuses);
    await gui.requestValidation(false);
    assert.deepEqual(events, [],
        "a budget-exhausted manual validation must not replace the trusted bridge");
    assert.match(statuses.at(-1).message, /资源上限/);
    assert.equal(statuses.at(-1).failed, true);
    assert.equal(gui.lastTrustedBridge, trusted);
}

console.log("sandbox GUI validation cancellation regression passed");
