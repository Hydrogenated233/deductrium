import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

import { TTSandboxGui } from "../js/tt/sandbox-gui.js";

const save = {
    version: 1,
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
};

const navigatorDescriptor = Object.getOwnPropertyDescriptor(globalThis, "navigator");
try {
    let copied = "";
    Object.defineProperty(globalThis, "navigator", {
        configurable: true,
        value: { clipboard: { writeText: async value => { copied = value; } } }
    });
    const statuses = [];
    const gui = Object.create(TTSandboxGui.prototype);
    gui.toSave = () => save;
    gui.setStatus = (message, error) => statuses.push({ message, error });
    await gui.copySave();
    assert.deepEqual(JSON.parse(copied), save,
        "copy must use the same versioned JSON package as export");
    assert.deepEqual(statuses.at(-1), { message: "沙盒包已复制", error: false });
} finally {
    if (navigatorDescriptor) Object.defineProperty(globalThis, "navigator", navigatorDescriptor);
    else delete globalThis.navigator;
}

const confirmDescriptor = Object.getOwnPropertyDescriptor(globalThis, "confirm");
try {
    Object.defineProperty(globalThis, "confirm", {
        configurable: true,
        value: () => true
    });
    const events = [];
    const gui = Object.create(TTSandboxGui.prototype);
    gui.declarations = [...save.declarations];
    gui.folders = [{ kind: "folder", id: "folder-1", name: "F", length: 1, open: true, disabled: false }];
    gui.order = ["folder-1", "sandbox-1"];
    gui.pendingFolderId = "folder-1";
    gui.fallback = {};
    gui.validationRequest = 4;
    gui.validationHandle = {};
    gui.validationCanRestoreBridge = true;
    gui.cancelValidation = announce => events.push(["cancel", announce]);
    gui.worker = { terminate: () => events.push(["terminate"]) };
    gui.updateValidationControls = running => events.push(["controls", running]);
    gui.workspace = { replace: items => events.push(["workspace", items]) };
    gui.onAxiomsChange = (bridge, options) => events.push(["bridge", bridge, options]);
    gui.persist = () => events.push(["persist"]);
    gui.render = () => events.push(["render"]);
    gui.setStatus = (message, error) => events.push(["status", message, error]);

    gui.clearWorkspace();
    assert.deepEqual(gui.declarations, []);
    assert.deepEqual(gui.folders, []);
    assert.deepEqual(gui.order, []);
    assert.equal(gui.pendingFolderId, null);
    assert.equal(gui.fallback, null);
    assert.equal(gui.validationRequest, 5);
    assert.equal(gui.validationHandle, null);
    assert.equal(gui.validationCanRestoreBridge, false);
    assert.deepEqual(events.find(event => event[0] === "bridge"), [
        "bridge",
        { axioms: [], inductives: [], definitions: [] },
        { revalidate: true }
    ]);
    assert.deepEqual(events.slice(-3), [
        ["persist"],
        ["render"],
        ["status", "沙盒已清空", false]
    ]);
} finally {
    if (confirmDescriptor) Object.defineProperty(globalThis, "confirm", confirmDescriptor);
    else delete globalThis.confirm;
}

// A bridge callback failure must not leave the cleared source state rendered
// or persisted as the old workspace.
try {
    Object.defineProperty(globalThis, "confirm", {
        configurable: true,
        value: () => true
    });
    const events = [];
    const gui = Object.create(TTSandboxGui.prototype);
    gui.declarations = [...save.declarations];
    gui.folders = [];
    gui.order = ["sandbox-1"];
    gui.pendingFolderId = null;
    gui.fallback = null;
    gui.validationRequest = 0;
    gui.validationHandle = null;
    gui.validationCanRestoreBridge = false;
    gui.cancelValidation = () => false;
    gui.worker = { terminate() {} };
    gui.updateValidationControls = () => undefined;
    gui.workspace = { replace() {} };
    gui.onAxiomsChange = () => { throw new Error("bridge failed"); };
    gui.persist = () => events.push("persist");
    gui.render = () => events.push("render");
    gui.setStatus = (message, error) => events.push({ message, error });

    gui.clearWorkspace();
    assert.deepEqual(gui.declarations, []);
    assert.deepEqual(events.slice(0, 2), ["persist", "render"]);
    assert.deepEqual(events.at(-1), {
        message: "沙盒已清空，但撤回类型层声明失败：bridge failed",
        error: true
    });
} finally {
    if (confirmDescriptor) Object.defineProperty(globalThis, "confirm", confirmDescriptor);
    else delete globalThis.confirm;
}

const html = await readFile(new URL("../index.html", import.meta.url), "utf8");
assert.match(html, /id="sandbox-copy"/);
assert.match(html, /id="sandbox-clear"[^>]*class="danger"|class="danger"[^>]*id="sandbox-clear"/);

console.log("sandbox package copy/clear regression passed");
