import assert from "node:assert/strict";

import { sandboxValidationSemanticsKey } from "../js/tt/sandbox.js";
import { TTSandboxGui } from "../js/tt/sandbox-gui.js";

const validationCache = Object.freeze({
    version: 1,
    semanticEpoch: "gui-cache-mutation-test",
    preludeKey: "prelude",
    entries: Object.freeze([])
});

{
    const base = {
        version: 1,
        declarations: [declaration()],
        folders: [],
        order: ["sandbox-1"]
    };
    const enabledFolder = structuredClone(base);
    enabledFolder.folders = [{
        kind: "folder",
        id: "folder",
        name: "Folder",
        length: 1,
        open: false,
        disabled: false
    }];
    enabledFolder.order = ["folder", "sandbox-1"];
    assert.equal(sandboxValidationSemanticsKey(enabledFolder), sandboxValidationSemanticsKey(base),
        "enabled folder presentation must not change validation semantics");

    const disabledFolder = structuredClone(enabledFolder);
    disabledFolder.folders[0].disabled = true;
    assert.notEqual(sandboxValidationSemanticsKey(disabledFolder), sandboxValidationSemanticsKey(base),
        "recursive folder disable state must change validation semantics");
}

class FakeClassList {
    names = new Set();

    add(...names) { for (const name of names) this.names.add(name); }
    remove(...names) { for (const name of names) this.names.delete(name); }
    contains(name) { return this.names.has(name); }
    toggle(name, force) {
        if (force === undefined ? !this.names.has(name) : force) this.names.add(name);
        else this.names.delete(name);
    }
}

class FakeElement {
    constructor(tagName) {
        this.tagName = String(tagName).toUpperCase();
        this.dataset = {};
        this.classList = new FakeClassList();
        this.listeners = new Map();
        this.children = [];
        this.value = "";
    }

    set className(value) {
        this.classList.names = new Set(String(value).split(/\s+/).filter(Boolean));
    }
    get className() { return [...this.classList.names].join(" "); }
    addEventListener(type, listener) {
        const listeners = this.listeners.get(type) ?? [];
        listeners.push(listener);
        this.listeners.set(type, listeners);
    }
    dispatch(type, event = {}) {
        for (const listener of this.listeners.get(type) ?? []) listener(event);
    }
    appendChild(child) { this.children.push(child); return child; }
    append(...children) { this.children.push(...children); }
    replaceChildren(...children) { this.children = [...children]; }
    focus() {}
    select() {}
}

function declaration(id = "sandbox-1", source = "A : U") {
    return {
        id,
        name: id === "sandbox-1" ? "A" : "B",
        kind: "type",
        source,
        typeSource: "U",
        enabled: true,
        trusted: true,
        status: "valid",
        dependencies: [],
        folderId: null
    };
}

function makeGui(events = []) {
    const gui = Object.create(TTSandboxGui.prototype);
    gui.persistenceSuspended = false;
    gui.environmentOptions = { validationMaxSourceChars: 100_000 };
    gui.declarations = [declaration()];
    gui.folders = [];
    gui.order = ["sandbox-1"];
    gui.validationCache = validationCache;
    gui.pendingValidationCache = undefined;
    gui.dragger = { attachIdxListener() {} };
    gui.renderDeclarationDisplay = () => undefined;
    gui.syncWorkspaceFromState = () => gui.workspace;
    gui.applyWorkspaceSnapshot = snapshot => {
        gui.order = snapshot.map(item => item.id);
    };
    gui.persist = () => events.push("persist");
    gui.render = () => events.push("render");
    gui.requestValidation = () => {
        events.push("validate");
        return Promise.resolve();
    };
    gui.setStatus = (message, failed) => events.push({ message, failed });
    return gui;
}

function assertCachePresent(gui, message) {
    const save = gui.serializeGameSave();
    assert.equal(save.validationCache, validationCache, message);
}

function assertCacheCleared(gui, message) {
    const save = gui.serializeGameSave();
    assert.equal(Object.hasOwn(save, "validationCache"), false, message);
}

const previousDocument = globalThis.document;
const previousPrompt = globalThis.prompt;
let created = [];
globalThis.document = {
    createElement(tagName) {
        const element = new FakeElement(tagName);
        created.push(element);
        return element;
    },
    createTextNode(text) {
        const node = new FakeElement("#text");
        node.textContent = text;
        return node;
    }
};

try {
    // Editing source changes the validation signature immediately. Autosave
    // must not retain the formerly certified cache while the Worker is pending.
    {
        created = [];
        const events = [];
        const gui = makeGui(events);
        assertCachePresent(gui, "the fixture must begin with a certified cache");
        gui.createDeclarationRow(gui.declarations[0]);
        const source = created.find(element => element.classList.contains("sandbox-source"));
        assert.ok(source);
        source.value = "A : U0";
        source.dispatch("keydown", { key: "Enter", preventDefault() {} });
        assertCacheCleared(gui,
            "editing declaration source must remove the stale validation cache before autosave");
        assert.deepEqual(events, ["persist", "validate"]);
    }

    // Enable state participates in validation and bridge publication, so a
    // toggle invalidates the old cache even when the source text is unchanged.
    {
        created = [];
        const events = [];
        const gui = makeGui(events);
        gui.createDeclarationRow(gui.declarations[0]);
        const enabled = created.find(element =>
            element.tagName === "INPUT" && element.type === "checkbox"
        );
        assert.ok(enabled);
        enabled.checked = false;
        enabled.dispatch("change");
        assertCacheCleared(gui,
            "enabling or disabling a declaration must remove the stale validation cache");
        assert.deepEqual(events, ["persist", "validate"]);
    }

    // Reordering changes the validated prefix chain. The old cache must not be
    // serialized during the replacement Worker request.
    {
        const events = [];
        const gui = makeGui(events);
        gui.declarations.push(declaration("sandbox-2", "B : U"));
        gui.order.push("sandbox-2");
        gui.workspace = {
            move() {
                return {
                    changed: true,
                    snapshot: [
                        { kind: "theorem", id: "sandbox-2", value: "B : U", local: false },
                        { kind: "theorem", id: "sandbox-1", value: "A : U", local: false }
                    ]
                };
            }
        };
        gui.moveSandboxItem("sandbox-1", " ");
        assert.deepEqual(gui.order, ["sandbox-2", "sandbox-1"]);
        assertCacheCleared(gui,
            "drag reordering must remove a cache bound to the previous declaration prefix");
        assert.deepEqual(events, ["persist", "render", "validate"]);
    }

    // Folder presentation state does not change declaration validation
    // signatures. Folding and renaming must retain the usable cache.
    {
        created = [];
        const events = [];
        const gui = makeGui(events);
        const folder = {
            kind: "folder",
            id: "sandbox-folder-1",
            name: "Folder",
            length: 1,
            open: true,
            disabled: false
        };
        gui.folders = [folder];
        gui.order = [folder.id, "sandbox-1"];
        gui.workspace = {
            setFolderOpen(_id, open) {
                folder.open = open;
                return { changed: true, snapshot: [] };
            },
            renameFolder(_id, name) {
                folder.name = name;
                return { changed: true, snapshot: [] };
            }
        };
        gui.applyWorkspaceSnapshot = () => undefined;
        globalThis.prompt = () => "Renamed";

        gui.createFolderRow(folder);
        const title = created.find(element => element.classList.contains("tt-folder-title"));
        const rename = created.find(element => element.title === "重命名文件夹");
        assert.ok(title);
        assert.ok(rename);
        title.dispatch("click");
        rename.dispatch("click");

        assert.equal(folder.open, false);
        assert.equal(folder.name, "Renamed");
        assertCachePresent(gui,
            "folder fold and rename operations must preserve the validation cache");
        assert.equal(events.includes("validate"), false,
            "pure folder presentation changes must not start semantic validation");
    }
} finally {
    if (previousDocument === undefined) delete globalThis.document;
    else globalThis.document = previousDocument;
    if (previousPrompt === undefined) delete globalThis.prompt;
    else globalThis.prompt = previousPrompt;
}

console.log("sandbox GUI validation-cache mutation regression passed");
