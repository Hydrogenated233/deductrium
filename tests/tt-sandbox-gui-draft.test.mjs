import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTSandboxGui } from "../js/tt/sandbox-gui.js";

const invalidDraft = "Draft := (";

function forbidAstParser() {
    const calls = [];
    const originals = new Map();
    for (const method of ["parse", "parseSurface", "parseSurfaceOrLegacy"]) {
        if (typeof ASTParser.prototype[method] !== "function") continue;
        originals.set(method, ASTParser.prototype[method]);
        ASTParser.prototype[method] = function () {
            calls.push(method);
            throw new Error(`main-thread AST parser called: ${method}`);
        };
    }
    return {
        calls,
        restore() {
            for (const [method, implementation] of originals) {
                ASTParser.prototype[method] = implementation;
            }
        }
    };
}

function baseGui(events = []) {
    const gui = Object.create(TTSandboxGui.prototype);
    gui.persistenceSuspended = false;
    gui.environmentOptions = { validationMaxSourceChars: 100_000 };
    gui.declarations = [];
    gui.folders = [];
    gui.order = [];
    gui.pendingFolderId = null;
    gui.validationCache = undefined;
    gui.input = { value: invalidDraft };
    gui.syncWorkspaceFromState = () => ({ move: () => ({ changed: false }) });
    gui.repairLegacyFolderLengths = () => undefined;
    gui.persist = () => events.push("persist");
    gui.render = () => events.push("render");
    gui.requestValidation = () => {
        events.push("validate");
        return Promise.resolve();
    };
    gui.setStatus = (message, failed) => events.push({ message, failed });
    return gui;
}

// Add stores a raw draft and delegates syntax/type validation to the Worker.
// A deliberately incomplete term makes any main-thread AST parse observable.
{
    const parserGuard = forbidAstParser();
    const events = [];
    const gui = baseGui(events);
    try {
        gui.addToFolder(null);

        assert.deepEqual(parserGuard.calls, [],
            "adding a draft must not call the main-thread AST parser");
        assert.equal(gui.declarations.length, 1,
            "adding an invalid draft must not be blocked by the main-thread AST parser");
        assert.equal(gui.declarations[0].source, invalidDraft);
        assert.equal(gui.declarations[0].status, "unchecked");
        assert.deepEqual(events, ["persist", "render", "validate"]);
    } finally {
        parserGuard.restore();
    }
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
        this.tagName = tagName.toUpperCase();
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

// Editing has the same draft boundary as adding: Enter commits text, then the
// Worker owns the parser error and resulting invalid status.
{
    const parserGuard = forbidAstParser();
    const previousDocument = globalThis.document;
    const created = [];
    globalThis.document = {
        createElement(tagName) {
            const element = new FakeElement(tagName);
            created.push(element);
            return element;
        },
        createTextNode(text) {
            const element = new FakeElement("#text");
            element.textContent = text;
            return element;
        }
    };
    try {
        const events = [];
        const gui = baseGui(events);
        gui.dragger = { attachIdxListener() {} };
        gui.renderDeclarationDisplay = () => undefined;
        const declaration = {
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
        };
        gui.declarations = [declaration];
        gui.order = [declaration.id];

        gui.createDeclarationRow(declaration);
        const input = created.find(element => element.classList.contains("sandbox-source"));
        assert.ok(input, "the declaration row must expose its source editor");
        input.value = invalidDraft;
        input.dispatch("keydown", {
            key: "Enter",
            preventDefault() {}
        });

        assert.deepEqual(parserGuard.calls, [],
            "editing a draft must not call the main-thread AST parser");
        assert.equal(declaration.source, invalidDraft,
            "editing an invalid draft must not be blocked by the main-thread AST parser");
        assert.equal(declaration.status, "unchecked");
        assert.deepEqual(events, ["persist", "validate"]);

        // A collapsed folder is not an insertion target. The add-at-folder-
        // bottom action must leave it collapsed and report the reason rather
        // than silently changing the user's folder state.
        const collapsedFolder = {
            kind: "folder",
            id: "sandbox-folder-1",
            name: "Closed",
            length: 1,
            open: false,
            disabled: false
        };
        gui.folders = [collapsedFolder];
        gui.order = [collapsedFolder.id, declaration.id];
        created.length = 0;
        gui.createFolderRow(collapsedFolder);
        const addToCollapsed = created.find(element =>
            element.tagName === "BUTTON" && element.title === "在文件夹底部添加沙盒声明"
        );
        assert.ok(addToCollapsed, "collapsed folders must still expose the guarded add action");
        addToCollapsed.dispatch("click");
        assert.equal(collapsedFolder.open, false,
            "the guarded add action must not expand a collapsed folder");
        assert.equal(gui.pendingFolderId, null,
            "a rejected collapsed-folder insertion must not leave a pending target");
        assert.match(events.at(-1)?.message ?? "", /折叠文件夹不能添加沙盒声明/);
    } finally {
        parserGuard.restore();
        if (previousDocument === undefined) delete globalThis.document;
        else globalThis.document = previousDocument;
    }
}

// Loading restores saved source text without reparsing every declaration on
// the UI thread. The subsequent Worker request owns migration validation.
{
    const parserGuard = forbidAstParser();
    const events = [];
    const gui = baseGui(events);
    const save = {
        version: 1,
        declarations: [{
            id: "sandbox-load-draft",
            name: "Draft",
            kind: "definition",
            source: invalidDraft,
            typeSource: "",
            enabled: true,
            trusted: true,
            status: "invalid",
            dependencies: [],
            folderId: null
        }],
        folders: [],
        order: ["sandbox-load-draft"]
    };

    try {
        let pending;
        assert.doesNotThrow(() => { pending = gui.load(save, true, false); },
            "loading a saved draft must not invoke the main-thread AST parser");
        await pending;
        assert.deepEqual(parserGuard.calls, [],
            "loading drafts must not call the main-thread AST parser");
        assert.equal(gui.declarations[0].source, invalidDraft);
        assert.deepEqual(events, ["render", "validate"]);
    } finally {
        parserGuard.restore();
    }
}

// Draft rendering is raw text. Once the Worker supplies a presentation AST,
// rendering consumes that AST without reparsing the source on the UI thread.
{
    const parserGuard = forbidAstParser();
    try {
        const gui = baseGui();
        const display = new FakeElement("div");
        const draft = {
            id: "sandbox-render-draft",
            name: "Draft",
            kind: "definition",
            source: invalidDraft,
            typeSource: "",
            enabled: true,
            trusted: true,
            status: "unchecked",
            dependencies: [],
            folderId: null
        };
        gui.renderDeclarationDisplay(draft, display);
        assert.equal(display.textContent, invalidDraft);

        let renderedAst;
        gui.renderAst = ast => {
            renderedAst = ast;
            return new FakeElement("span");
        };
        const presentationAst = { type: "var", name: "Validated", nodes: [] };
        gui.renderDeclarationDisplay({
            ...draft,
            source: "Validated : U",
            status: "valid",
            presentationAst
        }, display);
        assert.equal(renderedAst, presentationAst);
        assert.deepEqual(parserGuard.calls, [],
            "draft and Worker-backed display rendering must not call the UI-thread parser");
    } finally {
        parserGuard.restore();
    }
}

// A cache loaded from disk is an untrusted one-shot Worker hint. It must not
// enter autosave until the Worker returns a freshly certified cache.
{
    const gui = baseGui();
    const pendingCache = {
        version: 1,
        semanticEpoch: "untrusted-test-cache",
        preludeKey: "untrusted",
        entries: []
    };
    gui.load({
        version: 1,
        declarations: [],
        folders: [],
        order: [],
        validationCache: pendingCache
    }, false, false);
    assert.equal(Object.hasOwn(gui.serializeGameSave(), "validationCache"), false,
        "an unverified loaded cache must not be written back to autosave");
    assert.equal(gui.toWorkerSave().validationCache, pendingCache,
        "the pending cache must remain available to the next Worker validation only");
}

// Worker failure is explicit; expression checks must not instantiate a
// synchronous SandboxEnvironment fallback on the browser main thread.
{
    const gui = baseGui();
    gui.checkInput = { value: "True" };
    gui.checkOutput = { textContent: "" };
    gui.whenReady = async () => undefined;
    gui.toWorkerSave = () => ({ version: 1, declarations: [], folders: [], order: [] });
    gui.worker = { async check() { throw new Error("worker unavailable"); } };
    await gui.check();
    assert.match(gui.checkOutput.textContent, /Worker 检查失败.*worker unavailable/);
}

console.log("sandbox GUI parser-free draft lifecycle regression passed");
