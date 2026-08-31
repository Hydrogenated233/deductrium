import { ASTParser } from "./astparser.js";
import { Core } from "./core.js";
import { SANDBOX_SAVE_VERSION, SandboxEnvironment, createSandboxDeclaration } from "./sandbox.js";
import { SandboxWorkerClient } from "./sandbox-worker-client.js";
import { ListDragger } from "../fs/itemdragger.js";
import { TheoremWorkspace } from "./theorem-workspace.js";
import { applyWorkspaceLayout, createWorkspaceDragHandle, setWorkspaceRowData, syncWorkspaceDomOrder } from "./theorem-workspace-view.js";
const storageKey = "deductrium-type-theory-sandbox-v1";
const parser = new ASTParser();
const emptyBridge = () => ({ axioms: [], inductives: [], definitions: [] });
export function sandboxInductiveDisplaySources(declaration) {
    const signature = declaration.inductive;
    if (declaration.kind !== "inductive" || !signature)
        return null;
    const parameters = signature.parameters
        .map(parameter => ` (${parameter.name} : ${parameter.typeSource})`)
        .join("");
    const indices = signature.indices
        .map(index => ` [${index.name} : ${index.typeSource}]`)
        .join("");
    return [
        `${signature.name}${parameters}${indices} : ${signature.universe}`,
        ...signature.constructors.map(ctor => `${ctor.name} : ${ctor.typeSource}`)
    ];
}
function sandboxInductiveHeaderAst(signature) {
    let type = Core.clone(signature.universeAst);
    const binders = [...signature.parameters, ...signature.indices];
    for (let index = binders.length - 1; index >= 0; index--) {
        type = {
            type: "P",
            name: binders[index].name,
            nodes: [Core.clone(binders[index].type), type]
        };
    }
    return {
        type: ":",
        name: "",
        nodes: [{ type: "var", name: signature.name }, type]
    };
}
/** Delay dependent startup work until the sandbox has installed its final bridge. */
export async function runAfterSandboxReady(sandbox, action) {
    if (sandbox)
        await sandbox.whenReady();
    await action();
}
/** UI controller for the independent stage-1 type-theory sandbox. */
export class TTSandboxGui {
    onStateChange = () => undefined;
    root;
    list;
    input;
    status;
    checkInput;
    checkOutput;
    worker;
    environmentOptions;
    onAxiomsChange;
    renderAst;
    fallback = null;
    declarations = [];
    folders = [];
    order = [];
    /** Use the same ordered folder semantics as the type-layer theorem list. */
    workspace = new TheoremWorkspace();
    pendingFolderId = null;
    dragger;
    validationRequest = 0;
    validationPromise = Promise.resolve();
    initialized = false;
    persistenceSuspended = false;
    constructor(root, onAxiomsChange, renderAst, environmentOptions = {}, deferInitialLoad = false) {
        this.onAxiomsChange = onAxiomsChange;
        this.renderAst = renderAst;
        this.environmentOptions = {
            ...environmentOptions,
            systemRuleIds: environmentOptions.systemRuleIds
                ? [...environmentOptions.systemRuleIds]
                : undefined
        };
        this.worker = new SandboxWorkerClient(this.environmentOptions);
        this.root = root;
        this.list = root.querySelector("#sandbox-list");
        this.input = root.querySelector("#sandbox-input");
        this.status = root.querySelector("#sandbox-status");
        this.checkInput = root.querySelector("#sandbox-check-input");
        this.checkOutput = root.querySelector("#sandbox-check-output");
        this.dragger = new ListDragger(this.list);
        this.dragger.cols = 1;
        this.dragger.queryDraggedNames = source => this.syncWorkspaceFromState().dragBlockIds(source);
        this.dragger.onExecute = (source, destination) => this.moveSandboxItem(source, destination);
        this.bindEvents();
        if (deferInitialLoad)
            this.render();
        else
            void this.initializeFromStandaloneSave();
    }
    bindEvents() {
        rootButton(this.root, "#sandbox-add")?.addEventListener("click", () => this.add());
        rootButton(this.root, "#sandbox-add-folder")?.addEventListener("click", () => {
            const next = this.folders.reduce((max, folder) => {
                const match = folder.id.match(/^sandbox-folder-(\d+)$/);
                return match ? Math.max(max, Number(match[1])) : max;
            }, 0) + 1;
            const folder = {
                kind: "folder",
                id: `sandbox-folder-${next}`,
                name: "新文件夹",
                length: 0,
                open: true,
                disabled: false
            };
            this.folders.push(folder);
            this.order.push(folder.id);
            this.syncWorkspaceFromState();
            this.persist();
            this.render();
        });
        rootButton(this.root, "#sandbox-validate")?.addEventListener("click", () => void this.requestValidation());
        rootButton(this.root, "#sandbox-export")?.addEventListener("click", () => this.exportSave());
        rootButton(this.root, "#sandbox-import-trigger")?.addEventListener("click", () => {
            this.root.querySelector("#sandbox-import")?.click();
        });
        this.root.querySelector("#sandbox-import")?.addEventListener("change", event => {
            const file = event.target.files?.[0];
            if (!file)
                return;
            const reader = new FileReader();
            reader.onload = () => {
                try {
                    this.load(JSON.parse(String(reader.result)));
                }
                catch (error) {
                    this.setStatus(String(error), true);
                }
            };
            reader.readAsText(file);
            event.target.value = "";
        });
        rootButton(this.root, "#sandbox-check")?.addEventListener("click", () => void this.check());
        this.input?.addEventListener("keydown", event => {
            if (event.key === "Enter" && (event.ctrlKey || event.metaKey)) {
                event.preventDefault();
                this.add();
            }
        });
    }
    add() {
        this.addToFolder(this.pendingFolderId);
    }
    addToFolder(folderId) {
        const source = this.input.value.trim();
        if (!source)
            return;
        if (folderId) {
            const folder = this.folders.find(item => item.id === folderId);
            if (!folder)
                return;
            if (!folder.open)
                folder.open = true;
        }
        const next = this.declarations.reduce((max, declaration) => {
            const match = declaration.id.match(/^sandbox-(\d+)$/);
            return match ? Math.max(max, Number(match[1])) : max;
        }, 0) + 1;
        const declaration = createSandboxDeclaration(source, `sandbox-${next}`);
        this.declarations.push(declaration);
        this.order.push(declaration.id);
        this.syncWorkspaceFromState();
        if (folderId) {
            const mutation = this.workspace.move(declaration.id, `inside:${folderId}`);
            if (mutation.changed)
                this.applyWorkspaceSnapshot(mutation.snapshot);
        }
        this.pendingFolderId = null;
        this.input.value = "";
        this.persist();
        this.render();
        void this.requestValidation();
    }
    /** Load the legacy standalone sandbox key when no game save owns the state. */
    initializeFromStandaloneSave() {
        if (this.initialized)
            return this.validationPromise;
        this.initialized = true;
        this.restore();
        this.render();
        return this.requestValidation();
    }
    /** Current bridge-validation barrier used by creative-mode startup. */
    whenReady() {
        return this.validationPromise;
    }
    requestValidation() {
        // Source/order/enable mutations are authoritative immediately. Revoke
        // the last validated projection before yielding to the Worker so a
        // deleted or edited name cannot remain usable during validation. The
        // final publication below is the only one that revalidates theorems.
        this.invalidateBridge();
        const promise = this.validate();
        this.validationPromise = promise;
        return promise;
    }
    invalidateBridge() {
        if (this.persistenceSuspended)
            return;
        this.onAxiomsChange?.(emptyBridge(), { revalidate: false });
    }
    async validate() {
        if (this.persistenceSuspended)
            return;
        const request = ++this.validationRequest;
        const save = this.toSave();
        this.setStatus("正在校验沙盒声明…", false);
        let result;
        try {
            result = await this.worker.validate(save);
        }
        catch (error) {
            if (request !== this.validationRequest || this.persistenceSuspended)
                return;
            try {
                this.onAxiomsChange?.(emptyBridge(), { revalidate: true });
            }
            catch { }
            const reason = error instanceof Error ? error.message : String(error);
            this.setStatus(`沙盒 Worker 校验失败：${reason}`, true);
            return;
        }
        if (request !== this.validationRequest || this.persistenceSuspended)
            return;
        this.declarations = result.declarations;
        this.syncWorkspaceFromState();
        try {
            this.onAxiomsChange?.(result.bridge ?? emptyBridge(), { revalidate: true });
        }
        catch (error) {
            try {
                this.onAxiomsChange?.(emptyBridge(), { revalidate: true });
            }
            catch { }
            const reason = error instanceof Error ? error.message : String(error);
            this.setStatus(`沙盒类型层发布失败：${reason}`, true);
            return;
        }
        this.persist();
        this.render();
        const invalid = this.declarations.filter(declaration => declaration.status === "invalid").length;
        this.setStatus(invalid ? `有 ${invalid} 条声明未通过校验` : "沙盒声明已校验；原始公理标记为 trusted", invalid > 0);
    }
    async check() {
        const source = this.checkInput.value.trim();
        if (!source)
            return;
        await this.whenReady();
        try {
            const result = await this.worker.check(this.toSave(), source);
            this.checkOutput.textContent = result.ok
                ? `通过：${result.type ? parser.stringify(result.type) : "已检查"}`
                : `失败：${result.error ?? "类型检查失败"}`;
        }
        catch {
            try {
                const fallback = this.getFallback();
                fallback.load(this.toSave());
                const result = fallback.check(source);
                this.checkOutput.textContent = result.ok
                    ? `通过：${result.type ? parser.stringify(result.type) : "已检查"}`
                    : `失败：${result.error ?? "类型检查失败"}`;
            }
            catch (error) {
                this.checkOutput.textContent = `失败：${String(error)}`;
            }
        }
    }
    render() {
        this.list.replaceChildren();
        this.syncWorkspaceFromState();
        const items = this.orderedItems();
        if (!items.length) {
            const empty = document.createElement("p");
            empty.className = "sandbox-empty";
            empty.textContent = "尚未添加沙盒声明";
            this.list.appendChild(empty);
        }
        else {
            for (const item of items) {
                if (item.kind === "folder") {
                    this.list.appendChild(this.createFolderRow(item));
                    continue;
                }
                this.list.appendChild(this.createDeclarationRow(item));
            }
        }
        const addButton = document.createElement("button");
        addButton.id = "sandbox-add";
        addButton.className = "inhabitat-modify";
        addButton.type = "button";
        addButton.title = "添加沙盒声明";
        addButton.textContent = "+";
        addButton.addEventListener("click", () => this.add());
        this.list.appendChild(addButton);
        // Keep the DOM ordering operation shared with the theorem list. Rows
        // are normally created in model order, but this also handles legacy
        // restore callers that supply already-mounted rows.
        syncWorkspaceDomOrder(this.list, Array.from(this.list.querySelectorAll("[data-drag-row='true']")), addButton);
        this.renderWorkspaceStructure();
        this.dragger.update();
    }
    orderedItems() {
        const byId = new Map();
        for (const folder of this.folders)
            byId.set(folder.id, folder);
        for (const declaration of this.declarations)
            byId.set(declaration.id, declaration);
        const ids = this.workspace.snapshot().map(item => item.id);
        const seen = new Set();
        const result = [];
        for (const id of ids) {
            const item = byId.get(id);
            if (!item || seen.has(id))
                continue;
            seen.add(id);
            result.push(item);
        }
        this.order = result.map(item => item.id);
        return result;
    }
    createDeclarationRow(declaration) {
        const row = document.createElement("div");
        row.className = `wrapper sandbox-declaration-row sandbox-${declaration.status}`;
        setWorkspaceRowData(row, declaration.id);
        row.dataset.sandboxId = declaration.id;
        row.title = declaration.dependencies.length
            ? `依赖：${declaration.dependencies.join(", ")}`
            : "无外部依赖";
        const drag = createWorkspaceDragHandle(row, declaration.id, {
            dragger: this.dragger,
            title: "拖动排序声明"
        });
        drag.textContent = "↕";
        drag.draggable = false;
        const enabled = document.createElement("input");
        enabled.type = "checkbox";
        enabled.checked = declaration.enabled;
        enabled.title = "启用声明";
        enabled.addEventListener("change", () => {
            declaration.enabled = enabled.checked;
            declaration.status = declaration.enabled ? "unchecked" : "disabled";
            delete declaration.error;
            this.persist();
            void this.requestValidation();
        });
        const source = document.createElement("input");
        source.type = "text";
        source.className = "sandbox-source tt-theorem-input hide";
        source.value = declaration.source;
        source.title = "按 Enter 更新声明";
        const display = document.createElement("div");
        display.className = "inhabitat-div sandbox-source-display";
        display.title = "点击进入编辑";
        const renderDisplay = () => this.renderDeclarationDisplay(declaration, display);
        renderDisplay();
        display.addEventListener("click", () => {
            display.classList.add("hide");
            source.classList.remove("hide");
            source.focus();
            source.select();
        });
        const finishEdit = () => {
            if (source.value !== declaration.source) {
                declaration.source = source.value;
                declaration.status = declaration.enabled ? "unchecked" : "disabled";
                delete declaration.error;
                this.persist();
                void this.requestValidation();
            }
            source.classList.add("hide");
            display.classList.remove("hide");
            renderDisplay();
        };
        source.addEventListener("keydown", event => {
            if (event.key !== "Enter")
                return;
            event.preventDefault();
            finishEdit();
        });
        source.addEventListener("blur", () => {
            finishEdit();
        });
        const kind = document.createElement("span");
        kind.className = "sandbox-kind";
        kind.textContent = declaration.kind;
        const trust = document.createElement("span");
        trust.className = "sandbox-trusted";
        trust.textContent = "trusted";
        const state = document.createElement("span");
        state.className = "sandbox-declaration-status";
        state.textContent = declaration.status === "invalid"
            ? declaration.error || "无效"
            : declaration.status === "disabled" ? "已停用" : declaration.status;
        const remove = actionButton("×", "删除声明", () => {
            this.syncWorkspaceFromState();
            const mutation = this.workspace.removeTheorem(declaration.id);
            if (mutation.changed)
                this.applyWorkspaceSnapshot(mutation.snapshot);
            this.persist();
            this.render();
            void this.requestValidation();
        });
        row.append(drag, enabled, source, display, kind, trust, state, remove);
        return row;
    }
    /**
     * Re-render the read-only source views after the type-layer renderer has
     * refreshed its known-name/highlight tables.  Keep an actively edited row
     * untouched so a background type-list refresh cannot cancel the editor.
     */
    refreshDisplays() {
        const declarations = new Map(this.declarations.map(item => [item.id, item]));
        for (const row of Array.from(this.list.querySelectorAll("[data-sandbox-id]"))) {
            const id = row.dataset.sandboxId;
            const declaration = id ? declarations.get(id) : undefined;
            if (!declaration)
                continue;
            const source = row.querySelector(".sandbox-source");
            const display = row.querySelector(".sandbox-source-display");
            // The source input is visible while editing.  Do not replace its
            // sibling display or steal focus during an unrelated refresh.
            if (!display || source && !source.classList.contains("hide"))
                continue;
            this.renderDeclarationDisplay(declaration, display);
        }
    }
    /** Snapshot embedded in the creative-mode game save. */
    serializeGameSave() {
        return this.toSave();
    }
    /** Replace the complete sandbox workspace from a creative-mode game save. */
    restoreGameSave(value) {
        this.initialized = true;
        this.load(value, false, true);
        return this.requestValidation();
    }
    clearPersistedSave() {
        // Reset/navigation must revoke the creative bridge before suspending
        // persistence; otherwise the type layer can keep using declarations
        // from the deleted sandbox save until the next page load.
        try {
            this.onAxiomsChange?.(emptyBridge(), { revalidate: false });
        }
        catch { }
        this.persistenceSuspended = true;
        this.validationRequest++;
        this.worker.terminate();
        try {
            localStorage.removeItem(storageKey);
        }
        catch { }
    }
    renderDeclarationDisplay(declaration, display) {
        display.replaceChildren();
        try {
            const inductiveSources = sandboxInductiveDisplaySources(declaration);
            if (inductiveSources) {
                const keyword = document.createElement("span");
                keyword.textContent = "inductive ";
                display.appendChild(keyword);
                inductiveSources.forEach((source, index) => {
                    if (index > 0) {
                        const separator = document.createElement("span");
                        separator.textContent = " | ";
                        display.appendChild(separator);
                    }
                    const ast = index === 0
                        ? sandboxInductiveHeaderAst(declaration.inductive)
                        : parser.parse(source);
                    if (this.renderAst)
                        display.appendChild(this.renderAst(ast));
                    else {
                        const text = document.createElement("span");
                        text.textContent = parser.stringify(ast);
                        display.appendChild(text);
                    }
                });
                return;
            }
            const ast = parser.parse(declaration.source);
            if (this.renderAst)
                display.appendChild(this.renderAst(ast));
            else
                display.textContent = parser.stringify(ast);
        }
        catch (error) {
            display.textContent = `${declaration.source} - ${String(error)}`;
        }
    }
    createFolderRow(folder) {
        const row = document.createElement("div");
        row.className = "wrapper tt-folder-row sandbox-folder-row";
        setWorkspaceRowData(row, folder.id, {
            folder: true,
            folderOpen: folder.open
        });
        row.dataset.sandboxFolderId = folder.id;
        const drag = createWorkspaceDragHandle(row, folder.id, {
            dragger: this.dragger,
            title: "拖动排序文件夹",
            rowOptions: {
                folder: true,
                folderOpen: folder.open
            }
        });
        drag.draggable = false;
        const toggleFolder = () => {
            this.syncWorkspaceFromState();
            const mutation = this.workspace.setFolderOpen(folder.id, !folder.open);
            if (mutation.changed)
                this.applyWorkspaceSnapshot(mutation.snapshot);
            this.persist();
            this.render();
        };
        const add = actionButton("+", "在文件夹底部添加沙盒声明", () => {
            if (!folder.open) {
                this.syncWorkspaceFromState();
                const mutation = this.workspace.setFolderOpen(folder.id, true);
                if (mutation.changed)
                    this.applyWorkspaceSnapshot(mutation.snapshot);
            }
            this.pendingFolderId = folder.id;
            this.renderWorkspaceStructure();
            this.input.focus();
        });
        const title = document.createElement("span");
        title.className = "tt-folder-title";
        title.textContent = folder.name;
        title.title = "点击折叠或展开文件夹";
        title.classList.toggle("dir-open", folder.open);
        title.classList.toggle("dir-close", !folder.open);
        title.addEventListener("click", toggleFolder);
        const label = document.createElement("label");
        label.className = "tt-folder-disable";
        const disabled = document.createElement("input");
        disabled.type = "checkbox";
        disabled.checked = folder.disabled;
        disabled.title = "停用文件夹中的声明";
        label.append(disabled, document.createTextNode("停用子声明"));
        disabled.addEventListener("change", () => {
            this.syncWorkspaceFromState();
            const mutation = this.workspace.setFolderDisabled(folder.id, disabled.checked);
            if (mutation.changed)
                this.applyWorkspaceSnapshot(mutation.snapshot);
            this.persist();
            this.render();
            void this.requestValidation();
        });
        const rename = actionButton("✎", "重命名文件夹", () => {
            const nextName = prompt("文件夹名称：", folder.name)?.trim();
            if (!nextName)
                return;
            this.syncWorkspaceFromState();
            const mutation = this.workspace.renameFolder(folder.id, nextName);
            if (mutation.changed)
                this.applyWorkspaceSnapshot(mutation.snapshot);
            this.persist();
            this.render();
        });
        const remove = actionButton("×", "删除文件夹（声明移到上一级）", () => {
            this.syncWorkspaceFromState();
            const mutation = this.workspace.removeFolder(folder.id);
            if (!mutation.changed)
                return;
            this.applyWorkspaceSnapshot(mutation.snapshot);
            this.persist();
            this.render();
            void this.requestValidation();
        });
        row.append(drag, add, title, label, rename, remove);
        return row;
    }
    restore() {
        try {
            const raw = localStorage.getItem(storageKey);
            if (!raw)
                return;
            this.load(JSON.parse(raw), false);
        }
        catch (error) {
            this.setStatus(`沙盒存档加载失败：${String(error)}`, true);
        }
    }
    load(value, validate = true, persist = true) {
        if (!value || typeof value !== "object" || value.version !== SANDBOX_SAVE_VERSION
            || !Array.isArray(value.declarations)) {
            throw new Error("不支持的沙盒存档版本");
        }
        this.folders = Array.isArray(value.folders)
            ? value.folders.map(folder => ({
                ...folder,
                // Saves created before the shared workspace did not persist
                // subtree lengths.  Keep a marker until ownership can be
                // reconstructed from the legacy folderId/order fields.
                length: Number.isFinite(Number(folder.length)) ? Number(folder.length) : -1
            }))
            : [];
        const folderIds = new Set(this.folders.map(folder => folder.id));
        this.declarations = value.declarations.map((declaration, index) => {
            const source = declaration.source || `${declaration.name} : ${declaration.typeSource}`;
            const restored = createSandboxDeclaration(source, declaration.id || `sandbox-${index + 1}`);
            restored.enabled = declaration.enabled !== false;
            restored.folderId = declaration.folderId && folderIds.has(declaration.folderId)
                ? declaration.folderId
                : null;
            return restored;
        });
        const knownIds = new Set([
            ...this.folders.map(folder => folder.id),
            ...this.declarations.map(declaration => declaration.id)
        ]);
        this.order = (Array.isArray(value.order) ? value.order : [])
            .filter(id => knownIds.has(id));
        for (const id of [...this.folders.map(folder => folder.id), ...this.declarations.map(declaration => declaration.id)]) {
            if (!this.order.includes(id))
                this.order.push(id);
        }
        this.repairLegacyFolderLengths();
        this.render();
        if (persist)
            this.persist();
        if (validate)
            return this.requestValidation();
        return Promise.resolve();
    }
    toSave() {
        return {
            version: SANDBOX_SAVE_VERSION,
            declarations: this.declarations.map(declaration => ({ ...declaration, dependencies: [...declaration.dependencies] })),
            folders: this.folders.map(folder => ({ ...folder })),
            order: [...this.order]
        };
    }
    persist() {
        if (this.persistenceSuspended)
            return;
        try {
            localStorage.setItem(storageKey, JSON.stringify(this.toSave()));
        }
        catch { }
        this.onStateChange();
    }
    exportSave() {
        const blob = new Blob([JSON.stringify(this.toSave(), null, 2)], { type: "application/json" });
        const url = URL.createObjectURL(blob);
        const link = document.createElement("a");
        link.href = url;
        link.download = "deductrium-type-theory-sandbox.json";
        link.click();
        URL.revokeObjectURL(url);
    }
    setStatus(message, error) {
        this.status.textContent = message;
        this.status.classList.toggle("error", error);
    }
    moveSandboxItem(sourceId, destination) {
        if (!sourceId)
            return;
        // The shared theorem list keeps its add button as the final child;
        // dropping below it is the same as the workspace bottom sentinel.
        if (destination === "+")
            destination = " ";
        this.syncWorkspaceFromState();
        const mutation = this.workspace.move(sourceId, destination || " ");
        if (!mutation.changed)
            return;
        this.applyWorkspaceSnapshot(mutation.snapshot);
        this.persist();
        this.render();
        void this.requestValidation();
    }
    /**
     * Rebuild the shared flat workspace from the sandbox's persisted state.
     * The workspace is authoritative for nesting and ordering; declaration
     * objects retain validation metadata that is not part of its item shape.
     */
    syncWorkspaceFromState() {
        const folders = new Map(this.folders.map(folder => [folder.id, folder]));
        const declarations = new Map(this.declarations.map(declaration => [declaration.id, declaration]));
        const items = [];
        const seen = new Set();
        const append = (id) => {
            if (seen.has(id))
                return;
            const folder = folders.get(id);
            if (folder) {
                seen.add(id);
                items.push({
                    kind: "folder",
                    id: folder.id,
                    name: folder.name,
                    length: Math.max(0, Number(folder.length) || 0),
                    open: folder.open !== false,
                    disabled: !!folder.disabled
                });
                return;
            }
            const declaration = declarations.get(id);
            if (!declaration)
                return;
            seen.add(id);
            items.push({
                kind: "theorem",
                id: declaration.id,
                value: declaration.source,
                local: false
            });
        };
        for (const id of this.order)
            append(id);
        // Legacy callers and old saves may omit the order array.  Keep those
        // records visible and make the resulting order deterministic.
        for (const folder of this.folders)
            append(folder.id);
        for (const declaration of this.declarations)
            append(declaration.id);
        this.order = items.map(item => item.id);
        this.workspace.replace(items);
        const normalized = this.workspace.snapshot();
        const normalizedById = new Map(normalized.map(item => [item.id, item]));
        for (const folder of this.folders) {
            const item = normalizedById.get(folder.id);
            if (item?.kind === "folder")
                folder.length = item.length;
        }
        return this.workspace;
    }
    repairLegacyFolderLengths() {
        const positions = new Map(this.order.map((id, index) => [id, index]));
        for (const folder of this.folders) {
            if (folder.length >= 0)
                continue;
            const folderIndex = positions.get(folder.id);
            if (folderIndex === undefined) {
                folder.length = 0;
                continue;
            }
            let last = folderIndex;
            for (const declaration of this.declarations) {
                if (declaration.folderId !== folder.id)
                    continue;
                const index = positions.get(declaration.id);
                if (index !== undefined && index > last)
                    last = index;
            }
            folder.length = Math.max(0, last - folderIndex);
        }
    }
    /** Apply a workspace mutation while preserving sandbox-only declaration data. */
    applyWorkspaceSnapshot(snapshot) {
        const folderById = new Map(this.folders.map(folder => [folder.id, folder]));
        const declarationById = new Map(this.declarations.map(declaration => [declaration.id, declaration]));
        this.workspace.replace(snapshot);
        const normalized = this.workspace.snapshot();
        const scopesById = this.workspace.folderScopesForItems(normalized.map(item => item.id));
        const nextFolders = [];
        const nextDeclarations = [];
        for (const item of normalized) {
            if (item.kind === "folder") {
                const previous = folderById.get(item.id);
                const folder = {
                    kind: "folder",
                    id: item.id,
                    name: item.name,
                    length: item.length,
                    open: item.open,
                    disabled: item.disabled
                };
                // Preserve object identity for any external references while
                // still replacing removed/reordered rows deterministically.
                if (previous)
                    Object.assign(previous, folder);
                nextFolders.push(previous ?? folder);
                continue;
            }
            const declaration = declarationById.get(item.id);
            if (!declaration)
                continue;
            declaration.source = item.value;
            declaration.folderId = scopesById.get(item.id)?.at(-1)?.id ?? null;
            nextDeclarations.push(declaration);
        }
        this.folders = nextFolders;
        this.declarations = nextDeclarations;
        this.order = normalized.map(item => item.id);
    }
    /** Apply visibility, indentation, and disabled state from the workspace. */
    renderWorkspaceStructure() {
        this.syncWorkspaceFromState();
        const layout = this.workspace.layout();
        const folders = new Map(this.folders.map(folder => [folder.id, folder]));
        const declarations = new Map(this.declarations.map(declaration => [declaration.id, declaration]));
        applyWorkspaceLayout(Array.from(this.list.querySelectorAll("[data-drag-row='true']")), layout, (row, state) => {
            const id = row.dataset.dragId;
            if (!id)
                return;
            const declaration = declarations.get(id);
            row.classList.toggle("sandbox-disabled", state.disabled || declaration?.status === "disabled" || declaration?.enabled === false);
            if (row.dataset.dragFolder === "true") {
                const folder = folders.get(id);
                const title = row.querySelector(".tt-folder-title");
                row.dataset.dragFolderOpen = String(folder?.open !== false);
                row.classList.toggle("sandbox-folder-collapsed", folder?.open === false);
                if (folder) {
                    if (title)
                        title.title = folder.open ? "点击折叠文件夹" : "点击展开文件夹";
                    title?.classList.toggle("dir-open", folder.open);
                    title?.classList.toggle("dir-close", !folder.open);
                }
            }
        });
    }
    getFallback() {
        return this.fallback ??= new SandboxEnvironment(this.environmentOptions);
    }
}
function rootButton(root, selector) {
    return root.querySelector(selector);
}
function actionButton(label, title, action) {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "inhabitat-modify";
    button.textContent = label;
    button.title = title;
    button.addEventListener("click", action);
    return button;
}
//# sourceMappingURL=sandbox-gui.js.map