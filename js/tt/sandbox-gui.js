import { ASTParser } from "./astparser.js";
import { Core } from "./core.js";
import { SANDBOX_SAVE_VERSION, SandboxEnvironment, browserSandboxValidationLimits, createSandboxDeclaration, parseSandboxDeclaration, parseSandboxDeclarationSurface, migrateLegacySandboxSave, sandboxSourceLimitError, sandboxHitPathLevels, toSandboxSavedDeclaration } from "./sandbox.js";
import { highestHitPathLevel, hitPathConstructorsAt } from "./hit-path-levels.js";
import { SandboxWorkerCancelledError, SandboxWorkerClient } from "./sandbox-worker-client.js";
import { ListDragger } from "../fs/itemdragger.js";
import { TheoremWorkspace } from "./theorem-workspace.js";
import { applyWorkspaceLayout, createWorkspaceDragHandle, setWorkspaceRowData, syncWorkspaceDomOrder } from "./theorem-workspace-view.js";
import { expandTypeTheoryAliasesInSurface, installTypeTheorySymbolAliases } from "./symbol-aliases.js";
import { hasLegacySurfaceSyntax } from "./surface-syntax-migration.js";
const storageKey = "deductrium-type-theory-sandbox-v1";
const parser = new ASTParser();
const emptyBridge = () => ({ axioms: [], inductives: [], definitions: [] });
/** Normalize pasted aliases before the sandbox expression checker applies its
 * strict legacy-syntax guard.  Kept pure so the boundary is regression-testable
 * without constructing the browser UI. */
export function normalizeSandboxCheckInput(source) {
    return expandTypeTheoryAliasesInSurface(String(source ?? "").trim());
}
/** Apply the production browser guardrails while preserving explicit caller overrides. */
export function sandboxBrowserEnvironmentOptions(environmentOptions = {}) {
    return {
        ...browserSandboxValidationLimits,
        ...environmentOptions,
        systemRuleIds: environmentOptions.systemRuleIds
            ? [...environmentOptions.systemRuleIds]
            : undefined
    };
}
function sandboxStructuredDisplayDeclaration(declaration) {
    if (declaration.hit || declaration.inductive) {
        return { hit: declaration.hit, inductive: declaration.inductive };
    }
    if (!declaration.source || !["hit", "inductive"].includes(String(declaration.kind))) {
        return {};
    }
    try {
        let parsed;
        try {
            parsed = parseSandboxDeclarationSurface(declaration.source);
        }
        catch {
            parsed = parseSandboxDeclaration(declaration.source);
        }
        return { hit: parsed.hit, inductive: parsed.inductive };
    }
    catch {
        return {};
    }
}
function sandboxHitDisplayDeclaration(declaration) {
    return sandboxStructuredDisplayDeclaration(declaration).hit;
}
export function sandboxDeclarationDisplayKind(declaration) {
    if (String(declaration.kind) === "hit") {
        const hit = sandboxHitDisplayDeclaration(declaration);
        const dimension = hit ? highestHitPathLevel(sandboxHitPathLevels(hit)) : 1;
        return {
            kind: "HIT",
            trust: dimension === 3
                ? "三维高阶路径归纳"
                : dimension === 2
                    ? "二维高阶路径归纳"
                    : "一阶路径归纳",
            trustClass: "sandbox-hit"
        };
    }
    return { kind: declaration.kind, trust: "trusted", trustClass: "sandbox-trusted" };
}
export function sandboxInductiveDisplaySources(declaration) {
    const structured = sandboxStructuredDisplayDeclaration(declaration);
    const hit = structured.hit;
    const signature = declaration.kind === "inductive" ? structured.inductive : hit;
    if (!signature)
        return null;
    const parameters = signature.parameters
        .map(parameter => ` (${parameter.name} : ${parameter.typeSource})`)
        .join("");
    const indices = (signature.indices ?? [])
        .map(index => ` [${index.name} : ${index.typeSource}]`)
        .join("");
    const pathLevels = hit ? sandboxHitPathLevels(hit) : undefined;
    const constructors = hit
        ? [...hit.pointConstructors, ...hitPathConstructorsAt(pathLevels, 1)]
        : declaration.inductive?.constructors ?? [];
    return [
        `${signature.name}${parameters}${indices} : ${signature.universe}`,
        ...constructors.map(ctor => `${ctor.name} : ${ctor.typeSource}`),
        ...(pathLevels ? hitPathConstructorsAt(pathLevels, 2) : []).map(path => `path2 ${path.name} : ${path.typeSource}`),
        ...(pathLevels ? hitPathConstructorsAt(pathLevels, 3) : []).map(path => `path3 ${path.name} : ${path.typeSource}`)
    ];
}
function sandboxDeclarationLineAst(name, type) {
    return {
        type: ":",
        name: "",
        nodes: [
            { type: "var", name, nodes: [] },
            Core.clone(type)
        ]
    };
}
function sandboxDisplayTypeAst(value) {
    if (value.type)
        return Core.clone(value.type);
    // Older saves may contain only the type source.  Parse that source, never
    // the complete `name : type` line: declaration-owned names can begin with
    // parser-reserved letters such as L, P, S, W, or X.
    try {
        return parser.parseSurfaceOrLegacy(value.typeSource);
    }
    catch {
        return null;
    }
}
/**
 * Build structured display ASTs for an inductive/HIT declaration.
 *
 * Constructor names are kept as `var` nodes instead of being reparsed from
 * source text.  This is important for names such as `Loop2`, where the
 * generic parser treats the leading `L` as its lambda token.
 */
export function sandboxInductiveDisplayAsts(declaration) {
    const structured = sandboxStructuredDisplayDeclaration(declaration);
    const hit = structured.hit;
    const signature = declaration.kind === "inductive" ? structured.inductive : hit;
    if (!signature)
        return null;
    const entries = [
        { ast: sandboxInductiveHeaderAst(signature) }
    ];
    const pathLevels = hit ? sandboxHitPathLevels(hit) : undefined;
    const constructors = hit
        ? [...hit.pointConstructors, ...hitPathConstructorsAt(pathLevels, 1)]
        : declaration.inductive?.constructors ?? [];
    for (const constructor of constructors) {
        const type = sandboxDisplayTypeAst(constructor);
        if (!type)
            return null;
        entries.push({ ast: sandboxDeclarationLineAst(constructor.name, type) });
    }
    for (const path of pathLevels ? hitPathConstructorsAt(pathLevels, 2) : []) {
        const type = sandboxDisplayTypeAst(path);
        if (!type)
            return null;
        entries.push({
            ast: sandboxDeclarationLineAst(path.name, type),
            prefix: "path2 "
        });
    }
    for (const path of pathLevels ? hitPathConstructorsAt(pathLevels, 3) : []) {
        const type = sandboxDisplayTypeAst(path);
        if (!type)
            return null;
        entries.push({
            ast: sandboxDeclarationLineAst(path.name, type),
            prefix: "path3 "
        });
    }
    return entries;
}
function sandboxInductiveHeaderAst(signature) {
    let type = Core.clone(signature.universeAst);
    const binders = [...signature.parameters, ...(signature.indices ?? [])];
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
    validateButton;
    stopValidationButton;
    worker;
    environmentOptions;
    onAxiomsChange;
    renderAst;
    fallback = null;
    declarations = [];
    folders = [];
    order = [];
    validationCache;
    /** Use the same ordered folder semantics as the type-layer theorem list. */
    workspace = new TheoremWorkspace();
    pendingFolderId = null;
    dragger;
    validationRequest = 0;
    validationPromise = Promise.resolve();
    validationHandle = null;
    /** Whether the active validation may restore the bridge it found on entry. */
    validationCanRestoreBridge = false;
    /** Last bridge known to be published successfully for the current save. */
    lastTrustedBridge = null;
    initialized = false;
    persistenceSuspended = false;
    constructor(root, onAxiomsChange, renderAst, environmentOptions = {}, deferInitialLoad = false) {
        this.onAxiomsChange = onAxiomsChange;
        this.renderAst = renderAst;
        this.environmentOptions = sandboxBrowserEnvironmentOptions(environmentOptions);
        this.worker = new SandboxWorkerClient(this.environmentOptions);
        this.root = root;
        this.list = root.querySelector("#sandbox-list");
        this.input = root.querySelector("#sandbox-input");
        this.status = root.querySelector("#sandbox-status");
        this.checkInput = root.querySelector("#sandbox-check-input");
        this.checkOutput = root.querySelector("#sandbox-check-output");
        this.validateButton = rootButton(root, "#sandbox-validate");
        this.stopValidationButton = rootButton(root, "#sandbox-stop-validation");
        installTypeTheorySymbolAliases(this.input);
        installTypeTheorySymbolAliases(this.checkInput);
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
        this.validateButton?.addEventListener("click", () => void this.requestValidation(false));
        this.stopValidationButton?.addEventListener("click", () => this.cancelValidation());
        rootButton(this.root, "#sandbox-export")?.addEventListener("click", () => this.exportSave());
        rootButton(this.root, "#sandbox-copy")?.addEventListener("click", () => void this.copySave());
        rootButton(this.root, "#sandbox-import-trigger")?.addEventListener("click", () => {
            this.root.querySelector("#sandbox-import")?.click();
        });
        rootButton(this.root, "#sandbox-clear")?.addEventListener("click", () => this.clearWorkspace());
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
        this.updateValidationControls(false);
    }
    add() {
        this.addToFolder(this.pendingFolderId);
    }
    addToFolder(folderId) {
        const source = this.input.value.trim();
        if (!source)
            return;
        const sourceLimitError = sandboxSourceLimitError(source, this.environmentOptions?.validationMaxSourceChars);
        if (sourceLimitError) {
            this.setStatus(sourceLimitError, true);
            return;
        }
        try {
            parseSandboxDeclarationSurface(source);
        }
        catch (error) {
            this.setStatus(String(error), true);
            return;
        }
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
        const declaration = createSandboxDeclaration(source, `sandbox-${next}`, this.environmentOptions?.validationMaxSourceChars);
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
    /**
     * Queue a validation.  A manual re-check keeps the currently trusted
     * bridge available while the worker runs; mutations pass the default
     * `true` so stale declarations are revoked before checking the new save.
     */
    requestValidation(revokeBridge = true) {
        // A new request supersedes an in-flight one.  It must not restore the
        // old bridge because the new request may represent a newer save.
        this.cancelValidation(false);
        if (revokeBridge) {
            this.invalidateBridge();
            // Once a save mutation revoked the bridge, the previous bridge is
            // no longer valid for restoration if this validation is cancelled.
            this.lastTrustedBridge = null;
        }
        const promise = this.validate(!revokeBridge);
        this.validationPromise = promise;
        return promise;
    }
    invalidateBridge() {
        if (this.persistenceSuspended)
            return;
        this.onAxiomsChange?.(emptyBridge(), { revalidate: false });
    }
    /** Stop the active Worker request, retaining a bridge only for a manual re-check. */
    cancelValidation(announce = true) {
        const handle = this.validationHandle;
        if (!handle || !handle.cancel())
            return false;
        const canRestore = this.validationCanRestoreBridge;
        this.validationHandle = null;
        this.validationCanRestoreBridge = false;
        ++this.validationRequest;
        if (announce) {
            this.setStatus(canRestore && this.lastTrustedBridge
                ? "沙盒校验已取消，保留上次可信声明"
                : "沙盒校验已取消", false);
        }
        this.updateValidationControls(false);
        return true;
    }
    async validate(canRestoreBridge = false) {
        if (this.persistenceSuspended)
            return;
        const request = ++this.validationRequest;
        const save = this.toSave();
        this.validationCanRestoreBridge = canRestoreBridge;
        this.updateValidationControls(true);
        this.setStatus("正在校验沙盒声明…", false);
        let result;
        try {
            // New clients expose a cancellable request handle.  Keep the
            // legacy `validate()` path for deterministic mocks and older
            // integrations that do not yet implement the handle API.
            const worker = this.worker;
            const handle = typeof worker.validateRequest === "function"
                ? worker.validateRequest(save)
                : null;
            if (handle) {
                this.validationHandle = handle;
                try {
                    result = await handle.promise;
                }
                finally {
                    if (this.validationHandle === handle)
                        this.validationHandle = null;
                }
            }
            else {
                result = await this.worker.validate(save);
            }
        }
        catch (error) {
            if (request !== this.validationRequest || this.persistenceSuspended)
                return;
            this.updateValidationControls(false);
            if (error instanceof SandboxWorkerCancelledError) {
                this.setStatus(canRestoreBridge && this.lastTrustedBridge
                    ? "沙盒校验已取消，保留上次可信声明"
                    : "沙盒校验已取消", false);
                return;
            }
            try {
                this.onAxiomsChange?.(emptyBridge(), { revalidate: true });
            }
            catch { }
            this.lastTrustedBridge = null;
            const reason = error instanceof Error ? error.message : String(error);
            this.setStatus(`沙盒 Worker 校验失败：${reason}`, true);
            return;
        }
        if (request !== this.validationRequest || this.persistenceSuspended)
            return;
        this.updateValidationControls(false);
        if (result.status === "cancelled" || result.status === "budget-exhausted") {
            const message = result.status === "cancelled"
                ? "沙盒校验已取消，保留上次可信声明"
                : `沙盒校验已停止：${result.error ?? "达到资源上限"}`;
            this.setStatus(message, result.status === "budget-exhausted");
            return;
        }
        this.declarations = result.declarations;
        this.validationCache = result.validationCache;
        this.syncWorkspaceFromState();
        try {
            this.onAxiomsChange?.(result.bridge ?? emptyBridge(), { revalidate: true });
        }
        catch (error) {
            try {
                this.onAxiomsChange?.(emptyBridge(), { revalidate: true });
            }
            catch { }
            this.lastTrustedBridge = null;
            const reason = error instanceof Error ? error.message : String(error);
            this.setStatus(`沙盒类型层发布失败：${reason}`, true);
            return;
        }
        this.lastTrustedBridge = result.bridge ?? emptyBridge();
        this.validationCanRestoreBridge = false;
        this.persist();
        this.render();
        const invalid = this.declarations.filter(declaration => declaration.status === "invalid").length;
        this.setStatus(invalid ? `有 ${invalid} 条声明未通过校验` : "沙盒声明已校验；原始公理标记为 trusted", invalid > 0);
    }
    updateValidationControls(running) {
        if (this.validateButton)
            this.validateButton.disabled = running;
        if (this.stopValidationButton)
            this.stopValidationButton.disabled = !running;
        this.root?.classList.toggle("sandbox-validating", running);
    }
    async check() {
        // Pasted aliases may reach this expression checker without a keydown
        // event. Expand them before the legacy-syntax guard; otherwise the
        // supported `\\*` spelling is seen as a legacy `*` and rejected.
        const source = normalizeSandboxCheckInput(this.checkInput.value);
        if (!source)
            return;
        if (hasLegacySurfaceSyntax(source)) {
            this.checkOutput.textContent = "失败：不再支持旧语法，请使用 Unicode 符号";
            return;
        }
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
        installTypeTheorySymbolAliases(source);
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
                const sourceLimitError = sandboxSourceLimitError(source.value, this.environmentOptions?.validationMaxSourceChars);
                if (sourceLimitError) {
                    this.setStatus(sourceLimitError, true);
                    source.classList.remove("hide");
                    display.classList.add("hide");
                    return;
                }
                try {
                    parseSandboxDeclarationSurface(source.value.trim());
                }
                catch (error) {
                    this.setStatus(String(error), true);
                    source.classList.remove("hide");
                    display.classList.add("hide");
                    return;
                }
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
        const displayKind = sandboxDeclarationDisplayKind(declaration);
        kind.textContent = displayKind.kind;
        const trust = document.createElement("span");
        trust.className = displayKind.trustClass;
        trust.textContent = displayKind.trust;
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
        this.lastTrustedBridge = null;
        this.cancelValidation(false);
        this.persistenceSuspended = true;
        this.validationRequest++;
        this.worker.terminate();
        this.validationHandle = null;
        this.updateValidationControls(false);
        try {
            localStorage.removeItem(storageKey);
        }
        catch { }
    }
    renderDeclarationDisplay(declaration, display) {
        display.replaceChildren();
        try {
            const inductiveEntries = sandboxInductiveDisplayAsts(declaration);
            if (inductiveEntries) {
                const hit = sandboxHitDisplayDeclaration(declaration);
                const keyword = document.createElement("span");
                keyword.className = hit ? "sandbox-hit-keyword" : "";
                keyword.textContent = hit ? "hit " : "inductive ";
                display.appendChild(keyword);
                inductiveEntries.forEach((entry, index) => {
                    if (index > 0) {
                        const separator = document.createElement("span");
                        separator.textContent = " | ";
                        display.appendChild(separator);
                    }
                    if (entry.prefix) {
                        const prefix = document.createElement("span");
                        prefix.textContent = entry.prefix;
                        display.appendChild(prefix);
                    }
                    if (this.renderAst)
                        display.appendChild(this.renderAst(entry.ast));
                    else {
                        const text = document.createElement("span");
                        text.textContent = parser.stringify(entry.ast);
                        display.appendChild(text);
                    }
                });
                return;
            }
            // Keep malformed/legacy declarations readable without feeding a
            // constructor name back through the generic parser.  A source-only
            // fallback is preferable to a misleading lambda-token diagnostic.
            const inductiveSources = sandboxInductiveDisplaySources(declaration);
            if (inductiveSources) {
                const hit = sandboxHitDisplayDeclaration(declaration);
                display.textContent = `${hit ? "hit " : "inductive "}${inductiveSources.join(" | ")}`;
                return;
            }
            const ast = parser.parseSurfaceOrLegacy(declaration.source);
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
        const migrated = migrateLegacySandboxSave(value);
        if (!migrated || migrated.version !== SANDBOX_SAVE_VERSION
            || !Array.isArray(migrated.declarations)) {
            throw new Error("不支持的沙盒存档版本");
        }
        this.folders = Array.isArray(migrated.folders)
            ? migrated.folders.map(folder => ({
                ...folder,
                // Saves created before the shared workspace did not persist
                // subtree lengths.  Keep a marker until ownership can be
                // reconstructed from the legacy folderId/order fields.
                length: Number.isFinite(Number(folder.length)) ? Number(folder.length) : -1
            }))
            : [];
        const folderIds = new Set(this.folders.map(folder => folder.id));
        this.declarations = migrated.declarations.map((declaration, index) => {
            const source = declaration.source || `${declaration.name} : ${declaration.typeSource}`;
            const restored = createSandboxDeclaration(source, declaration.id || `sandbox-${index + 1}`, this.environmentOptions?.validationMaxSourceChars);
            restored.enabled = declaration.enabled !== false;
            restored.folderId = declaration.folderId && folderIds.has(declaration.folderId)
                ? declaration.folderId
                : null;
            return restored;
        });
        this.validationCache = migrated.validationCache;
        const knownIds = new Set([
            ...this.folders.map(folder => folder.id),
            ...this.declarations.map(declaration => declaration.id)
        ]);
        this.order = (Array.isArray(migrated.order) ? migrated.order : [])
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
            declarations: this.declarations.map(toSandboxSavedDeclaration),
            folders: this.folders.map(folder => ({ ...folder })),
            order: [...this.order],
            ...(this.validationCache ? { validationCache: this.validationCache } : {})
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
    /** Copy the same versioned package produced by Export. */
    async copySave() {
        const text = JSON.stringify(this.toSave(), null, 2);
        try {
            const clipboard = globalThis.navigator?.clipboard;
            if (!clipboard?.writeText)
                throw new Error("Clipboard API unavailable");
            await clipboard.writeText(text);
            this.setStatus("沙盒包已复制", false);
        }
        catch (error) {
            const reason = error instanceof Error ? error.message : String(error);
            this.setStatus(`复制沙盒包失败：${reason}`, true);
        }
    }
    /** Clear source state and revoke the trusted projection immediately. */
    clearWorkspace() {
        if (!this.declarations.length && !this.folders.length) {
            this.setStatus("沙盒已经为空", false);
            return;
        }
        if (!confirm("确定清空所有沙盒声明和文件夹吗？此操作不能撤销。"))
            return;
        this.cancelValidation(false);
        // Invalidate even a legacy/mock request that did not expose a
        // cancellable handle, and discard the Worker's old configured save.
        this.validationRequest++;
        this.worker.terminate();
        this.validationHandle = null;
        this.validationCanRestoreBridge = false;
        this.updateValidationControls(false);
        this.declarations = [];
        this.folders = [];
        this.order = [];
        this.pendingFolderId = null;
        this.fallback = null;
        this.workspace.replace([]);
        const bridge = emptyBridge();
        this.lastTrustedBridge = bridge;
        let bridgeError;
        try {
            this.onAxiomsChange?.(bridge, { revalidate: true });
        }
        catch (error) {
            bridgeError = error;
        }
        this.persist();
        this.render();
        if (bridgeError) {
            const reason = bridgeError instanceof Error ? bridgeError.message : String(bridgeError);
            this.setStatus(`沙盒已清空，但撤回类型层声明失败：${reason}`, true);
            return;
        }
        this.setStatus("沙盒已清空", false);
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