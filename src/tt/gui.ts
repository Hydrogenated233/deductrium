import { langMgr, TR } from "../lang.js";
import { AST, ASTParser, debugBoundVarId } from "./astparser.js";
import { Core, Context, DefinitionTypeCacheSnapshot, assignContext, wrapApply, wrapVar, wrapLambda } from "./core.js";
import { TTCoreWorkerClient } from "./core-worker-client.js";
import {
    installTrustedDeclarations,
    TTCoreConfig,
    type TTTrustedDeclarationOrderEntry
} from "./engine.js";
import type { CoreSystemInductiveBundle } from "./core.js";
import type { SandboxBridge } from "./sandbox.js";
import type { SandboxBridgeChangeOptions } from "./sandbox-gui.js";
import { TTDefinitionSlot } from "./core-session.js";
import { TTAssistEngine, TTAssistOptions, TTAssistQedResult, TTAssistSnapshot } from "./assist-engine.js";
import { TTAssistWorkerClient } from "./assist-worker-client.js";
import { Assist } from "./assist.js";
import { TTWorkerMutationQueue } from "./worker-mutation-queue.js";
import { ListDragger } from "../fs/itemdragger.js";
import { TypeRule, initTypeSystem } from "./initial.js";
import { ProofScriptEditor, scriptThroughCaret } from "../proof-editor.js";
import {
    prettySandboxInductiveNamesForDisplay,
    restoreSemanticMetaNamesForDisplay
} from "./presentation.js";
import { canReuseTheoremResultOnBlur, findEarliestPendingTheorem, isKnownTheoremIdentifier, shouldFallbackToSynchronousTheoremValidation, theoremInferenceComplete, theoremInferenceStatus, theoremInferenceTarget, theoremPreviewNeedsRefresh, theoremValidationPositionMatches, TheoremValidationCoordinator, typeTheoryValidationTimedOut } from "./theorem-validation.js";
import {
    TheoremWorkspace,
    TheoremWorkspaceItem,
    TheoremWorkspaceSaveItem
} from "./theorem-workspace.js";
import {
    applyWorkspaceLayout,
    createWorkspaceDragHandle,
    syncWorkspaceDomOrder
} from "./theorem-workspace-view.js";
import {
    SerializedTTProofSessions,
    TTProofSession,
    TTProofSessionStore
} from "./proof-sessions.js";
const parser = new ASTParser;
const constructors = new Set<string>();
const destructors = new Set<string>();
const computeEqs = new Set<string>();
const macro = new Set<string>();
const sysmacro = new Set<string>();
const semanticResourceScaleStorageKey = "deductrium-tt-semantic-resource-scale";
const tacticTextModeStorageKey = "deductrium-tt-proof-text-mode";

let consts = new Set<string>;
type definedConst = [string, AST, DefinitionTypeCacheSnapshot?];
export type TTTheoremSaveItem = TheoremWorkspaceSaveItem;
type TTTheoremItem = {
    kind: "theorem",
    id: string,
    wrapper: HTMLDivElement,
    input: HTMLInputElement,
    localCheckbox: HTMLInputElement
} | {
    kind: "folder",
    id: string,
    name: string,
    length: number,
    open: boolean,
    disabled: boolean,
    wrapper: HTMLDivElement,
    title: HTMLSpanElement,
    checkbox: HTMLInputElement
};
const allrules = initTypeSystem();
const reservedConsts = new Set<string>;

export function cloneInductiveBundle(bundle: CoreSystemInductiveBundle): CoreSystemInductiveBundle {
    return {
        type: [bundle.type[0], Core.clone(bundle.type[1])],
        auxiliaryTypes: (bundle.auxiliaryTypes ?? []).map(([name, type]) => [name, Core.clone(type)]),
        constructors: (bundle.constructors ?? []).map(([name, type]) => [name, Core.clone(type)]),
        eliminator: bundle.eliminator
            ? [bundle.eliminator[0], Core.clone(bundle.eliminator[1])]
            : undefined,
        recursor: bundle.recursor
            ? [bundle.recursor[0], Core.clone(bundle.recursor[1])]
            : undefined,
        definitions: (bundle.definitions ?? []).map(([name, definition]) => [name, Core.clone(definition)]),
        computeRules: Object.fromEntries(Object.entries(bundle.computeRules ?? {}).map(([head, rules]) => [
            head,
            rules.map(rule => ({
                pattern: rule.pattern.map(pattern => Core.clone(pattern)),
                result: Core.clone(rule.result)
            }))
        ])),
        metadata: bundle.metadata
            ? {
                version: bundle.metadata.version,
                kind: bundle.metadata.kind,
                dimension: bundle.metadata.dimension,
                typeName: bundle.metadata.typeName,
                parameterCount: bundle.metadata.parameterCount,
                indexCount: bundle.metadata.indexCount,
                indices: bundle.metadata.indices?.map(index => ({
                    name: index.name,
                    type: Core.clone(index.type)
                })),
                eliminatorName: bundle.metadata.eliminatorName,
                fullEliminatorName: bundle.metadata.fullEliminatorName,
                recursorName: bundle.metadata.recursorName,
                fullRecursorName: bundle.metadata.fullRecursorName,
                constructors: bundle.metadata.constructors.map(ctor => ({
                    name: ctor.name,
                    argumentTypes: ctor.argumentTypes.map(type => Core.clone(type)),
                    resultIndices: ctor.resultIndices?.map(index => Core.clone(index))
                })),
                pathConstructors: bundle.metadata.pathConstructors?.map(ctor => ({
                    name: ctor.name,
                    argumentTypes: ctor.argumentTypes.map(type => Core.clone(type)),
                    left: Core.clone(ctor.left),
                    right: Core.clone(ctor.right),
                    computationName: ctor.computationName
                }))
            }
            : undefined
    };
}

export type SandboxInductiveEntryPresentation = {
    postfix: "构造" | "解构" | "递归" | "定义" | "计算";
    prefix: "sandbox inductive" | "sandbox HIT";
    category: "constructor" | "eliminator" | "axiom" | "compute";
};

/** Classify a generated sandbox entry without relying on name-prefix guesses. */
export function sandboxInductiveEntryPresentation(
    bundle: CoreSystemInductiveBundle,
    name: string,
    fallback: Omit<SandboxInductiveEntryPresentation, "prefix">
): SandboxInductiveEntryPresentation {
    const prefix = bundle.metadata?.kind === "hit1" ? "sandbox HIT" : "sandbox inductive";
    const paths = bundle.metadata?.pathConstructors ?? [];
    const publicName = name.startsWith("@") ? name.slice(1) : name;
    if (paths.some(path => path.name === publicName)) {
        return { postfix: "构造", prefix, category: "constructor" };
    }
    if (paths.some(path =>
        path.computationName === publicName || `ap_${path.name}` === publicName
    )) {
        return { postfix: "计算", prefix, category: "compute" };
    }
    return { ...fallback, prefix };
}
export class TTGui {
    puzzleDefs = new Set<string>;
    skipRendering = true;
    onStateChange = () => { };
    /** Called after the rendered type/constant tables have been rebuilt. */
    onTypeListUpdated = () => { };
    core = new Core;
    disableSimpleFn = false;
    disableSimpleEq = false;
    displayPi = true;
    enablecopygate = false;
    lastGateTarget = "";
    // gamecore = new HoTTGame;
    typeList = document.getElementById("type-list");
    unlockedTypes: Set<string>;
    unlockedTactics: Set<string>;
    inhabitList = document.getElementById("inhabit-list");
    private theoremItems: TTTheoremItem[] = [];
    private theoremWorkspace = new TheoremWorkspace();
    /** The workspace is authoritative after its first hydration. */
    private theoremWorkspaceHydrated = false;
    /** Ordered theorem inputs derived from theoremItems, cached by structure revision. */
    private theoremInputsCache: HTMLInputElement[] = [];
    private theoremInputsCacheRevision = -1;
    private theoremItemSequence = 0;
    private restoringTheoremItems = false;
    private theoremDragger = new ListDragger(this.inhabitList);
    // tactic mode: tactic-begin for waiting clicking theorem
    mode = null;
    // "_" for infered, "@" for original
    inferDisplayMode: "_" | "@" = "_";
    userDefinedConsts: definedConst[] = [];
    /** Trusted body-less declarations imported from the creative sandbox. */
    private sandboxAxioms: [string, AST][] = [];
    private sandboxAxiomNames = new Set<string>();
    /** Trusted ordinary-inductive signatures supplied by the creative sandbox. */
    private sandboxInductives: CoreSystemInductiveBundle[] = [];
    /** Transparent definitions supplied by the creative sandbox. */
    private sandboxDefinitions: [string, AST][] = [];
    private sandboxDefinitionNames = new Set<string>();
    /** Cross-category order validated by the sandbox Worker. */
    private sandboxDeclarationOrder: TTTrustedDeclarationOrderEntry[] | undefined = undefined;
    private readonly creativeMode: boolean;
    /** Names of successfully checked user definitions used by AST rendering. */
    private userConstNames = new Set<string>();
    sysDefinedConsts: definedConst[] = [];
    private coreWorker: TTCoreWorkerClient | null = null;
    private assistWorker: TTAssistWorkerClient | null = null;
    private assistWorkerGeneration = -1;
    private assistWorkerConfigKey = "";
    private assistWorkerConfigurePromise: Promise<void> = null;
    private readonly assistWorkerMutations = new TTWorkerMutationQueue();
    private readonly assistFallback = new TTAssistEngine();
    private assistOptions: TTAssistOptions = {
        disableMultipleApply: true,
        disableDestructConds: true,
        disableDestructEq: true
    };
    private assistSnapshot: TTAssistSnapshot = null;
    private assistWorkerSessionReady = false;
    private tacticBusy = false;
    private tacticRequestId = 0;
    private tacticTextMode = false;
    private tacticTextModePreference = false;
    private tacticScript = "";
    private tacticScriptDirty = false;
    private tacticScriptEditor: ProofScriptEditor | null = null;
    private tacticTextReplayTimer: number | null = null;
    private tacticTextReplayRevision = 0;
    private proofSessions = new TTProofSessionStore();
    private pendingProofSessions: SerializedTTProofSessions | null = null;
    /** Prevent autosave from replacing a stored draft with a replay prefix. */
    private tacticSessionReplayId: string | null = null;
    private tacticCaptureBlockedSessionId: string | null = null;
    private tacticSelectingTarget = false;
    private tacticTargetInput: HTMLInputElement | null = null;
    private tacticScopeFolderId: string | null = null;
    private tacticScopeExplicit = false;
    private tacticDefinitionsRevision = -1;
    private coreWorkerGeneration = -1;
    private coreWorkerConfigKey = "";
    private coreWorkerConfigurePromise: Promise<void> = null;
    private coreWorkerLoadedThrough = 0;
    /** Invalidates completions from an older logical state of the same Worker/configuration. */
    private coreWorkerStateRevision = 0;
    private readonly coreWorkerMutations = new TTWorkerMutationQueue();
    private definitionRevision = 0;
    /** Core context currently materialized for gate/type queries. */
    private hottDefCtxtKey: string | null = null;
    private hottDefCtxtMacroNames: Set<string> | null = null;
    private hottDefCtxtCore: Core | null = null;
    private hottDefCtxtMaterialized: {
        scopeId: string | null;
        configKey: string;
        entries: { index: number, slot: definedConst }[];
    } | null = null;
    private semanticResourceScale = 1;
    /** Changes whenever theorem rows are inserted, removed, or reordered. */
    private theoremStructureRevision = 0;
    private workerRequestId = 0;
    private readonly theoremValidation = new TheoremValidationCoordinator();
    private gateQueryCache = new Map<string, boolean>();
    private gatePreviewRevision = -1;
    private gatePreviewStructureRevision = -1;
    private gatePreviewScopeId: string | null = null;
    /** Explicit scope used while synchronously rendering a gate preview. */
    private astRenderScopeFolderId: string | null | undefined;
    /** Cached shared tooltip node; ast2HTML is called for every AST fragment. */
    private floatTypeDiv: HTMLDivElement | null = null;

    private initializeSemanticResourceScale() {
        let stored: string | null = null;
        try {
            stored = localStorage.getItem(semanticResourceScaleStorageKey);
        } catch { }
        this.semanticResourceScale = Core.setSemanticResourceScale(stored ?? 1);
        const input = document.getElementById("semanticResourceScale") as HTMLInputElement;
        if (!input) return;
        input.value = String(this.semanticResourceScale);
        input.addEventListener("change", () => this.setSemanticResourceScale(input.value));
    }

    private setSemanticResourceScale(value: unknown) {
        const previous = this.semanticResourceScale;
        this.semanticResourceScale = Core.setSemanticResourceScale(value);
        const input = document.getElementById("semanticResourceScale") as HTMLInputElement;
        if (input) input.value = String(this.semanticResourceScale);
        try {
            localStorage.setItem(semanticResourceScaleStorageKey, String(this.semanticResourceScale));
        } catch { }
        if (this.semanticResourceScale === previous) return;

        // The active proof session owns a separately configured engine. Keep
        // its visible history, but replay it with the new finite budget before
        // accepting another command.
        this.tacticDefinitionsRevision = -1;
        this.assistWorkerSessionReady = false;
        this.tacticRequestId++;
        this.setTacticBusy(false);
        if (!this.skipRendering) {
            this.revalidateTheorems();
            this.warmCoreWorkerWhenEmpty();
        }
    }

    private getTheoremInputsFromItems() {
        if (this.theoremInputsCacheRevision !== this.theoremStructureRevision) {
            this.theoremInputsCache = this.theoremItems
                .filter((item): item is Extract<TTTheoremItem, { kind: "theorem" }> => item.kind === "theorem")
                .map(item => item.input);
            this.theoremInputsCacheRevision = this.theoremStructureRevision;
        }
        return this.theoremInputsCache;
    }
    /** Resolves after the current automatic theorem-validation suffix settles. */
    waitForValidationIdle() {
        return this.theoremValidation.waitForIdle();
    }
    initTypeList() {
        const expand = {};
        for (const rule of allrules) {
            if (rule.ast.type === ":=" && rule.ast.nodes[0].type === "var") {
                let sub = rule.ast.nodes[1];
                const applyList = [];
                let isInfer = true;
                while (sub.type === "apply") {
                    applyList.unshift(sub.nodes[1]);
                    if (sub.nodes[1].name !== "_" || sub.nodes[1].type !== "var") isInfer = false;
                    sub = sub.nodes[0];
                }
                applyList.unshift(sub);
                if (sub.name[0] === "@" && isInfer) this.core.opaque.push([rule.ast.nodes[0].name, applyList.length]);
                expand[rule.ast.nodes[0].name] = applyList;
            }
            if (rule.postfix === "计算" && rule.ast.type === "===" && rule.id !== "Function") {
                const applyList: AST[] = [];
                let sub = rule.ast.nodes[0];
                while (sub.type === "apply") {
                    applyList.unshift(sub.nodes[1]);
                    sub = sub.nodes[0];
                }
                applyList.unshift(sub);
                const result = this.core.desugar(Core.clone(rule.ast.nodes[1]), true);
                // yy x === xx
                this.core.state.computeRules[sub.name] ??= [];
                this.core.state.computeRules[sub.name].push({
                    pattern: applyList,
                    result
                });
                let sub2: AST[];
                // if yy := @yy _ _
                if (sub.type === "var" && (sub2 = expand[sub.name])) {
                    const applyList2 = applyList.slice(1);
                    applyList2.unshift(...sub2);
                    // also add @yy _ _ x === xx
                    this.core.state.computeRules[sub2[0].name] ??= [];
                    this.core.state.computeRules[sub2[0].name].push({
                        pattern: applyList2,
                        result
                    });
                }
            }
        }
        this.core.syncSemanticComputeRules?.();
        // During save restoration the UI is intentionally hidden, but the
        // sandbox Worker can finish before the first visible type-list render.
        // Seed the main Core after its computation rules are ready so the
        // first trusted bridge sees the same complete built-in environment as
        // the Worker (notably indexed-family indices such as `nat`).
        if (this.skipRendering) this.updateTypeList(this.unlockedTypes, false);
    }
    constructor(creative: boolean, skipRendering: boolean) {
        this.creativeMode = creative;
        this.initializeSemanticResourceScale();
        try { this.coreWorker = new TTCoreWorkerClient(); } catch (error) { console.warn("Type-theory worker unavailable", error); }
        this.skipRendering = skipRendering;
        try {
            this.tacticTextModePreference = window.localStorage.getItem(tacticTextModeStorageKey) === "1";
        } catch { }
        this.tacticTextMode = this.tacticTextModePreference;
        this.theoremDragger.cols = 1;
        this.theoremDragger.queryDraggedNames = source => this.syncTheoremWorkspaceFromDom().dragBlockIds(source);
        this.theoremDragger.onExecute = (src, dst) => this.moveTheoremItem(src, dst === "+" ? " " : dst);
        this.unlockedTypes = new Set(creative ? allrules.map(r => r.id) : ["True", "False"]);
        if (!skipRendering) this.updateTypeList(this.unlockedTypes);
        if (!creative) {
            this.unlockedTactics = new Set(["qed"]);
            this.disableSimpleFn = true;
            this.disableSimpleEq = true;
            this.puzzleDefs = new Set([
                "what", "Fin", "code_nat", "ftr", "ftreq", "Combin", "factorial2",
                "fillList", "lastList", "firstList", "lenList", "invList", "sumList", "mapList",
                "count_0", "del_0", "joinList",
            ]);
        } else {
            this.assistOptions = {
                disableMultipleApply: false,
                disableDestructConds: false,
                disableDestructEq: false
            };
            document.getElementById("displayPi-label").classList.remove("hide");
            document.getElementById("tactic-div").classList.remove("hide");
        }
        this.initTypeList();
        this.updateInhabitList();
        document.getElementById("add-btn").addEventListener("click", () => {
            this.updateInhabitList();
        });
        document.getElementById("tt-add-theorem")?.addEventListener("click", () => this.updateInhabitList());
        document.getElementById("tt-add-folder")?.addEventListener("click", () => this.addTheoremFolder());
        const input = document.getElementById("tactic-input") as HTMLInputElement;
        input.addEventListener("keydown", (ev) => {
            if (ev.key === "Enter" || ev.key === "Escape") {
                ev.preventDefault();
                document.getElementById("tactic-begin").click();
            }
        });
        input.addEventListener("input", () => this.resizeTacticInput());
        input.addEventListener("focus", () => this.resizeTacticInput());
        document.getElementById("tactic-text-toggle")?.addEventListener("click", () => {
            this.toggleTacticTextMode();
        });
        const scriptInput = document.getElementById("tactic-script") as HTMLTextAreaElement | null;
        if (scriptInput) this.tacticScriptEditor = new ProofScriptEditor(scriptInput);
        scriptInput?.addEventListener("input", () => {
            this.tacticScript = scriptInput.value;
            this.tacticScriptDirty = true;
            if (this.proofSessions.activeId) {
                this.proofSessions.update(this.proofSessions.activeId, {
                    script: this.tacticScript,
                    stale: true
                });
            }
            this.onStateChange();
            this.scheduleTacticTextReplay();
        });
        const scheduleTacticCaretReplay = () => this.scheduleTacticTextReplay();
        scriptInput?.addEventListener("selectionchange", scheduleTacticCaretReplay);
        scriptInput?.addEventListener("click", scheduleTacticCaretReplay);
        scriptInput?.addEventListener("keyup", scheduleTacticCaretReplay);
        scriptInput?.addEventListener("keydown", event => {
            if (event.key === "Enter" && event.ctrlKey) {
                event.preventDefault();
                void this.replayTacticText(true, true);
            }
        });
        document.getElementById("tactic-script-run-cursor")?.addEventListener("click", () => {
            void this.replayTacticText(true, true);
        });
        document.getElementById("tactic-script-run")?.addEventListener("click", () => {
            void this.replayTacticText(true, false);
        });
        (document.getElementById('timeSelect') as HTMLSelectElement).addEventListener('change', function () {
            Core.timeout = Number(this.value) * 1000;
        });
        document.getElementById("tactic-scope")?.addEventListener("change", () => {
            if (!(this.mode instanceof Array) || this.tacticBusy) return;
            const select = document.getElementById("tactic-scope") as HTMLSelectElement;
            this.tacticScopeFolderId = select.value || null;
            this.tacticScopeExplicit = true;
            if (this.proofSessions.activeId) {
                this.proofSessions.update(this.proofSessions.activeId, {
                    scopeFolderId: this.tacticScopeFolderId,
                    scopeExplicit: true,
                    stale: true
                });
            }
            this.tacticDefinitionsRevision = -1;
            const requestId = ++this.tacticRequestId;
            this.renderTacticScopeOptions();
            this.ensureAssistSessionCurrent().then(snapshot => {
                if (requestId !== this.tacticRequestId || !(this.mode instanceof Array)) return;
                if (this.proofSessions.activeId) {
                    this.proofSessions.update(this.proofSessions.activeId, {
                        history: snapshot.history,
                        stale: false
                    });
                    if (this.tacticCaptureBlockedSessionId === this.proofSessions.activeId) {
                        this.tacticCaptureBlockedSessionId = null;
                    }
                }
                this.renderAssistSnapshot(snapshot);
                this.renderTacticSessionTabs();
                this.onStateChange();
            }).catch(error => {
                if (requestId === this.tacticRequestId) {
                    document.getElementById("tactic-errmsg").innerText = this.formatTacticError(error);
                }
            });
        });
        document.getElementById("tactic-remove").addEventListener("click", () => void this.removeTactic());
        document.getElementById("tactic-clear").addEventListener("click", () => this.resetTacticPage());
        document.getElementById("tactic-begin").addEventListener("click", () => {
            this.addTactic(false);
        });
        this.renderTacticSessionTabs();
    }
    setLastGateTarget(target: string) {
        if (!theoremPreviewNeedsRefresh(
            target,
            this.lastGateTarget,
            this.definitionRevision,
            this.gatePreviewRevision,
            this.theoremStructureRevision,
            this.gatePreviewStructureRevision
        )) return;
        if (target !== this.lastGateTarget) this.gatePreviewScopeId = null;
        if (this.gatePreviewScopeId
            && !this.getAllTheoremFolders().some(folder => folder.id === this.gatePreviewScopeId)) {
            this.gatePreviewScopeId = null;
        }
        this.lastGateTarget = target;
        this.gatePreviewRevision = this.definitionRevision;
        this.gatePreviewStructureRevision = this.theoremStructureRevision;
        const copygate = document.getElementById("copygate");
        copygate.innerText = "";
        const btn = document.createElement("button");
        copygate.appendChild(document.createTextNode(TR("最近#t门上的目标：")));
        const scopeLabel = document.createElement("label");
        scopeLabel.className = "tactic-scope-picker";
        scopeLabel.appendChild(document.createTextNode(TR("引用文件夹：")));
        const scopeSelect = document.createElement("select");
        const global = document.createElement("option");
        global.value = "";
        global.innerText = TR("不使用局部常量");
        scopeSelect.appendChild(global);
        for (const folder of this.getAllTheoremFolders()) {
            const option = document.createElement("option");
            option.value = folder.id;
            option.innerText = this.getFolderPath(folder.id);
            scopeSelect.appendChild(option);
        }
        scopeLabel.appendChild(scopeSelect);
        copygate.appendChild(scopeLabel);
        btn.classList.add("inhabitat-modify"); btn.innerText = "+";
        copygate.appendChild(btn);
        scopeSelect.value = this.gatePreviewScopeId ?? "";
        scopeSelect.addEventListener("change", () => {
            this.gatePreviewScopeId = scopeSelect.value || null;
            this.gatePreviewRevision = -1;
            this.setLastGateTarget(target);
        });
        btn.onclick = () => {
            this.executeTactic(target, null, scopeSelect.value || null);
        }
        copygate.appendChild(this.renderAstInScope(
            "",
            parser.parse(target),
            [],
            [],
            this.getInhabitatArray().length,
            this.gatePreviewScopeId
        ));
    }
    private autofillTactics(allTactics: string[]) {
        let tactics: string[];
        if (this.unlockedTactics) {
            tactics = [];
            // only for survival. If creative, this.unlockedTactics is undefined
            for (const t of allTactics) {
                const prefix = t.split(" ")[0];
                if (this.unlockedTactics.has(prefix)) {
                    tactics.push(t);
                }
            }
        } else {
            tactics = allTactics;
        }

        const div = document.getElementById("tactic-autofill");
        const inp = document.getElementById("tactic-input") as HTMLInputElement;
        const exec = document.getElementById("tactic-begin");
        div.innerHTML = tactics.length ? TR("推荐策略：<br>") : "";
        for (const t of tactics) {
            const btn = document.createElement("button");
            div.appendChild(btn);
            btn.innerText = t;
            btn.addEventListener("click", () => {
                inp.value = t;
                if (!t.includes("??")) {
                    exec.click();
                } else {
                    inp.focus();
                    inp.selectionStart = t.indexOf("??");
                    inp.selectionEnd = inp.selectionStart + 2;
                }
            });
        }
    }
    private updateTacticStateDisplay(snapshot: TTAssistSnapshot, statediv: HTMLDivElement) {
        if (!snapshot.goals.length) {
            this.addSpan(statediv, TR("无目标，请输入qed结束"));
        }

        for (let count = snapshot.goals.length - 1; count >= 0; count--) {
            const g = snapshot.goals[count];
            statediv.appendChild(document.createElement("hr"));
            const goalDiv = document.createElement("div");
            goalDiv.className = "proof-text-goal";
            const scope = g.context.map(e => ({ type: "var", name: e[0], bondVarId: e[2] } as AST));

            for (const [k, v, id] of g.context) {
                const ast = {
                    type: ":", name: "", nodes: [{ type: "var", name: k }, v]
                };
                ast.nodes[0].checked = ast.nodes[1];
                goalDiv.prepend(document.createElement("br"));
                goalDiv.prepend(this.ast2HTML("", ast, scope, g.context, this.getInhabitatArray().length));
            }
            goalDiv.appendChild(document.createElement("br"));
            this.addSpan(goalDiv, count ? TR("目标") + (count) + TR("：") : TR("当前目标："));
            goalDiv.appendChild(this.ast2HTML("", g.type, scope, g.context, this.getInhabitatArray().length));
            if (count) goalDiv.classList.add("proof-text-goal-secondary");
            goalDiv.appendChild(document.createElement("br"));
            statediv.appendChild(goalDiv);
        }
    }
    private setTacticBusy(busy: boolean) {
        this.tacticBusy = busy;
        // Keep the original assistant's controls interactive. The internal
        // flag still prevents overlapping async commands.
    }
    /** Keep the active tactic command selectable without horizontal scrolling. */
    private resizeTacticInput() {
        const input = document.getElementById("tactic-input") as HTMLTextAreaElement | null;
        if (!input) return;
        input.style.height = "auto";
        // Growing the editor can add a scrollbar to the history list, which
        // narrows the editor and may create another wrapped line. Re-measure
        // a few times so the last line is not clipped.
        for (let pass = 0; pass < 3; pass++) {
            const nextHeight = Math.max(input.scrollHeight, 21);
            const borderHeight = Math.max(0, input.offsetHeight - input.clientHeight);
            if (input.clientHeight >= nextHeight) break;
            input.style.height = `${nextHeight + borderHeight}px`;
        }
    }
    private isBlankTacticSession(session: TTProofSession | null | undefined) {
        return !!session
            && session.kind === "manual"
            && !session.target.trim()
            && session.history.length === 0
            && !session.script.trim();
    }
    private proofSessionLabel(session: TTProofSession, index: number) {
        if (session.title.trim()) return session.title.trim();
        if (this.isBlankTacticSession(session)) return `${TR("证明页")} ${index + 1}`;
        const prefix = session.kind === "gate" ? "#t " : session.kind === "manual" ? "? " : "";
        return prefix + (session.target.trim() || TR("空目标"));
    }
    private renderTacticSessionTabs() {
        const tabs = document.getElementById("tactic-session-tabs");
        if (!tabs || !this.proofSessions) return;
        tabs.replaceChildren();
        for (const [index, session] of this.proofSessions.sessions.entries()) {
            const tab = document.createElement("div");
            tab.className = "proof-session-tab"
                + (session.id === this.proofSessions.activeId ? " active" : "")
                + (session.stale ? " stale" : "")
                + (session.detached ? " detached" : "");
            tab.draggable = true;
            tab.dataset.proofSessionId = session.id;
            const label = document.createElement("button");
            label.type = "button";
            label.className = "proof-session-label";
            label.textContent = this.proofSessionLabel(session, index);
            label.title = session.target
                ? `${session.target}\n${TR("双击重命名证明页")}`
                : TR("双击重命名证明页");
            label.addEventListener("click", () => this.selectTacticSession(session.id));
            label.addEventListener("dblclick", event => {
                event.preventDefault();
                event.stopPropagation();
                const editor = document.createElement("input");
                editor.className = "proof-session-name-input";
                editor.value = session.title || this.proofSessionLabel(session, index);
                let settled = false;
                const finish = (cancel: boolean) => {
                    if (settled) return;
                    settled = true;
                    if (!cancel) {
                        this.proofSessions.update(session.id, { title: editor.value.trim() });
                        this.onStateChange();
                    }
                    this.renderTacticSessionTabs();
                };
                editor.addEventListener("keydown", keyEvent => {
                    if (keyEvent.key === "Enter") {
                        keyEvent.preventDefault();
                        finish(false);
                    } else if (keyEvent.key === "Escape") {
                        keyEvent.preventDefault();
                        finish(true);
                    }
                });
                editor.addEventListener("blur", () => finish(false));
                label.replaceWith(editor);
                editor.focus();
                editor.select();
            });
            const close = document.createElement("button");
            close.type = "button";
            close.className = "proof-session-close";
            close.textContent = "x";
            close.title = TR("关闭证明会话");
            close.addEventListener("click", event => {
                event.stopPropagation();
                if (session.id === this.proofSessions.activeId) {
                    this.closeTacticSession();
                } else {
                    this.proofSessions.close(session.id);
                    this.renderTacticSessionTabs();
                    this.onStateChange();
                }
            });
            tab.addEventListener("dragstart", event => {
                event.dataTransfer?.setData("text/type-proof-session", session.id);
                tab.classList.add("dragging");
            });
            tab.addEventListener("dragend", () => tab.classList.remove("dragging"));
            tab.addEventListener("dragover", event => {
                event.preventDefault();
                tab.classList.add("drag-over");
            });
            tab.addEventListener("dragleave", () => tab.classList.remove("drag-over"));
            tab.addEventListener("drop", event => {
                event.preventDefault();
                tab.classList.remove("drag-over");
                const source = event.dataTransfer?.getData("text/type-proof-session");
                if (!source || source === session.id) return;
                this.captureActiveTacticSession();
                this.proofSessions.reorder(source, session.id);
                this.renderTacticSessionTabs();
                this.onStateChange();
            });
            tab.append(label, close);
            tabs.appendChild(tab);
        }
        const add = document.createElement("button");
        add.id = "tactic-session-add";
        add.type = "button";
        add.className = "proof-session-add";
        add.textContent = "+";
        add.title = TR("新建证明页");
        add.addEventListener("click", () => this.beginTacticTargetSelection(true));
        tabs.appendChild(add);
        tabs.ondragover = event => {
            if ((event.target as HTMLElement).closest?.(".proof-session-tab")) return;
            event.preventDefault();
        };
        tabs.ondrop = event => {
            if ((event.target as HTMLElement).closest?.(".proof-session-tab")) return;
            event.preventDefault();
            const source = event.dataTransfer?.getData("text/type-proof-session");
            if (!source) return;
            this.captureActiveTacticSession();
            this.proofSessions.reorder(source, null);
            this.renderTacticSessionTabs();
            this.onStateChange();
        };
    }
    private selectTacticSession(id: string) {
        if (id === this.proofSessions.activeId) return;
        void this.activateTacticSession(id);
    }
    private beginTacticTargetSelection(createPage = false) {
        if (this.tacticBusy) return;
        this.captureActiveTacticSession();
        if (createPage || !this.isBlankTacticSession(this.proofSessions.active)) {
            this.proofSessions.openBlank();
        }
        this.clearTacticRuntime();
        this.tacticSelectingTarget = true;
        this.mode = "tactic-begin";
        document.getElementById("tactic-hint").innerText = TR("请在定理列表中点选待证命题");
        this.renderTacticSessionTabs();
        this.onStateChange();
    }
    private captureActiveTacticSession() {
        if (!this.proofSessions) return;
        const active = this.proofSessions.active;
        if (!active || !(this.mode instanceof Array)) return;
        if (active.id === this.tacticSessionReplayId
            || active.id === this.tacticCaptureBlockedSessionId) return;
        const scriptInput = document.getElementById("tactic-script") as HTMLTextAreaElement | null;
        const script = this.tacticTextMode || this.tacticScriptDirty
            ? scriptInput?.value ?? this.tacticScript
            : this.mode.slice(1).join("\n");
        this.proofSessions.update(active.id, {
            target: this.mode[0],
            history: this.mode.slice(1),
            script,
            scopeFolderId: this.tacticScopeFolderId,
            scopeExplicit: this.tacticScopeExplicit
        });
    }
    private theoremItemById(id: string | null) {
        if (!id) return null;
        return this.theoremItems.find((item): item is Extract<TTTheoremItem, { kind: "theorem" }> =>
            item.kind === "theorem" && item.id === id) ?? null;
    }
    private reconcileProofSessionBindings(allowIndexFallback: boolean) {
        // Some state/helper regression tests construct TTGui without running
        // its browser constructor. Session binding is optional in that path.
        if (!this.proofSessions) return;
        const inputs = this.getInhabitatArray();
        const bindings = this.proofSessions.sessions
            .filter(session => session.kind === "theorem" && !session.detached)
            .map(session => {
                let item = this.theoremItemById(session.theoremItemId);
                if (!item && allowIndexFallback && session.targetTheoremIndex !== null) {
                    const input = inputs[session.targetTheoremIndex];
                    item = input ? this.getTheoremItemForInput(input) as Extract<TTTheoremItem, { kind: "theorem" }> : null;
                }
                return { session, item, index: item ? inputs.indexOf(item.input) : -1 };
            })
            .sort((left, right) => left.index - right.index);
        for (const binding of bindings) {
            const { session, item, index } = binding;
            if (!item || index < 0) {
                if (session.theoremItemId) this.proofSessions.detachTheorem(session.theoremItemId);
                continue;
            }
            const defaultScope = this.getDefaultTacticScope(item.input);
            if (allowIndexFallback && session.theoremItemId !== item.id) {
                this.proofSessions.rebindTheoremByIndex({
                    target: item.input.value,
                    theoremItemId: item.id,
                    targetTheoremIndex: index,
                    scopeFolderId: session.scopeExplicit ? session.scopeFolderId : defaultScope,
                    scopeExplicit: session.scopeExplicit
                });
            } else {
                if (session.target !== item.input.value) {
                    this.proofSessions.markTheoremTargetChanged(item.id, item.input.value, index);
                }
                const allowedScopes = this.getFolderScopeForInput(item.input).map(folder => folder.id);
                if (session.scopeExplicit && session.scopeFolderId !== null
                    && !allowedScopes.includes(session.scopeFolderId)) {
                    this.proofSessions.update(session.id, {
                        scopeFolderId: defaultScope,
                        scopeExplicit: false,
                        stale: true
                    });
                } else {
                    this.proofSessions.updateTheoremLocation(item.id, index, defaultScope);
                }
            }
        }
        this.renderTacticSessionTabs();
    }
    private async activateTacticSession(id: string, captureCurrent = true) {
        if (this.tacticBusy) return;
        if (captureCurrent) this.captureActiveTacticSession();
        this.reconcileProofSessionBindings(false);
        let session = this.proofSessions.activate(id);
        this.clearTacticRuntime();
        session = this.proofSessions.session(id) ?? session;
        this.renderTacticSessionTabs();
        this.onStateChange();
        if (this.isBlankTacticSession(session)) {
            this.tacticSelectingTarget = true;
            this.mode = "tactic-begin";
            document.getElementById("tactic-hint").innerText = TR("请在定理列表中点选待证命题");
            return;
        }
        const targetItem = session.kind === "theorem" && !session.detached
            ? this.theoremItemById(session.theoremItemId)
            : null;
        if (session.kind === "theorem" && !session.detached && !targetItem) {
            if (session.theoremItemId) this.proofSessions.detachTheorem(session.theoremItemId);
            session = this.proofSessions.session(id) ?? session;
        }
        this.tacticTargetInput = targetItem?.input ?? null;
        this.tacticScopeExplicit = session.scopeExplicit;
        this.tacticScopeFolderId = session.scopeFolderId;
        this.tacticScript = session.script;
        this.tacticScriptDirty = session.script !== session.history.join("\n");
        const scriptInput = document.getElementById("tactic-script") as HTMLTextAreaElement | null;
        if (scriptInput) {
            scriptInput.value = session.script;
            this.tacticScriptEditor?.refresh();
        }
        this.mode = [session.target];
        this.renderTacticScopeOptions();
        this.renderTacticSessionTabs();
        this.tacticSessionReplayId = id;
        if (this.tacticTextMode) {
            try {
                await this.replayTacticText(false);
            } finally {
                if (this.tacticSessionReplayId === id) this.tacticSessionReplayId = null;
            }
            return;
        }
        const requestId = ++this.tacticRequestId;
        this.setTacticBusy(true);
        let snapshot: TTAssistSnapshot = null;
        const accepted: string[] = [];
        let failedAt: number | null = null;
        try {
            await this.theoremValidation.waitForIdle();
            if (requestId !== this.tacticRequestId) return;
            snapshot = await this.startAssistSession(session.target, []);
            this.tacticDefinitionsRevision = this.definitionRevision;
            this.assistSnapshot = snapshot;
            for (let index = 0; index < session.history.length; index++) {
                failedAt = index + 1;
                this.mode = [session.target, ...accepted];
                snapshot = await this.applyAssistCommand(session.history[index]);
                accepted.splice(0, accepted.length, ...snapshot.history);
                this.assistSnapshot = snapshot;
            }
            this.mode = [session.target, ...accepted];
            this.proofSessions.update(id, { history: accepted, stale: false });
            if (this.tacticCaptureBlockedSessionId === id) this.tacticCaptureBlockedSessionId = null;
            this.renderAssistSnapshot(snapshot);
        } catch (error) {
            if (requestId !== this.tacticRequestId) return;
            this.mode = [session.target, ...accepted];
            this.proofSessions.update(id, { stale: true });
            this.tacticCaptureBlockedSessionId = id;
            if (snapshot) this.renderAssistSnapshot(snapshot);
            document.getElementById("tactic-errmsg").innerText = failedAt === null
                ? this.formatTacticError(error)
                : `第 ${failedAt} 行：${this.formatTacticError(error)}`;
        } finally {
            if (this.tacticSessionReplayId === id) this.tacticSessionReplayId = null;
            if (requestId === this.tacticRequestId) this.setTacticBusy(false);
            this.renderTacticSessionTabs();
        }
    }
    private parseTacticScript(text: string) {
        return text.split(/\r?\n/).map((raw, index) => {
            let command = raw.trim();
            // Existing saved/copyable tactic lines may carry the old visual
            // trailing period. It is presentation syntax, not an argument.
            command = command.replace(/\s+\.$/, "").trim();
            return { command, lineNumber: index + 1 };
        }).filter(entry => !!entry.command);
    }
    private renderTacticTextRecommendations(tactics: string[]) {
        const container = document.getElementById("tactic-script-recommendations");
        if (!container) return;
        container.replaceChildren();
        const visible = this.unlockedTactics
            ? tactics.filter(tactic => this.unlockedTactics.has(tactic.split(" ", 1)[0]))
            : tactics;
        if (!visible.length) return;
        container.appendChild(document.createTextNode(TR("推荐：")));
        visible.forEach((tactic, index) => {
            if (index) container.appendChild(document.createTextNode("  |  "));
            const code = document.createElement("code");
            code.textContent = tactic;
            container.appendChild(code);
        });
    }
    private renderTacticTextSnapshot(
        snapshot: TTAssistSnapshot,
        error = "",
        errorLine: number | null = null,
        terminal = false
    ) {
        const mode = document.getElementById("tactic-text-mode");
        const state = document.getElementById("tactic-script-state") as HTMLDivElement | null;
        const errorDiv = document.getElementById("tactic-script-error");
        const script = document.getElementById("tactic-script") as HTMLTextAreaElement | null;
        if (!mode || !state || !errorDiv || !script) return;
        this.assistSnapshot = snapshot;
        this.getHottTacticDefCtxt(this.getActiveTacticScopeId());
        this.renderTacticScopeOptions();
        mode.classList.remove("hide");
        document.getElementById("tactic-clear")?.classList.remove("hide");
        document.getElementById("tactic-list")?.parentElement?.classList?.add?.("hide");
        if (script.value !== this.tacticScript) {
            script.value = this.tacticScript;
            this.tacticScriptEditor?.refresh();
        }
        errorDiv.replaceChildren();
        if (error) {
            const line = document.createElement("div");
            line.className = "proof-text-line-error";
            line.textContent = errorLine === null
                ? this.formatTacticError(error)
                : `第 ${errorLine} 行：${this.formatTacticError(error)}`;
            errorDiv.appendChild(line);
        } else if (terminal) {
            const done = document.createElement("div");
            const complete = snapshot.goals.length === 0;
            done.className = complete ? "proof-text-status" : "proof-text-line-error";
            done.textContent = complete
                ? "qed 已就绪，Ctrl+Enter/执行到光标提交；执行全部运行整页"
                : "qed 未就绪：仍有未完成的证明目标";
            errorDiv.appendChild(done);
        }
        state.replaceChildren();
        this.updateTacticStateDisplay(snapshot, state);
        this.renderTacticTextRecommendations(snapshot.tactics);
    }
    private toggleTacticTextMode() {
        if (!(this.mode instanceof Array)) {
            document.getElementById("tactic-errmsg").innerText = TR("请在定理列表中点选待证命题");
            return;
        }
        this.tacticTextMode = !this.tacticTextMode;
        this.tacticTextModePreference = this.tacticTextMode;
        try {
            window.localStorage.setItem(tacticTextModeStorageKey, this.tacticTextMode ? "1" : "0");
        } catch { }
        this.onStateChange();
        const textMode = document.getElementById("tactic-text-mode");
        const buttonMode = document.getElementById("tactic-list")?.parentElement;
        const script = document.getElementById("tactic-script") as HTMLTextAreaElement | null;
        if (this.tacticTextMode) {
            if (!this.tacticScriptDirty) this.tacticScript = this.mode.slice(1).join("\n");
            if (script) {
                script.value = this.tacticScript;
                this.tacticScriptEditor?.refresh();
            }
            textMode?.classList?.remove?.("hide");
            buttonMode?.classList?.add?.("hide");
            if (this.assistSnapshot) this.renderTacticTextSnapshot(this.assistSnapshot);
            script?.focus();
        } else {
            textMode?.classList?.add?.("hide");
            buttonMode?.classList?.remove?.("hide");
            if (this.assistSnapshot) this.renderAssistSnapshot(this.assistSnapshot);
        }
    }
    private scheduleTacticTextReplay() {
        if (!this.tacticTextMode || !(this.mode instanceof Array)) return;
        if (this.tacticTextReplayTimer !== null) window.clearTimeout(this.tacticTextReplayTimer);
        this.tacticTextReplayTimer = window.setTimeout(() => {
            this.tacticTextReplayTimer = null;
            void this.replayTacticText(false, true);
        }, 350);
    }
    private async commitTacticQed(qedName?: string) {
        const result = await this.finishAssistProof();
        const output = this.updateInhabitList(
            this.getTacticOutputInsertPosition(),
            this.getTacticOutputFolder()
        );
        output.focus();
        output.value = qedName
            ? `${qedName}:=${result.proof}:${result.theorem}`
            : `${result.proof}:${result.theorem}`;
        output.dispatchEvent(new Event("input"));
        this.resetTacticPage();
        output.blur();
    }
    private async replayTacticText(explicitRun: boolean, toCursor = false) {
        if (!this.tacticTextMode || !(this.mode instanceof Array)) return;
        if (this.tacticBusy) {
            this.scheduleTacticTextReplay();
            return;
        }
        const script = document.getElementById("tactic-script") as HTMLTextAreaElement | null;
        if (script) this.tacticScript = script.value;
        const target = this.mode[0];
        const source = toCursor && script ? scriptThroughCaret(script) : this.tacticScript;
        const entries = this.parseTacticScript(source);
        const requestId = ++this.tacticRequestId;
        let accepted: string[] = [];
        let snapshot: TTAssistSnapshot = null;
        let errorLine: number | null = null;
        let terminal = false;
        this.setTacticBusy(true);
        try {
            this.mode = [target];
            snapshot = await this.startAssistSession(target, []);
            if (requestId !== this.tacticRequestId || !this.tacticTextMode) return;
            this.assistSnapshot = snapshot;
            this.tacticDefinitionsRevision = this.definitionRevision;
            for (let index = 0; index < entries.length; index++) {
                const entry = entries[index];
                const commandName = entry.command.split(/\s+/, 1)[0];
                errorLine = entry.lineNumber;
                if (commandName === "qed") {
                    if (index !== entries.length - 1) {
                        throw new Error("qed 必须是策略序列的最后一行");
                    }
                    terminal = true;
                    break;
                }
                this.mode = [target, ...accepted];
                snapshot = await this.applyAssistCommand(entry.command);
                if (requestId !== this.tacticRequestId || !this.tacticTextMode) return;
                accepted = [...snapshot.history];
                this.mode = [target, ...accepted];
                this.assistSnapshot = snapshot;
                this.tacticDefinitionsRevision = this.definitionRevision;
            }
            this.mode = [target, ...accepted];
            this.assistSnapshot = snapshot;
            if (this.proofSessions.activeId) {
                this.proofSessions.update(this.proofSessions.activeId, {
                    target,
                    history: accepted,
                    script: this.tacticScript,
                    stale: false
                });
                if (this.tacticCaptureBlockedSessionId === this.proofSessions.activeId) {
                    this.tacticCaptureBlockedSessionId = null;
                }
            }
            if (terminal && explicitRun) {
                const qed = entries.at(-1)?.command.match(/^qed(?:\s+([^\s]+))?$/);
                const qedName = qed?.[1];
                if (qedName) {
                    const nameAst = parser.parse(qedName);
                    if (nameAst?.type !== "var" || nameAst.name !== qedName) {
                        throw new Error(TR("qed命名参数必须是单个常量名"));
                    }
                }
                await this.commitTacticQed(qedName);
                return;
            }
            this.renderTacticTextSnapshot(snapshot, "", null, terminal);
            this.renderTacticSessionTabs();
            this.onStateChange();
        } catch (error) {
            if (requestId !== this.tacticRequestId || !this.tacticTextMode) return;
            this.mode = [target, ...accepted];
            if (snapshot) this.assistSnapshot = snapshot;
            if (this.proofSessions.activeId) {
                this.proofSessions.update(this.proofSessions.activeId, {
                    target,
                    history: accepted,
                    script: this.tacticScript
                });
                this.tacticCaptureBlockedSessionId = this.proofSessions.activeId;
            }
            if (this.assistSnapshot) this.renderTacticTextSnapshot(this.assistSnapshot, String(error), errorLine);
            this.renderTacticSessionTabs();
            this.onStateChange();
        } finally {
            if (requestId === this.tacticRequestId) this.setTacticBusy(false);
        }
    }
    /**
     * Assist tactics are configured when a Worker session starts.  Keep the
     * option change in TTGui as the source of truth and invalidate the active
     * session so the next command is rebuilt with the newly unlocked tactic.
     */
    private setAssistOption(option: keyof TTAssistOptions, value: boolean) {
        if (this.assistOptions[option] === value) return;
        this.assistOptions = { ...this.assistOptions, [option]: value };
        this.assistSnapshot = null;
        this.tacticDefinitionsRevision = -1;
        this.assistWorkerSessionReady = false;
        this.tacticRequestId++;
        this.setTacticBusy(false);
    }
    enableAssistDestructEq() {
        this.setAssistOption("disableDestructEq", false);
        Assist.disableDestructEq = false;
    }
    enableAssistDestructConds() {
        this.setAssistOption("disableDestructConds", false);
        Assist.disableDestructConds = false;
    }
    enableAssistMultipleApply() {
        this.setAssistOption("disableMultipleApply", false);
        Assist.disableMultipleApply = false;
    }
    private clearTacticRuntime() {
        this.tacticRequestId++;
        this.tacticTextReplayRevision++;
        if (this.tacticTextReplayTimer !== null) {
            window.clearTimeout(this.tacticTextReplayTimer);
            this.tacticTextReplayTimer = null;
        }
        this.tacticScript = "";
        this.tacticScriptDirty = false;
        this.tacticSelectingTarget = false;
        this.mode = null;
        this.assistSnapshot = null;
        this.tacticDefinitionsRevision = -1;
        this.assistWorkerSessionReady = false;
        this.tacticTargetInput = null;
        this.tacticScopeFolderId = null;
        this.tacticScopeExplicit = false;
        this.renderTacticScopeOptions();
        document.getElementById("tactic-autofill").innerHTML = "";
        document.getElementById("tactic-hint").innerHTML = "";
        document.getElementById("tactic-errmsg").innerText = "";
        document.getElementById("tactic-state").innerHTML = "";
        document.getElementById("tactic-remove").classList.add("hide");
        document.getElementById("tactic-begin").classList.add("hide");
        document.getElementById("tactic-clear").classList.add("hide");
        document.getElementById("copygate").classList.remove("hide");
        const input = document.getElementById("tactic-input") as HTMLInputElement;
        input.value = "";
        this.resizeTacticInput();
        input.classList.add("hide");
        const script = document.getElementById("tactic-script") as HTMLTextAreaElement | null;
        if (script) {
            script.value = "";
            this.tacticScriptEditor?.refresh();
        }
        document.getElementById("tactic-text-mode")?.classList?.add?.("hide");
        document.getElementById("tactic-list")?.parentElement?.classList?.remove?.("hide");
        this.setTacticBusy(false);
        this.assistWorker?.clear().catch(() => { });
        this.assistFallback.clear();
    }
    private closeTacticSession() {
        this.captureActiveTacticSession();
        const closingId = this.proofSessions.activeId;
        if (closingId) this.proofSessions.close();
        if (this.tacticSessionReplayId === closingId) this.tacticSessionReplayId = null;
        if (this.tacticCaptureBlockedSessionId === closingId) this.tacticCaptureBlockedSessionId = null;
        const nextId = this.proofSessions.activeId;
        this.clearTacticRuntime();
        this.renderTacticSessionTabs();
        this.onStateChange();
        if (nextId) void this.activateTacticSession(nextId, false);
    }
    private resetTacticPage() {
        this.captureActiveTacticSession();
        const activeId = this.proofSessions.activeId;
        if (!activeId) {
            this.beginTacticTargetSelection();
            return;
        }
        this.proofSessions.reset(activeId);
        if (this.tacticSessionReplayId === activeId) this.tacticSessionReplayId = null;
        if (this.tacticCaptureBlockedSessionId === activeId) this.tacticCaptureBlockedSessionId = null;
        this.clearTacticRuntime();
        this.tacticSelectingTarget = true;
        this.mode = "tactic-begin";
        document.getElementById("tactic-hint").innerText = TR("请在定理列表中点选待证命题");
        this.renderTacticSessionTabs();
        this.onStateChange();
    }
    private async removeTactic(all = false) {
        if (this.tacticBusy) return;
        if (!(this.mode instanceof Array) || this.mode.length <= 1 || all) {
            this.resetTacticPage();
            return;
        }

        this.mode.pop();
        this.setTacticBusy(true);
        const requestId = ++this.tacticRequestId;
        try {
            let snapshot: TTAssistSnapshot;
            if (this.tacticDefinitionsRevision === this.definitionRevision && this.assistWorker) {
                try {
                    snapshot = await this.assistWorker.undo(Core.timeout);
                    this.assistWorkerSessionReady = true;
                } catch (workerError) {
                    if (!shouldFallbackToSynchronousTheoremValidation(workerError)) throw workerError;
                    snapshot = await this.startAssistFallback(this.mode[0], this.mode.slice(1));
                    this.assistWorkerSessionReady = false;
                }
            } else {
                snapshot = await this.startAssistSession(this.mode[0], this.mode.slice(1));
            }
            if (requestId !== this.tacticRequestId || !(this.mode instanceof Array)) return;
            this.tacticDefinitionsRevision = this.definitionRevision;
            this.mode = [this.mode[0], ...snapshot.history];
            if (this.tacticTextMode) {
                this.tacticScript = snapshot.history.join("\n");
                this.tacticScriptDirty = false;
                const script = document.getElementById("tactic-script") as HTMLTextAreaElement | null;
                if (script) {
                    script.value = this.tacticScript;
                    this.tacticScriptEditor?.refresh();
                }
            }
            if (this.proofSessions.activeId) {
                this.proofSessions.update(this.proofSessions.activeId, {
                    history: snapshot.history,
                    script: this.tacticScriptDirty ? this.tacticScript : snapshot.history.join("\n"),
                    stale: false
                });
                if (this.tacticCaptureBlockedSessionId === this.proofSessions.activeId) {
                    this.tacticCaptureBlockedSessionId = null;
                }
            }
            this.renderAssistSnapshot(snapshot);
            this.renderTacticSessionTabs();
            this.onStateChange();
        } catch (error) {
            if (requestId === this.tacticRequestId) {
                document.getElementById("tactic-errmsg").innerText = this.formatTacticError(error);
            }
        } finally {
            if (requestId === this.tacticRequestId) this.setTacticBusy(false);
        }
    }
    private async startAssistSession(target: string, history: string[] = []) {
        const definitionEnd = this.getTacticDefinitionEnd();
        const scopeFolderId = this.getActiveTacticScopeId();
        this.ensureAssistWorker();
        if (this.assistWorker) {
            try {
                await this.prepareAssistWorker(
                    definitionEnd,
                    this.getWorkerSystemConfig(),
                    this.getTacticWorkerDefinitionSlots(scopeFolderId),
                    scopeFolderId,
                    "tactic"
                );
                await this.assistWorkerMutations.wait();
                const snapshot = await this.assistWorker.start(target, this.assistOptions, history, Core.timeout);
                this.assistWorkerSessionReady = true;
                return snapshot;
            } catch (workerError) {
                if (!shouldFallbackToSynchronousTheoremValidation(workerError)) throw workerError;
                try {
                    const snapshot = await this.startAssistFallback(target, history);
                    this.assistWorkerSessionReady = false;
                    return snapshot;
                } catch (fallbackError) {
                    throw fallbackError ?? workerError;
                }
            }
        }
        return this.startAssistFallback(target, history);
    }
    private ensureAssistWorker() {
        if (this.assistWorker) return this.assistWorker;
        try {
            this.assistWorker = new TTAssistWorkerClient();
        } catch (error) {
            console.warn("Proof-assistant worker unavailable", error);
        }
        return this.assistWorker;
    }
    private async startAssistFallback(target: string, history: string[], config?: TTCoreConfig) {
        const scopeFolderId = this.getActiveTacticScopeId();
        config ??= this.getTacticWorkerConfig(scopeFolderId);
        this.assistFallback.configure(config);
        return this.assistFallback.start(target, this.assistOptions, history);
    }
    private async ensureAssistSessionCurrent() {
        if (!(this.mode instanceof Array)) throw new Error(TR("请在定理列表中点选待证命题"));
        const workerSessionCurrent = !this.assistWorker
            || (this.assistWorkerSessionReady && this.assistWorkerGeneration === this.assistWorker.generation);
        if (this.tacticDefinitionsRevision === this.definitionRevision
            && workerSessionCurrent) return this.assistSnapshot;
        const snapshot = await this.startAssistSession(this.mode[0], this.mode.slice(1));
        this.tacticDefinitionsRevision = this.definitionRevision;
        this.mode = [this.mode[0], ...snapshot.history];
        this.assistSnapshot = snapshot;
        return snapshot;
    }
    private async applyAssistCommand(command: string) {
        await this.ensureAssistSessionCurrent();
        if (this.assistWorker) {
            try {
                const snapshot = await this.assistWorker.apply(command, Core.timeout);
                this.assistWorkerSessionReady = true;
                return snapshot;
            } catch (workerError) {
                if ((workerError as any)?.operationError) throw workerError;
                if (!shouldFallbackToSynchronousTheoremValidation(workerError)) throw workerError;
                try {
                    await this.startAssistFallback(this.mode[0], this.mode.slice(1));
                    const snapshot = this.assistFallback.apply(command);
                    this.assistWorkerSessionReady = false;
                    return snapshot;
                } catch (fallbackError) {
                    throw fallbackError ?? workerError;
                }
            }
        }
        await this.startAssistFallback(this.mode[0], this.mode.slice(1));
        return this.assistFallback.apply(command);
    }
    private async finishAssistProof(): Promise<TTAssistQedResult> {
        await this.ensureAssistSessionCurrent();
        if (this.assistWorker) {
            try {
                return await this.assistWorker.qed(Core.timeout);
            } catch (workerError) {
                if ((workerError as any)?.operationError) throw workerError;
                if (!shouldFallbackToSynchronousTheoremValidation(workerError)) throw workerError;
                try {
                    await this.startAssistFallback(this.mode[0], this.mode.slice(1));
                    return this.assistFallback.qed();
                } catch (fallbackError) {
                    throw fallbackError ?? workerError;
                }
            }
        }
        await this.startAssistFallback(this.mode[0], this.mode.slice(1));
        return this.assistFallback.qed();
    }
    private renderAssistSnapshot(snapshot: TTAssistSnapshot) {
        this.assistSnapshot = snapshot;
        if (this.tacticTextMode) {
            this.renderTacticTextSnapshot(snapshot);
            return;
        }
        this.getHottTacticDefCtxt(this.getActiveTacticScopeId());
        this.renderTacticScopeOptions();
        const hint = document.getElementById("tactic-hint");
        const statediv = document.getElementById("tactic-state") as HTMLDivElement;
        hint.innerHTML = "";
        statediv.innerHTML = "";
        if (this.mode instanceof Array) {
            for (const command of this.mode.slice(1)) {
                // Keep history text identical to the command accepted by the
                // assistant. The old display-only ` . ` suffix was copied
                // with a selected line, so pasting it back made a valid tactic
                // look like an invalid command. Each blocked span is already
                // a visual line on its own.
                this.addSpan(statediv, command).className = "blocked";
            }
        }
        this.updateTacticStateDisplay(snapshot, statediv);
        this.autofillTactics(snapshot.tactics);
        const holes = snapshot.goals.map(goal => [goal.holeName, goal.type, 0] as [string, AST, number]);
        hint.appendChild(this.ast2HTML("", {
            type: ":",
            name: "",
            nodes: [snapshot.elem, snapshot.theorem]
        }, [], holes, this.getInhabitatArray().length));
        document.getElementById("tactic-remove").classList.remove("hide");
        document.getElementById("tactic-begin").classList.remove("hide");
        document.getElementById("tactic-clear").classList.remove("hide");
        document.getElementById("copygate").classList.add("hide");
        const input = document.getElementById("tactic-input") as HTMLInputElement;
        input.classList.remove("hide");
        this.resizeTacticInput();
        window.scrollTo(0, document.body.clientHeight);
        const wrapperDiv = document.getElementById("tactic-list").parentElement;
        wrapperDiv.scrollTo(0, document.getElementById("tactic-list").clientHeight);
    }
    private formatTacticError(error: unknown) {
        return String(error).replace(/^Error:\s*/, "");
    }
    private renderAstInScope(
        idx: string,
        ast: AST,
        scopes: AST[] = [],
        context: Context = [],
        userLineNumber = 0,
        scopeFolderId: string | null = null
    ) {
        const previousScope = this.astRenderScopeFolderId;
        this.astRenderScopeFolderId = scopeFolderId;
        try {
            return this.ast2HTML(idx, ast, scopes, context, userLineNumber);
        } finally {
            this.astRenderScopeFolderId = previousScope;
        }
    }

    /**
     * Render an AST owned by the creative sandbox without borrowing the first
     * theorem's scope for hover/type lookup.  The sandbox has no theorem row,
     * so use the end-of-list position and an explicit global scope.
     */
    renderSandboxAst(ast: AST) {
        return this.renderAstInScope(
            "",
            ast,
            [],
            [],
            this.getInhabitatArray().length,
            null
        );
    }
    private addSpan(parentSpan: HTMLSpanElement, text: string, parseHTML?: boolean) {
        const span = document.createElement("span");
        if (parseHTML) span.innerHTML = text; else span.innerText = text;
        parentSpan.appendChild(span);
        return span;
    }
    ast2HTML(idx: string, ast: AST, scopes: AST[] = [], context: Context = [], userLineNumber = 0) {
        const varnode = document.createElement("span");
        if (!ast) {
            varnode.innerText = TR("表达式因错误而丢失");
            return varnode;
        }
        if (ast.type === "=" && this.disableSimpleEq && ast.nodes[0].checked) {
            const eq = wrapVar("eq");
            eq.checked = wrapLambda("->", "", ast.nodes[0].checked, wrapLambda("->", "", ast.nodes[0].checked, ast.checked));
            const app = wrapApply(eq, ast.nodes[0], ast.nodes[1]);
            app.checked = ast.checked;
            return this.ast2HTML(idx, app, scopes, context, userLineNumber);
        }
        const astStr = parser.stringify(ast);
        varnode.setAttribute("ast-string", astStr);
        if (ast.type === "var") {
            if (idx === "Checked" && ast.name === "_" && ast.checked?.type === ":") {
                return this.ast2HTML("Checked", ast.checked.nodes[0], scopes, context, userLineNumber);
            }
            let el: HTMLSpanElement;
            if (ast.name.startsWith("@") && (isFinite(Number(ast.name.slice(1))) || ast.name === "@succ" || ast.name === "@max")) {
                el = this.addSpan(varnode, "<sub>" + ast.name + "</sub>", true);
                el.classList.add("universe");
            } else if (ast.name.startsWith("U@")) {
                el = this.addSpan(varnode, "U<sub>" + ast.name.slice(1) + "</sub>", true);
                el.classList.add("universe");
            } else {
                el = this.addSpan(varnode, ast.name);
            }
            if (debugBoundVarId && ast.bondVarId) {
                this.addSpan(el, "<sup>" + ast.bondVarId + "</sup>", true);
            }
            const scopeStack = scopes.slice(0);
            const astname = ast.name.replace(/'+$/g, "");
            if (astname.match(/^[1-9][0-9]*$/)) el.classList.add("constructors");
            else if (computeEqs.has(astname)) el.classList.add("compute_eqs");
            else if (destructors.has(astname)) el.classList.add("ind_fn");
            else if (constructors.has(astname)) el.classList.add("constructors");
            else if (consts.has(astname)) el.classList.add("constant");
            else if (this.isKnownTheoremName(astname, userLineNumber)) el.classList.add("macro");
            else if (!ast.name.startsWith("U@")) {
                el.classList.add("freeVar");
            }
            if (scopeStack[0]?.type === "quantvar") {
                // quantvar is only aimed for mark css style
                if (!el.classList.contains("replvar")) {
                    el.classList.remove("freeVar");
                    el.classList.remove("constant");
                    el.classList.add("boundedVar");
                }
                scopeStack.shift();
            } else {
                do {
                    if (ast.type === "var" && scopeStack[0] && scopeStack[0]?.name === ast.name) {
                        varnode.setAttribute("ast-scope", parser.stringify(scopeStack[0]));
                        if (!el.classList.contains("replvar")) {
                            el.classList.remove("freeVar");
                            el.classList.add("boundedVar");
                        }
                        break;
                    }
                } while (scopeStack.shift());
            }
        } else {
            switch (ast.type) {
                case "[]": case "[[]]":
                    this.addSpan(varnode, ast.type === "[]" ? " |" : " ||");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    this.addSpan(varnode, ast.type === "[]" ? "| " : "|| ");
                    break;
                case ":": case ":=": case "===":
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    this.addSpan(varnode, " &nbsp;" + (ast.type === "===" ? "≡" : ast.type) + "&nbsp; ", true);
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    break;
                case "->": case "X": case "+":

                    const b1 = !(((ast.type === "+" || ast.type === "->") && ast.nodes[0].type === "X") || ["var", "=", "~=", "*"].includes(ast.nodes[0].type) || ast.nodes[0].nodes[0].name == "U");

                    const b2 = !(((ast.type === "+" || ast.type === "->") && ast.nodes[1].type === "X") || (["var", "->", "X"].includes(ast.nodes[1].type) && ast.type !== "X") || ["var"].includes(ast.nodes[1].type) || ast.nodes[1].nodes[0].name == "U");
                    if (b1) this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    if (b1) this.addSpan(varnode, ")");
                    this.addSpan(varnode, ast.type === "X" ? "×" : ast.type === "+" ? "+" : "→");
                    if (b2) this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    if (b2) this.addSpan(varnode, ")");
                    break;
                case ",": case "~": case "~=": case "=": case "*":
                    const bra = !["var", ",", "*", "[[]]", "[]", "~=", "="].includes(ast.nodes[0].type) && ast.type !== ",";
                    const brb = !["var", ",", "*", "[[]]", "[]", "~=", "="].includes(ast.nodes[1].type) && ast.type !== ",";
                    if (!(bra && brb)) this.addSpan(varnode, "(");
                    if (bra) this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    if (bra) this.addSpan(varnode, ")");
                    this.addSpan(varnode, ast.type === "," ? "," : ast.type === "~" ? " ~ " : ast.type === "~=" ? " ≃ " : ast.type === "*" ? "▪" : " = ");
                    if (brb) this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    if (brb) this.addSpan(varnode, ")");
                    if (!(bra && brb)) this.addSpan(varnode, ")");
                    break;
                case "apply":
                    if (ast.nodes[0].name === "U") {
                        const sub = parser.stringify(ast.nodes[1]);
                        this.addSpan(varnode, `U<sub>${sub.replaceAll(/@([0-9])/g, "$1")}</sub>`, true).classList.add("universe");
                        break;
                    }
                    const br1 = !["apply", "var", ",", "=", "*", "~=", "[[]]", "[]"].includes(ast.nodes[0].type);
                    const br2 = !(["var", ",", "*", "=", "~=", "[[]]", "[]"].includes(ast.nodes[1].type) || ast.nodes[1].nodes[0].name == "U");
                    if (br1) this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    if (br1) this.addSpan(varnode, ")");
                    this.addSpan(varnode, "&nbsp;", true);
                    if (br2) this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    if (br2) this.addSpan(varnode, ")");
                    break;
                case "L": case "P": case "S": case "W":
                    const outterLayers: HTMLSpanElement[] = [];
                    const newcontext = Object.assign({}, context);
                    const newType = Core.clone(ast.nodes[0]); //this.hott.unbeautify(newType);
                    newcontext[ast.name] = newType;
                    outterLayers.push(this.addSpan(varnode, "" + ast.type.replace("S", "Σ").replace("L", "λ").replace("P", this.displayPi ? "Π" : "(")));
                    const varast = this.ast2HTML(idx, { type: "var", name: ast.name, checked: ast.nodes[0] }, [{ type: "quantvar", name: "quantvar" }, ...scopes], newcontext, userLineNumber);
                    varast.classList.add("boundedVar");
                    if (debugBoundVarId && ast.bondVarId) {
                        this.addSpan(varast, "<sup>" + ast.bondVarId + "</sup>", true);
                    }
                    outterLayers.push(varnode.appendChild(varast));
                    outterLayers.push(this.addSpan(varnode, ":"));
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    outterLayers.push(this.addSpan(varnode, ast.type === "L" ? "." : ast.type === "P" && !this.displayPi ? ")→" : ","));
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], [ast, ...scopes], newcontext, userLineNumber));
                    // outterLayers.push(this.addSpan(varnode, ")"));

                    // hightlight constrained vars

                    const constrainedVars = Array.from(varnode.querySelectorAll("span")).filter(
                        node => (node as HTMLSpanElement).getAttribute("ast-scope") === astStr
                    ) as HTMLSpanElement[];
                    for (const node of constrainedVars) {
                        node.addEventListener('mouseover', ev => {
                            for (const node of outterLayers) {
                                node.classList.add("highlighted");
                            }
                        });
                        node.addEventListener('mouseout', ev => {
                            for (const node of outterLayers) {
                                node.classList.remove("highlighted");
                            }
                        });
                    }
                    outterLayers[1].addEventListener('mouseover', ev => {
                        varnode.classList.add("mediumlighted");
                        for (const node of constrainedVars) {
                            node.classList.add("highlighted");
                        }
                    });
                    outterLayers[1].addEventListener('mouseout', ev => {
                        varnode.classList.remove("mediumlighted");
                        for (const node of constrainedVars) {
                            node.classList.remove("highlighted");
                        }
                    });
                    break;
            }
        }

        // clicks and hovers in this layer
        const spans = Array.from(varnode.childNodes).filter(
            node => !(node as HTMLSpanElement).getAttribute("ast-string")
        ) as HTMLSpanElement[];
        const floatTypeDiv = this.floatTypeDiv ??= document.querySelector(".float-type") as HTMLDivElement;
        const renderedInput = this.getInhabitatArray()[userLineNumber];
        const renderedItemId = renderedInput ? this.getTheoremItemForInput(renderedInput)?.id : null;
        const renderedScopeOverride = this.astRenderScopeFolderId;
        for (const node of spans) {
            const localCtxt = context;
            const localNumber = userLineNumber;
            node.addEventListener('mouseover', ev => {
                if (this.mouseoutTimeout) {
                    window.clearTimeout(this.mouseoutTimeout);
                }
                floatTypeDiv.innerHTML = "";
                this.mouseoutTimeout = null;
                varnode.classList.add("mediumlighted");
                for (const node of spans) {
                    node.classList.add("highlighted");
                }
                floatTypeDiv.style.left = '';
                floatTypeDiv.style.right = '';
                floatTypeDiv.style.width = '';
                floatTypeDiv.style.maxWidth = '';
                floatTypeDiv.style.wordBreak = '';

                floatTypeDiv.style.left = (ev.pageX - 4) + "px";
                floatTypeDiv.style.top = (ev.pageY + 30) + "px";
                const localInput = renderedItemId
                    ? this.theoremItems.find((item): item is Extract<TTTheoremItem, { kind: "theorem" }> =>
                        item.kind === "theorem" && item.id === renderedItemId)?.input
                    : this.getInhabitatArray()[localNumber];
                const currentNumber = localInput ? this.getInhabitatArray().indexOf(localInput) : localNumber;
                this.getHottDefCtxt(currentNumber, this.getDefaultTacticScope(localInput));
                floatTypeDiv.style.display = "block";
                if (ast.checked) {
                    if (scopes[0]?.type === "quantvar") {
                        scopes = scopes.slice(1);
                    }
                    try {
                        const checkedHtml = renderedScopeOverride === undefined
                            ? this.ast2HTML("Checked", ast.checked, scopes, localCtxt, userLineNumber)
                            : this.renderAstInScope(
                                "Checked",
                                ast.checked,
                                scopes,
                                localCtxt,
                                userLineNumber,
                                renderedScopeOverride
                            );
                        floatTypeDiv.appendChild(checkedHtml);
                    } catch (e) {
                        floatTypeDiv.innerText = e;
                    }
                } else if (ast.err) {
                    floatTypeDiv.appendChild(document.createTextNode(ast.err));
                } else {
                    floatTypeDiv.style.display = "none"; return;
                }
                // deal with hint position on screen
                const pad = 10;
                const rect = floatTypeDiv.getBoundingClientRect();
                const viewWidth = window.innerWidth;

                if (rect.right > viewWidth - pad) {
                    floatTypeDiv.style.left = 'auto';
                    floatTypeDiv.style.right = (pad) + 'px';

                    const rect2 = floatTypeDiv.getBoundingClientRect();
                    if (rect2.left < pad) {
                        floatTypeDiv.style.left = pad + 'px';
                        floatTypeDiv.style.right = pad + 'px';
                        floatTypeDiv.style.width = 'auto';
                        floatTypeDiv.style.wordBreak = 'break-all';
                    }
                }
                else if (rect.left < pad) {
                    floatTypeDiv.style.left = pad + 'px';
                }

            });
            node.addEventListener('mouseout', ev => {
                varnode.classList.remove("mediumlighted");
                for (const node of spans) {
                    node.classList.remove("highlighted");
                }
                if (!this.mouseoutTimeout) {
                    this.mouseoutTimeout = window.setTimeout(() => {
                        floatTypeDiv.style.display = "none";
                        floatTypeDiv.innerHTML = "";
                        this.mouseoutTimeout = null;
                    }, 100);
                }
            });
        }
        return varnode;
    }
    mouseoutTimeout: number;
    private refreshUserConstNames() {
        this.userConstNames.clear();
        const inputs = this.getInhabitatArray();
        for (let i = 0; i < this.userDefinedConsts.length; i++) {
            const definition = this.userDefinedConsts[i];
            if (!definition || this.isTheoremInputDisabled(inputs[i])) continue;
            const item = this.getTheoremItemForInput(i);
            if (item?.localCheckbox.checked) continue;
            this.userConstNames.add(definition[0]);
        }
    }
    private invalidateHottDefCtxt(hard = true) {
        this.hottDefCtxtKey = null;
        this.hottDefCtxtMacroNames = null;
        if (hard) {
            this.hottDefCtxtCore = null;
            this.hottDefCtxtMaterialized = null;
        }
    }
    private isKnownTheoremName(name: string, userLineNumber: number) {
        if (isKnownTheoremIdentifier(name, consts, sysmacro)) return true;
        const inputs = this.getInhabitatArray();
        const definitionEnd = Math.max(0, Math.min(userLineNumber, inputs.length));
        const scopeId = this.astRenderScopeFolderId !== undefined
            ? this.astRenderScopeFolderId
            : definitionEnd < inputs.length
            ? this.getDefaultTacticScope(inputs[definitionEnd])
            : this.getActiveTacticScopeId();
        // The declaration currently being rendered is not part of the
        // preceding context (and must not be usable by its own type check),
        // but its name should still render as a known declaration instead of
        // a black free variable on the theorem row.
        if (this.userDefinedConsts[definitionEnd]?.[0] === name) return true;
        if (this.findVisibleDefinitionIndex(name, definitionEnd, scopeId) >= 0) return true;
        // System declarations are always available. User definitions are
        // handled above so a name from another local folder stays visually
        // unknown instead of appearing as an available macro.
        return Object.prototype.hasOwnProperty.call(this.core.state.sysTypes ?? {}, name)
            || Object.prototype.hasOwnProperty.call(this.core.state.sysDefs ?? {}, name);
    }
    updateTypeList(terms: Set<string>, render = true) {
        this.invalidateHottDefCtxt();
        const list = this.typeList;
        consts.clear();
        constructors.clear();
        destructors.clear();
        computeEqs.clear();
        sysmacro.clear();
        if (render) {
            while (list.lastChild) {
                list.removeChild(list.lastChild);
            }
        }
        const pendingDefinitions = new Map<string, AST>();
        const deferredVariableDisplays: { container: HTMLDivElement, ast: AST }[] = [];
        const disableSimpleEq = this.disableSimpleEq;
        const disableSimpleFn = this.disableSimpleFn;
        for (const rule of allrules) {

            // register systype and sysdef in core
            const vname = rule.ast.nodes?.[0]?.name;
            if (rule.ast.type !== "===") {
                reservedConsts.add(vname);
            }
            if (!terms.has(rule.id)) continue;
            this.core.state.disableSimpleEq = false;
            this.core.state.disableSimpleFn = false;
            if (rule.ast.type === ":" && rule.ast.nodes[0].type === "var") {
                if (this.unlockedTypes.has("// " + vname)) this.core.setSystemType(vname);
                else this.core.setSystemType(
                    vname,
                    this.core.desugar(Core.clone(rule.ast.nodes[1]), true)
                );
            }
            // ast.nodes[0].type==="var" -> skip a X b := @Prod _ _ ...
            if (rule.ast.type === ":=" && rule.ast.nodes[0].type === "var") {
                const val = rule.ast.nodes[1].type === ":" ? rule.ast.nodes[1].nodes[0] : rule.ast.nodes[1];
                if (this.unlockedTypes.has("// " + vname)) this.core.setSystemDefinition(vname);
                else this.core.setSystemDefinition(
                    vname,
                    this.core.desugar(Core.clone(val), true)
                );
            }
            if (this.unlockedTypes.has("// " + vname)) { this.core.clearDefinitionCache(vname); continue; }

            // register in gui highlight, only ignore ====

            if (rule.ast.type === "var" || ((rule.ast.type === ":=" || rule.ast.type === ":") && rule.ast.nodes[0].type === "var")) {
                const vname = rule.ast.type === "var" ? rule.ast.name : rule.ast.nodes[0].name;
                if (rule.postfix === "类型") consts.add(vname);
                if (rule.postfix === "构造") constructors.add(vname);
                if (rule.postfix === "解构") destructors.add(vname);
                if (rule.postfix === "计算") computeEqs.add(vname);
                if (rule.postfix === "定义") sysmacro.add(vname);
            }
            if ((rule.inferMode === "@" && this.inferDisplayMode === "_") || (rule.inferMode === "_" && this.inferDisplayMode === "@")) {
                if (rule.ast.type === ":=") {
                    if (rule.ast.nodes[1].type === ":") {
                        this.core.setSystemType(
                            vname,
                            this.core.desugar(Core.clone(rule.ast.nodes[1].nodes[1]), true)
                        );
                    } else {
                        try {
                            this.core.registerSystemDefinition(vname, rule.ast.nodes[1]);
                        } catch {
                            pendingDefinitions.set(vname, Core.clone(rule.ast.nodes[1]));
                        }
                    }
                }
                continue;
            }

            // register in gui type list

            let itVal: HTMLDivElement | null = null;
            if (render) {
                const itIdx = document.createElement("div");
                list.appendChild(itIdx);
                itIdx.classList.add("idx");
                itIdx.style.width = "30px";
                itIdx.innerText = TR(rule.postfix);

                itVal = document.createElement("div");
                list.appendChild(itVal);
                itVal.classList.add("val");
            }
            const ast = Core.clone(rule.ast);
            // avoid check const for redefined const error
            // const def = this.core.state.sysDefs[vname];
            // delete this.core.state.sysDefs[vname];
            let error = false;
            this.core.state.disableSimpleEq = disableSimpleEq;
            this.core.state.disableSimpleFn = disableSimpleFn;
            // Compute equations are trusted system rewrite rules. Rechecking
            // them on every list render can block startup on meta-heavy rules.
            // The renderless startup pass only seeds the Core; these checks
            // exist to populate display annotations and would duplicate a
            // large amount of main-thread work before the visible rebuild.
            if (render && ast.type !== "===") {
                try { this.core.checkType(ast, [], false); } catch (e) { console.log(e); error = true; }
            }
            // this.core.state.sysDefs[vname] = def;
            if (render && ast.type === "var") {
                if (ast.checked) {
                    const displayAst = restoreSemanticMetaNamesForDisplay(Core.clone(ast, true));
                    itVal!.appendChild(this.ast2HTML("", {
                        type: ":",
                        nodes: [displayAst, displayAst.checked],
                        name: ""
                    }));
                } else {
                    // Some public aliases depend on definitions registered
                    // later in the rule table. Render them after the bounded
                    // fixed-point pass below, when their inferred type caches
                    // are available.
                    deferredVariableDisplays.push({ container: itVal!, ast });
                }
            } else if (render) {
                itVal!.appendChild(this.ast2HTML(
                    "",
                    restoreSemanticMetaNamesForDisplay(Core.clone(ast, true))
                ));
            }
            if (ast.type === ":=") {
                const val = rule.ast.nodes[1].type === ":" ? rule.ast.nodes[1].nodes[0] : rule.ast.nodes[1];
                if (rule.ast.nodes[1].type === ":") {
                    this.core.setSystemType(
                        vname,
                        this.core.desugar(Core.clone(rule.ast.nodes[1].nodes[1]), true)
                    );
                } else if (!error) {
                    try {
                        this.core.registerSystemDefinition(vname, val);
                    } catch {
                        pendingDefinitions.set(vname, Core.clone(val));
                    }
                }
            }
            if (render) {
                for (let i = 0; i < 6; i++) {
                    const itInfo = document.createElement("div");
                    list.appendChild(itInfo);
                    itInfo.className = "info";
                    if (!i) itInfo.innerText = rule.prefix;
                }
            }
        }
        for (let pass = 0; pass < 4 && pendingDefinitions.size; pass++) {
            this.core.elaborateSemanticSystemTypes();
            let progress = false;
            for (const [name, value] of Array.from(pendingDefinitions)) {
                try {
                    this.core.registerSystemDefinition(name, Core.clone(value));
                    pendingDefinitions.delete(name);
                    progress = true;
                } catch { }
            }
            if (!progress) break;
        }
        this.core.elaborateSemanticSystemTypes();
        this.core.syncSemanticDefinitions?.();
        if (render) {
            for (const { container, ast } of deferredVariableDisplays) {
                if (!ast.checked) {
                    try { this.core.checkType(ast, [], false); } catch { }
                }
                const displayType = ast.checked
                    ? restoreSemanticMetaNamesForDisplay(Core.clone(ast.checked, true))
                    : wrapVar("_");
                container.appendChild(this.ast2HTML("", {
                    type: ":",
                    nodes: [ast, displayType],
                    name: ""
                }));
            }
            this.renderSandboxAxioms();
            this.onTypeListUpdated?.();
        }
    }

    private renderSandboxAxioms() {
        // A few DOM-free rendering tests construct a TTGui prototype without
        // running the constructor, so tolerate absent optional sandbox state.
        if (!this.typeList) return;
        const appendEntry = (
            name: string,
            type: AST,
            postfix: string,
            prefix: string,
            category: "type" | "constructor" | "eliminator" | "axiom" | "compute",
            displayOptions: Parameters<typeof prettySandboxInductiveNamesForDisplay>[1] = {}
        ) => {
            // Register trusted names before rendering their types so the
            // first frame gets the same highlighting as subsequent refreshes.
            consts.add(name);
            if (category === "type") consts.add(name);
            if (category === "constructor") constructors.add(name);
            if (category === "eliminator") destructors.add(name);
            if (category === "compute") computeEqs.add(name);

            const idx = document.createElement("div");
            idx.className = "idx";
            idx.style.width = "30px";
            idx.innerText = postfix;
            this.typeList.appendChild(idx);

            const value = document.createElement("div");
            value.className = "val";
            const nameAst: AST = { type: "var", name, nodes: [] };
            const typeAst = prettySandboxInductiveNamesForDisplay(
                restoreSemanticMetaNamesForDisplay(Core.clone(type, true)),
                displayOptions
            );
            nameAst.checked = typeAst;
            value.appendChild(this.ast2HTML("", {
                type: ":",
                name: "",
                nodes: [nameAst, typeAst]
            }));
            this.typeList.appendChild(value);

            for (let index = 0; index < 6; index++) {
                const info = document.createElement("div");
                info.className = "info";
                if (index === 0) info.innerText = prefix;
                this.typeList.appendChild(info);
            }
        };

        for (const [name, type] of this.sandboxAxioms ?? []) {
            appendEntry(name, type, "trusted", "sandbox", "axiom");
        }
        // Transparent sandbox definitions carry their body in the bridge;
        // render the inferred type from the Core semantic cache so they look
        // like ordinary declarations without pretending the body is an axiom
        // type. Older bridges may omit the cache, in which case the definition
        // remains usable but has no type row to render yet.
        for (const [name] of this.sandboxDefinitions ?? []) {
            const type = this.core.state.defTypes[name]?.type;
            if (type) appendEntry(name, type, "定义", "sandbox", "axiom");
        }
        for (const bundle of this.sandboxInductives ?? []) {
            const bundlePrefix = bundle.metadata?.kind === "hit1"
                ? "sandbox HIT"
                : "sandbox inductive";
            const displayOptions = {
                constructorNames: bundle.metadata?.constructors?.map(ctor => ctor.name)
                    ?? bundle.constructors?.map(([name]) => name)
                    ?? []
            };
            appendEntry(
                bundle.type[0],
                bundle.type[1],
                "类型",
                bundlePrefix,
                "type",
                displayOptions
            );
            for (const [name, type] of bundle.constructors ?? []) {
                const presentation = sandboxInductiveEntryPresentation(bundle, name, {
                    postfix: "构造",
                    category: "constructor"
                });
                appendEntry(name, type, presentation.postfix, presentation.prefix,
                    presentation.category, displayOptions);
            }
            for (const [name, type] of bundle.auxiliaryTypes ?? []) {
                const presentation = sandboxInductiveEntryPresentation(bundle, name, {
                    postfix: "解构",
                    category: "eliminator"
                });
                appendEntry(name, type, presentation.postfix, presentation.prefix,
                    presentation.category, displayOptions);
            }
            if (bundle.eliminator) {
                appendEntry(
                    bundle.eliminator[0],
                    bundle.eliminator[1],
                    "解构",
                    bundlePrefix,
                    "eliminator",
                    displayOptions
                );
            }
            if (bundle.recursor) {
                appendEntry(
                    bundle.recursor[0],
                    bundle.recursor[1],
                    "递归",
                    bundlePrefix,
                    "eliminator",
                    displayOptions
                );
            }
            for (const [name, definition] of bundle.definitions ?? []) {
                const presentation = sandboxInductiveEntryPresentation(bundle, name, {
                    postfix: "定义",
                    category: "axiom"
                });
                appendEntry(name, definition, presentation.postfix, presentation.prefix,
                    presentation.category, displayOptions);
            }
        }
    }
    private getTheoremWorkspace() {
        this.theoremWorkspace ??= new TheoremWorkspace();
        return this.theoremWorkspace;
    }

    private theoremWorkspaceItemsFromDom(): TheoremWorkspaceItem[] {
        return this.theoremItems.map((item, index) => {
            if (!item.id) item.id = `${item.kind}-legacy-${index}`;
            return item.kind === "theorem"
                ? {
                    kind: "theorem",
                    id: item.id,
                    value: String(item.input?.value ?? ""),
                    local: !!item.localCheckbox?.checked
                }
                : {
                    kind: "folder",
                    id: item.id,
                    name: item.name,
                    length: item.length,
                    open: item.open,
                    disabled: item.disabled
                };
        });
    }

    private syncTheoremWorkspaceFromDom(force = false) {
        const workspace = this.getTheoremWorkspace();
        // DOM hydration is a compatibility path for tests/legacy callers that
        // construct theoremItems directly.  Normal reads use the already
        // hydrated workspace; replacing the whole list on every scope query
        // made ordered validation O(n^2) for large saves.
        if (force || !this.theoremWorkspaceHydrated) {
            workspace.replace(this.theoremWorkspaceItemsFromDom());
            this.theoremWorkspaceHydrated = true;
        }
        return workspace;
    }

    private applyTheoremWorkspaceSnapshot(
        snapshot: readonly TheoremWorkspaceItem[],
        additionalItems: readonly TTTheoremItem[] = []
    ) {
        const byId = new Map<string, TTTheoremItem>();
        for (const item of [...this.theoremItems, ...additionalItems]) {
            if (item?.id) byId.set(item.id, item);
        }
        const next: TTTheoremItem[] = [];
        for (const record of snapshot) {
            const item = byId.get(record.id);
            if (!item || item.kind !== record.kind) continue;
            if (item.kind === "theorem" && record.kind === "theorem") {
                item.input.value = record.value;
                item.localCheckbox.checked = record.local;
            } else if (item.kind === "folder" && record.kind === "folder") {
                item.name = record.name;
                item.length = record.length;
                item.open = record.open;
                item.disabled = record.disabled;
            }
            next.push(item);
        }
        this.theoremItems = next;
        this.theoremInputsCacheRevision = -1;
        this.theoremWorkspaceHydrated = true;
    }

    private createTheoremItemId(prefix: "theorem" | "folder") {
        const uuid = globalThis.crypto?.randomUUID?.();
        return prefix + "-" + (uuid ?? ++this.theoremItemSequence);
    }
    private createTheoremDragHandle(
        wrapper: HTMLDivElement,
        id: string,
        rowOptions: { folder?: boolean, folderOpen?: boolean } = {}
    ) {
        return createWorkspaceDragHandle(wrapper, id, {
            dragger: this.theoremDragger,
            title: TR("拖动排序"),
            rowOptions
        });
    }
    private syncTheoremDomOrder() {
        const addButton = document.getElementById("add-btn");
        syncWorkspaceDomOrder(
            this.inhabitList,
            this.theoremItems.map(item => item.wrapper),
            addButton
        );
    }
    private appendRestoredTheoremItem(item: TTTheoremItem) {
        this.theoremItems.push(item);
        this.theoremInputsCacheRevision = -1;
        const addButton = document.getElementById("add-btn");
        if (this.inhabitList && addButton) {
            this.inhabitList.insertBefore(item.wrapper, addButton);
        } else {
            this.syncTheoremDomOrder();
        }
    }
    private normalizeTheoremFolderLengths() {
        const workspace = this.syncTheoremWorkspaceFromDom();
        this.applyTheoremWorkspaceSnapshot(workspace.snapshot());
    }
    private scanTheoremFolderScope(targets: string[]) {
        const scopes = this.syncTheoremWorkspaceFromDom().folderScopesForItems(targets);
        const folders = new Map(
            this.theoremItems
                .filter((item): item is Extract<TTTheoremItem, { kind: "folder" }> => item.kind === "folder")
                .map(folder => [folder.id, folder] as const)
        );
        const result = new Map<string, Extract<TTTheoremItem, { kind: "folder" }>[]>;
        for (const [id, folderScopes] of scopes) {
            result.set(id, folderScopes
                .map(folder => folders.get(folder.id))
                .filter((folder): folder is Extract<TTTheoremItem, { kind: "folder" }> => !!folder));
        }
        return result;
    }
    private getTheoremItemForInput(input: HTMLInputElement | number) {
        const target = typeof input === "number" ? this.getInhabitatArray()[input] : input;
        return this.theoremItems.find((item): item is Extract<TTTheoremItem, { kind: "theorem" }> =>
            item.kind === "theorem" && item.input === target) ?? null;
    }
    private getFolderScopeForFolder(folderId: string | null) {
        if (!folderId) return [] as Extract<TTTheoremItem, { kind: "folder" }>[];
        return this.scanTheoremFolderScope([folderId]).get(folderId) ?? [];
    }
    private getAllTheoremFolders() {
        return this.theoremItems.filter((item): item is Extract<TTTheoremItem, { kind: "folder" }> => item.kind === "folder");
    }
    private getFolderPath(folderId: string) {
        return this.syncTheoremWorkspaceFromDom().folderPath(folderId);
    }
    private getFolderScopeForInput(input: HTMLInputElement | number, selectedFolderId?: string | null) {
        const item = this.getTheoremItemForInput(input);
        if (!item) return [] as Extract<TTTheoremItem, { kind: "folder" }>[];
        const scopes = this.scanTheoremFolderScope([item.id]).get(item.id) ?? [];
        if (selectedFolderId && scopes.some(folder => folder.id === selectedFolderId)) {
            return this.getFolderScopeForFolder(selectedFolderId);
        }
        return scopes;
    }
    private getDefaultTacticScope(input: HTMLInputElement | null) {
        const scopes = input ? this.getFolderScopeForInput(input) : [];
        return scopes.length ? scopes[scopes.length - 1].id : null;
    }
    private getDefinitionFolderId(index: number) {
        const item = this.getTheoremItemForInput(index);
        if (!item) return null;
        const scopes = this.syncTheoremWorkspaceFromDom().folderScopesForItem(item.id);
        return scopes.length ? scopes[scopes.length - 1].id : null;
    }
    private findVisibleDefinitionIndex(name: string, targetIndex: number, selectedFolderId: string | null) {
        for (let index = Math.min(targetIndex - 1, this.userDefinedConsts.length - 1); index >= 0; index--) {
            if (this.userDefinedConsts[index]?.[0] !== name) continue;
            if (this.isDefinitionVisible(index, targetIndex, selectedFolderId)) return index;
        }
        return -1;
    }
    private hasDefinitionNameConflict(name: string, currentIndex: number, selectedFolderId: string | null) {
        const currentItem = this.getTheoremItemForInput(currentIndex);
        const currentFolderId = this.getDefinitionFolderId(currentIndex);
        const currentIsLocal = !!currentItem?.localCheckbox.checked && !!currentFolderId;
        for (let index = currentIndex - 1; index >= 0; index--) {
            if (this.userDefinedConsts[index]?.[0] !== name) continue;
            if (!this.isDefinitionVisible(index, currentIndex, selectedFolderId)) continue;
            const previousFolderId = this.getDefinitionFolderId(index);
            // A nested local scope may shadow an ancestor's local helper. A
            // duplicate in the same folder, or any collision with a global
            // definition, remains an error.
            if (currentIsLocal && previousFolderId && previousFolderId !== currentFolderId) continue;
            return true;
        }
        return false;
    }
    private isDefinitionInScope(index: number, selectedFolderId: string | null) {
        const inputs = this.getInhabitatArray();
        if (this.isTheoremInputDisabled(inputs[index])) return false;
        const definition = this.userDefinedConsts[index];
        if (!definition) return false;
        return this.syncTheoremWorkspaceFromDom().isTheoremInScope(index, selectedFolderId);
    }
    private isDefinitionVisible(index: number, targetIndex: number, selectedFolderId: string | null) {
        return index < targetIndex && this.isDefinitionInScope(index, selectedFolderId);
    }
    private isTacticDefinitionVisible(index: number, selectedFolderId: string | null) {
        const targetIndex = this.getTacticDefinitionEnd();
        return index !== targetIndex && this.isDefinitionInScope(index, selectedFolderId);
    }
    private clearUserDefinitionContext() {
        this.invalidateHottDefCtxt();
        const names = new Set(Object.keys(this.core.state.userDefs));
        for (const definition of this.userDefinedConsts) {
            if (definition) names.add(definition[0]);
        }
        for (const name of names) delete this.core.state.defTypes[name];
        if (typeof this.core.clearUserDefinitions === "function") this.core.clearUserDefinitions();
        else this.core.state.userDefs = {};
    }
    private addUserDefinitionToContext(name: string, definition: definedConst) {
        if (typeof this.core.setUserDefinition === "function") this.core.setUserDefinition(name, definition[1]);
        else this.core.state.userDefs[name] = definition[1];
        if (definition[2]) this.core.restoreDefinitionCache(name, definition[2]);
    }
    private getActiveTacticScopeId() {
        const scopes = this.getTacticScopeOptions();
        if (this.tacticScopeExplicit) {
            if (this.tacticScopeFolderId === null) return null;
            if (scopes.some(folder => folder.id === this.tacticScopeFolderId)) {
                return this.tacticScopeFolderId;
            }
            this.tacticScopeExplicit = false;
            this.tacticScopeFolderId = null;
        }
        if (this.tacticScopeFolderId && scopes.some(folder => folder.id === this.tacticScopeFolderId)) {
            return this.tacticScopeFolderId;
        }
        return this.tacticTargetInput ? this.getDefaultTacticScope(this.tacticTargetInput) : null;
    }
    private getTacticDefinitionEnd() {
        const inputs = this.getInhabitatArray();
        const targetIndex = this.tacticTargetInput ? inputs.indexOf(this.tacticTargetInput) : -1;
        return targetIndex >= 0 ? targetIndex : inputs.length;
    }
    private getTacticScopeOptions() {
        return this.tacticTargetInput
            ? this.getFolderScopeForInput(this.tacticTargetInput)
            : this.getAllTheoremFolders();
    }
    private renderTacticScopeOptions() {
        const select = document.getElementById("tactic-scope") as HTMLSelectElement;
        const label = document.getElementById("tactic-scope-label");
        if (!select || !label) return;
        const previous = this.tacticScopeFolderId;
        select.innerHTML = "";
        const scopes = this.getTacticScopeOptions();
        const global = document.createElement("option");
        global.value = "";
        global.innerText = TR("不使用局部常量");
        select.appendChild(global);
        for (const folder of scopes) {
            const option = document.createElement("option");
            option.value = folder.id;
            option.innerText = this.getFolderPath(folder.id);
            select.appendChild(option);
        }
        const defaultScope = this.getDefaultTacticScope(this.tacticTargetInput);
        if (this.tacticScopeExplicit) {
            if (previous !== null && !scopes.some(folder => folder.id === previous)) {
                this.tacticScopeExplicit = false;
                this.tacticScopeFolderId = defaultScope;
            }
        } else {
            this.tacticScopeFolderId = previous && scopes.some(folder => folder.id === previous)
                ? previous
                : defaultScope;
        }
        select.value = this.tacticScopeFolderId ?? "";
        label.classList.toggle("hide", !(this.mode instanceof Array) || scopes.length === 0);
    }
    private renderTheoremStructure() {
        if (!this.restoringTheoremItems) this.normalizeTheoremFolderLengths();
        const workspace = this.syncTheoremWorkspaceFromDom();
        this.applyTheoremWorkspaceSnapshot(workspace.snapshot());
        this.syncTheoremDomOrder();
        const itemByWrapper = new Map<HTMLElement, TTTheoremItem>(
            this.theoremItems.map(item => [item.wrapper, item] as const)
        );
        applyWorkspaceLayout(
            this.theoremItems.map(item => item.wrapper),
            workspace.layout(),
            (row, state) => {
                const item = itemByWrapper.get(row);
                if (!item) return;
                if (item.kind === "theorem") {
                    item.input.dataset.ttDisabled = String(state.disabled);
                    item.wrapper.classList.toggle("tt-theorem-disabled", state.disabled);
                    item.localCheckbox.disabled = !state.canBeLocal;
                    if (!state.canBeLocal) {
                        item.localCheckbox.checked = false;
                        workspace.updateTheorem(item.id, { local: false });
                    }
                    item.localCheckbox.title = TR(state.canBeLocal
                        ? "局部常量仅在所在文件夹及子文件夹中可见"
                        : "局部常量需放在文件夹中");
                    if (item.localCheckbox.parentElement) {
                        item.localCheckbox.parentElement.title = item.localCheckbox.title;
                    }
                    return;
                }
                item.title.innerText = item.name;
                item.title.classList.toggle("dir-open", item.open);
                item.title.classList.toggle("dir-close", !item.open);
                row.dataset.dragFolderOpen = String(item.open);
                item.checkbox.checked = item.disabled;
            }
        );
    }

    private isTypePanelVisible() {
        return document.getElementById("panel-2")?.classList.contains("show") ?? false;
    }

    private theoremDisplayDiv(input: HTMLInputElement) {
        return input.parentElement?.querySelector(".inhabitat-div") as HTMLDivElement | null;
    }

    private clearTheoremDisplay(item: Extract<TTTheoremItem, { kind: "theorem" }>) {
        const div = this.theoremDisplayDiv(item.input);
        if (!div) return;
        while (div.firstChild) div.removeChild(div.firstChild);
        item.input["ttDisplayDeferred"] = true;
    }

    private renderTheoremDisplay(item: Extract<TTTheoremItem, { kind: "theorem" }>) {
        const input = item.input;
        const div = this.theoremDisplayDiv(input);
        if (!div || !input.value.trim()) return;
        while (div.firstChild) div.removeChild(div.firstChild);
        const currentIdx = this.getInhabitatArray().indexOf(input);
        const parseError = input["ttDisplayParseError"] as string | undefined;
        const error = input["ttDisplayError"] as string | undefined;
        if (parseError) {
            this.addSpan(div, input.value + " - " + parseError);
        } else {
            try {
                const displayAst = restoreSemanticMetaNamesForDisplay(parser.parse(input.value));
                div.appendChild(this.ast2HTML("", displayAst, [], [], currentIdx));
                if (error) this.addSpan(div, " - " + error);
                const validatedType = input["validatedType"] as AST | undefined;
                if (!error && displayAst.type[0] !== ":" && validatedType) {
                    this.addSpan(div, " &nbsp; : &nbsp; ", true);
                    div.appendChild(this.ast2HTML(
                        "",
                        restoreSemanticMetaNamesForDisplay(Core.clone(validatedType, true)),
                        [],
                        [],
                        currentIdx
                    ));
                }
            } catch (renderError) {
                this.addSpan(div, input.value + " - " + String(renderError));
            }
        }
        input["ttDisplayDeferred"] = false;
    }

    /** Release large theorem formula DOM while the map or another layer is visible. */
    setTypePanelVisible(visible: boolean) {
        if (visible) {
            for (const item of this.theoremItems) {
                if (item.kind === "theorem" && item.input["ttDisplayDeferred"]) {
                    this.renderTheoremDisplay(item);
                }
            }
            return;
        }
        for (const item of this.theoremItems) {
            if (item.kind === "theorem") this.clearTheoremDisplay(item);
        }
    }

    private isTheoremInputDisabled(input: HTMLInputElement) {
        return input?.dataset.ttDisabled === "true";
    }
    private invalidateTheoremTypeTags(startIndex = 0) {
        const inputs = this.getInhabitatArray();
        for (let i = Math.max(0, startIndex); i < inputs.length; i++) {
            const input = inputs[i];
            delete input["validatedType"];
            delete input.dataset.validatedTypeKey;
        }
        this.gateQueryCache.clear();
    }
    private setTheoremTypeTag(input: HTMLInputElement, ast: AST) {
        if (!ast?.checked) return;
        const checked = Core.clone(ast.checked, true);
        input["validatedType"] = checked;
        input.dataset.validatedTypeKey = parser.stringify(checked);
        delete input["validationInvalidated"];
        this.gateQueryCache.clear();
    }
    private suspendTheoremTypeTag(input: HTMLInputElement) {
        input["editingValidatedType"] = input["validatedType"];
        input["editingValidatedTypeKey"] = input.dataset.validatedTypeKey;
        delete input["validatedType"];
        delete input.dataset.validatedTypeKey;
        this.gateQueryCache.clear();
    }
    private restoreSuspendedTheoremTypeTag(input: HTMLInputElement) {
        const checked = input["editingValidatedType"] as AST;
        const key = input["editingValidatedTypeKey"] as string;
        if (checked) input["validatedType"] = checked;
        if (key) input.dataset.validatedTypeKey = key;
        delete input["editingValidatedType"];
        delete input["editingValidatedTypeKey"];
        this.gateQueryCache.clear();
    }
    private discardSuspendedTheoremTypeTag(input: HTMLInputElement) {
        delete input["editingValidatedType"];
        delete input["editingValidatedTypeKey"];
    }
    private invalidateTheoremChecks(startIndex = 0, resetWorker = false) {
        const inputs = this.getInhabitatArray();
        // A persistent Worker cannot cancel a synchronous check already
        // running. Restart it before invalidating a suffix so an older chain
        // cannot mutate the session between two rapid revalidations.
        if (resetWorker && this.coreWorker && inputs.some(input => input.parentElement?.classList.contains("checking"))) {
            this.resetCoreWorkerSession();
        }
        for (let i = Math.max(0, startIndex); i < inputs.length; i++) {
            const input = inputs[i];
            input["workerRequestId"] = ++this.workerRequestId;
            input.parentElement?.classList.remove("checking");
        }
        this.invalidateTheoremTypeTags(startIndex);
    }
    private revalidateTheorems(startIndex = 0) {
        const inputs = this.getInhabitatArray();
        const earliestChecking = inputs.findIndex(input => input.parentElement?.classList.contains("checking"));
        const effectiveStart = Math.min(
            Math.max(0, startIndex),
            ...(earliestChecking >= 0 ? [earliestChecking] : [])
        );
        const run = this.theoremValidation.request(effectiveStart);
        this.invalidateTheoremChecks(effectiveStart, true);
        if (!run) return;
        const first = this.getInhabitatArray()[effectiveStart];
        if (first) first.onblur({ updateDefs: true, validationRunId: run.id } as any);
        else this.completeTheoremValidation(run.id);
    }
    private resetCoreWorkerSession() {
        if (!this.coreWorker) return;
        this.coreWorkerStateRevision++;
        this.coreWorker.reset();
        this.coreWorkerGeneration = -1;
        this.coreWorkerConfigKey = "";
        this.coreWorkerConfigurePromise = null;
        this.coreWorkerLoadedThrough = 0;
    }
    private completeTheoremValidation(runId: number) {
        const next = this.theoremValidation.complete(runId);
        if (!next) return;
        this.invalidateTheoremChecks(next.startIndex, true);
        const first = this.getInhabitatArray()[next.startIndex];
        if (first) first.onblur({ updateDefs: true, validationRunId: next.id } as any);
        else this.completeTheoremValidation(next.id);
    }
    private realignUserDefinitions(previousInputs: HTMLInputElement[], previousDefinitions: definedConst[]) {
        const byInput = new Map<HTMLInputElement, definedConst>();
        previousInputs.forEach((input, index) => byInput.set(input, previousDefinitions[index]));
        this.userDefinedConsts = this.getInhabitatArray().map(input => byInput.get(input) ?? null);
        this.refreshUserConstNames();
    }
    private moveTheoremItem(srcId: string, dstId: string) {
        if (!srcId) return;
        const previousInputs = this.getInhabitatArray();
        const previousDefinitions = this.userDefinedConsts.slice();
        const workspace = this.syncTheoremWorkspaceFromDom(true);
        const mutation = workspace.move(srcId, dstId);
        if (!mutation.changed) return;
        this.applyTheoremWorkspaceSnapshot(mutation.snapshot);
        this.syncTheoremDomOrder();
        this.realignUserDefinitions(previousInputs, previousDefinitions);
        this.definitionRevision++;
        this.theoremStructureRevision++;
        this.gatePreviewStructureRevision = -1;
        this.renderTheoremStructure();
        this.reconcileProofSessionBindings(false);
        this.onStateChange();
        if (mutation.revalidateFrom !== null) this.revalidateTheorems(mutation.revalidateFrom);
    }
    addTheoremFolder(name?: string, saved?: Partial<Extract<TTTheoremSaveItem, { kind: "folder" }>>, silent = false) {
        if (name === undefined) name = prompt(TR("文件夹名称："), TR("新文件夹"))?.trim();
        if (!name) return;
        const id = saved?.id || this.createTheoremItemId("folder");
        const wrapper = document.createElement("div");
        wrapper.className = "wrapper tt-folder-row";
        wrapper.dataset.dragFolder = "true";
        this.createTheoremDragHandle(wrapper, id, {
            folder: true,
            folderOpen: saved?.open ?? true
        });

        const addTheorem = document.createElement("button");
        addTheorem.type = "button";
        addTheorem.className = "inhabitat-modify";
        addTheorem.innerText = "+";
        addTheorem.title = TR("在文件夹底部添加定理");
        // Keep the folder action beside the drag handle, matching theorem
        // rows while still inserting the new theorem at the folder's end.
        wrapper.appendChild(addTheorem);

        const title = document.createElement("span");
        title.className = "tt-folder-title";
        wrapper.appendChild(title);
        const label = document.createElement("label");
        label.className = "tt-folder-disable";
        const checkbox = document.createElement("input");
        checkbox.type = "checkbox";
        label.appendChild(checkbox);
        label.appendChild(document.createTextNode(TR("停用子定理")));
        wrapper.appendChild(label);

        const rename = document.createElement("button");
        rename.type = "button";
        rename.className = "inhabitat-modify";
        rename.innerText = "✎";
        rename.title = TR("重命名文件夹");
        wrapper.appendChild(rename);
        const remove = document.createElement("button");
        remove.type = "button";
        remove.className = "inhabitat-modify danger";
        remove.innerText = "×";
        remove.title = TR("删除文件夹");
        wrapper.appendChild(remove);

        const folder: Extract<TTTheoremItem, { kind: "folder" }> = {
            kind: "folder",
            id,
            name,
            length: Number(saved?.length) || 0,
            open: saved?.open ?? true,
            disabled: saved?.disabled ?? false,
            wrapper,
            title,
            checkbox
        };
        title.addEventListener("click", () => {
            const workspace = this.syncTheoremWorkspaceFromDom(true);
            const mutation = workspace.setFolderOpen(folder.id, !folder.open);
            this.applyTheoremWorkspaceSnapshot(mutation.snapshot);
            this.renderTheoremStructure();
            this.onStateChange();
        });
        checkbox.addEventListener("change", () => {
            const workspace = this.syncTheoremWorkspaceFromDom(true);
            const mutation = workspace.setFolderDisabled(folder.id, checkbox.checked);
            this.applyTheoremWorkspaceSnapshot(mutation.snapshot);
            this.definitionRevision++;
            this.theoremStructureRevision++;
            this.gatePreviewStructureRevision = -1;
            this.renderTheoremStructure();
            this.onStateChange();
            if (mutation.revalidateFrom !== null) this.revalidateTheorems(mutation.revalidateFrom);
        });
        addTheorem.addEventListener("click", () => {
            if (!folder.open) {
                const workspace = this.syncTheoremWorkspaceFromDom(true);
                const mutation = workspace.setFolderOpen(folder.id, true);
                this.applyTheoremWorkspaceSnapshot(mutation.snapshot);
            }
            this.renderTheoremStructure();
            this.updateInhabitList(undefined, folder);
        });
        rename.addEventListener("click", () => {
            const nextName = prompt(TR("文件夹名称："), folder.name)?.trim();
            if (!nextName) return;
            const workspace = this.syncTheoremWorkspaceFromDom(true);
            const mutation = workspace.renameFolder(folder.id, nextName);
            this.applyTheoremWorkspaceSnapshot(mutation.snapshot);
            this.renderTheoremStructure();
            this.onStateChange();
        });
        remove.addEventListener("click", () => {
            if (!confirm(TR("删除文件夹后，里面的定理会移动到上一级。确定继续吗？"))) return;
            const workspace = this.syncTheoremWorkspaceFromDom(true);
            const mutation = workspace.removeFolder(folder.id);
            this.applyTheoremWorkspaceSnapshot(mutation.snapshot);
            wrapper.remove();
            this.definitionRevision++;
            this.theoremStructureRevision++;
            this.gatePreviewStructureRevision = -1;
            this.renderTheoremStructure();
            this.onStateChange();
            if (mutation.revalidateFrom !== null) this.revalidateTheorems(mutation.revalidateFrom);
        });

        if (this.restoringTheoremItems) {
            // During save restore descendants have not been appended yet.
            // Keep the saved flat length untouched and hydrate the workspace
            // only after the complete ordered list exists.
            this.appendRestoredTheoremItem(folder);
            return folder;
        }
        const workspace = this.syncTheoremWorkspaceFromDom(true);
        const mutation = workspace.insertFolder({
            kind: "folder",
            id: folder.id,
            name: folder.name,
            length: folder.length,
            open: folder.open,
            disabled: folder.disabled
        }, workspace.itemCount, null);
        this.applyTheoremWorkspaceSnapshot(mutation.snapshot, [folder]);
        this.renderTheoremStructure();
        if (!silent) this.onStateChange();
        return folder;
    }
    serializeTheoremItems(): TTTheoremSaveItem[] {
        return this.syncTheoremWorkspaceFromDom(true).serialize();
    }
    serializeProofSessions(): SerializedTTProofSessions {
        this.captureActiveTacticSession();
        this.reconcileProofSessionBindings(false);
        return this.proofSessions.serialize();
    }
    resetProofAssistantForSaveLoad() {
        this.pendingProofSessions = null;
        this.proofSessions = new TTProofSessionStore();
        this.tacticSessionReplayId = null;
        this.tacticCaptureBlockedSessionId = null;
        this.clearTacticRuntime();
        this.renderTacticSessionTabs();
    }
    queueProofSessionsRestore(serialized?: Partial<SerializedTTProofSessions> | null) {
        this.pendingProofSessions = serialized && Array.isArray(serialized.sessions)
            ? { sessions: serialized.sessions as TTProofSession[], activeId: serialized.activeId ?? null }
            : { sessions: [], activeId: null };
        if (!this.skipRendering) void this.restorePendingProofSessionsWhenReady();
    }
    private async restorePendingProofSessionsWhenReady() {
        const serialized = this.pendingProofSessions;
        if (!serialized || this.skipRendering) return;
        await this.theoremValidation.waitForIdle();
        if (this.pendingProofSessions !== serialized) return;
        this.pendingProofSessions = null;
        this.proofSessions = TTProofSessionStore.deserialize(serialized);
        this.reconcileProofSessionBindings(true);
        this.renderTacticSessionTabs();
        const activeId = this.proofSessions.activeId;
        if (activeId) await this.activateTacticSession(activeId, false);
    }
    restoreTheoremItems(items: TTTheoremSaveItem[]) {
        this.invalidateHottDefCtxt();
        this.definitionRevision++;
        this.theoremStructureRevision++;
        this.gatePreviewStructureRevision = -1;
        // Drop caches belonging to the previous theorem list before replacing
        // it. They are keyed by name and otherwise survive a save restore.
        for (const definition of this.userDefinedConsts) {
            if (definition) delete this.core.state.defTypes[definition[0]];
        }
        for (const item of this.theoremItems) item.wrapper.remove();
        this.theoremItems = [];
        this.getTheoremWorkspace().replace([]);
        // Keep the empty workspace authoritative while rows are appended. A
        // partial DOM hydration would normalize saved folder lengths against
        // the incomplete suffix and lose nested scopes.
        this.theoremWorkspaceHydrated = true;
        this.userDefinedConsts = [];
        this.refreshUserConstNames();
        this.gateQueryCache.clear();
        this.restoringTheoremItems = true;
        try {
            for (const item of items) {
                if (item.kind === "folder") {
                    this.addTheoremFolder(item.name, item, true);
                } else {
                    this.updateInhabitList();
                    const theorem = this.theoremItems[this.theoremItems.length - 1];
                    if (theorem?.kind === "theorem") {
                        theorem.input.value = String(item.value ?? "");
                        theorem.localCheckbox.checked = !!item.local;
                    }
                }
            }
        } finally {
            this.restoringTheoremItems = false;
        }
        const workspace = this.syncTheoremWorkspaceFromDom(true);
        this.applyTheoremWorkspaceSnapshot(workspace.snapshot());
        this.renderTheoremStructure();
        if (!this.skipRendering) this.revalidateTheorems();
    }
    getHottDefCtxt(input: HTMLInputElement | number, selectedFolderId: string | null = null) {
        const inputs = this.getInhabitatArray();
        const currentIdx = typeof input === "number" ? input : inputs.indexOf(input);
        const end = typeof input === "number" ? Math.min(inputs.length - 1, input) : currentIdx - 1;
        const scopeId = selectedFolderId ?? (typeof input === "number"
            ? this.getActiveTacticScopeId()
            : this.getDefaultTacticScope(input));
        const configKey = JSON.stringify({
            scopeId,
            disableSimpleFn: this.disableSimpleFn,
            disableSimpleEq: this.disableSimpleEq,
            inferDisplayMode: this.inferDisplayMode,
            semanticResourceScale: this.semanticResourceScale,
            language: langMgr.lang,
            unlockedTypes: Array.from(this.unlockedTypes ?? []).sort()
        });
        const key = JSON.stringify({
            definitionRevision: this.definitionRevision,
            theoremStructureRevision: this.theoremStructureRevision,
            currentIdx,
            end,
            configKey
        });
        const targetIndex = currentIdx + (typeof input === "number" ? 0 : 1);
        const desiredEntries: { index: number, slot: definedConst }[] = [];
        for (let i = 0; i <= end; i++) {
            const def = this.userDefinedConsts[i];
            if (!def || !this.isDefinitionVisible(i, targetIndex, scopeId)) continue;
            desiredEntries.push({ index: i, slot: def });
        }
        const materialized = this.hottDefCtxtMaterialized;
        const sameEntry = (
            left: { index: number, slot: definedConst },
            right: { index: number, slot: definedConst }
        ) => left.index === right.index
            && left.slot === right.slot
            && left.slot?.[1] === right.slot?.[1]
            && left.slot?.[2] === right.slot?.[2];
        const exactMaterialized = this.hottDefCtxtCore === this.core
            && materialized
            && materialized.scopeId === scopeId
            && materialized.configKey === configKey
            && materialized.entries.length === desiredEntries.length
            && materialized.entries.every((entry, index) => sameEntry(entry, desiredEntries[index]));
        if (exactMaterialized && this.hottDefCtxtKey === key && this.hottDefCtxtMacroNames) {
            this.core.state.disableSimpleFn = this.disableSimpleFn;
            this.core.state.disableSimpleEq = this.disableSimpleEq;
            macro.clear();
            for (const name of this.hottDefCtxtMacroNames) macro.add(name);
            return currentIdx;
        }

        const canExtendMaterialized = this.hottDefCtxtCore === this.core
            && materialized
            && materialized.scopeId === scopeId
            && materialized.configKey === configKey
            && desiredEntries.length >= materialized.entries.length
            && materialized.entries.every((entry, index) => sameEntry(entry, desiredEntries[index]));
        if (canExtendMaterialized) {
            const macroNames = new Set<string>(sysmacro);
            for (const entry of materialized.entries) macroNames.add(entry.slot[0]);
            for (const entry of desiredEntries.slice(materialized.entries.length)) {
                macroNames.add(entry.slot[0]);
                this.addUserDefinitionToContext(entry.slot[0], entry.slot);
            }
            macro.clear();
            for (const name of macroNames) macro.add(name);
            this.hottDefCtxtMaterialized = {
                scopeId,
                configKey,
                entries: desiredEntries
            };
            this.hottDefCtxtKey = key;
            this.hottDefCtxtMacroNames = macroNames;
            this.hottDefCtxtCore = this.core;
            return currentIdx;
        }

        macro.clear();
        for (const s of sysmacro) macro.add(s);
        this.clearUserDefinitionContext();
        const materializedMacroNames = new Set<string>(sysmacro);
        for (const entry of desiredEntries) {
            macro.add(entry.slot[0]);
            materializedMacroNames.add(entry.slot[0]);
            this.addUserDefinitionToContext(entry.slot[0], entry.slot);
        }
        this.hottDefCtxtMaterialized = {
            scopeId,
            configKey,
            entries: desiredEntries
        };
        this.hottDefCtxtKey = key;
        this.hottDefCtxtMacroNames = materializedMacroNames;
        this.hottDefCtxtCore = this.core;
        return currentIdx;
    }
    private getHottTacticDefCtxt(selectedFolderId: string | null) {
        this.invalidateHottDefCtxt();
        macro.clear();
        for (const s of sysmacro) macro.add(s);
        this.clearUserDefinitionContext();
        for (let i = 0; i < this.getInhabitatArray().length; i++) {
            const definition = this.userDefinedConsts[i];
            if (!definition || !this.isTacticDefinitionVisible(i, selectedFolderId)) continue;
            macro.add(definition[0]);
            this.addUserDefinitionToContext(definition[0], definition);
        }
    }
    private getWorkerSystemConfig(): TTCoreConfig {
        return {
            unlockedTypes: Array.from(this.unlockedTypes),
            disableSimpleFn: this.disableSimpleFn,
            disableSimpleEq: this.disableSimpleEq,
            inferDisplayMode: this.inferDisplayMode,
            timeout: Core.timeout,
            semanticResourceScale: this.semanticResourceScale,
            language: langMgr.lang,
            trustedAxioms: (this.sandboxAxioms ?? []).map(([name, type]) => [name, Core.clone(type)]),
            trustedInductives: (this.sandboxInductives ?? []).map(bundle => cloneInductiveBundle(bundle)),
            trustedDefinitions: (this.sandboxDefinitions ?? []).map(([name, definition]) => [
                name,
                Core.clone(definition)
            ]),
            trustedDeclarationOrder: this.sandboxDeclarationOrder?.map(entry => ({ ...entry })),
        };
    }
    private getWorkerDefinitionSlots(definitionEnd: number, scopeFolderId: string | null = null): TTDefinitionSlot[] {
        const definitions: TTDefinitionSlot[] = [];
        const inputs = this.getInhabitatArray();
        for (let i = 0; i < definitionEnd; i++) {
            if (!this.isDefinitionVisible(i, definitionEnd, scopeFolderId)) {
                definitions.push(null);
                continue;
            }
            const definition = this.userDefinedConsts[i];
            if (!definition) {
                definitions.push(null);
                continue;
            }
            definitions.push([definition[0], Core.clone(definition[1]), definition[2]]);
        }
        return definitions;
    }
    private getTacticWorkerDefinitionSlots(scopeFolderId: string | null = null): TTDefinitionSlot[] {
        const definitions: TTDefinitionSlot[] = [];
        const inputs = this.getInhabitatArray();
        for (let i = 0; i < inputs.length; i++) {
            if (!this.isTacticDefinitionVisible(i, scopeFolderId)) {
                definitions.push(null);
                continue;
            }
            const definition = this.userDefinedConsts[i];
            if (!definition) {
                definitions.push(null);
                continue;
            }
            definitions.push([definition[0], Core.clone(definition[1]), definition[2]]);
        }
        return definitions;
    }
    private getWorkerConfig(definitionEnd: number, scopeFolderId: string | null = null): TTCoreConfig {
        const definitions = this.getWorkerDefinitionSlots(definitionEnd, scopeFolderId);
        return {
            ...this.getWorkerSystemConfig(),
            userDefinitions: definitions.filter(Boolean).map(definition => [definition[0], definition[1]]),
            userDefinitionCaches: definitions.filter(definition => definition?.[2]).map(definition => [definition[0], definition[2]])
        };
    }
    private getTacticWorkerConfig(scopeFolderId: string | null = null): TTCoreConfig {
        const definitions = this.getTacticWorkerDefinitionSlots(scopeFolderId);
        return {
            ...this.getWorkerSystemConfig(),
            userDefinitions: definitions.filter(Boolean).map(definition => [definition[0], definition[1]]),
            userDefinitionCaches: definitions.filter(definition => definition?.[2]).map(definition => [definition[0], definition[2]])
        };
    }
    private prepareCoreWorker(definitionEnd: number, scopeFolderId: string | null = null) {
        if (!this.coreWorker) return Promise.reject(new Error("Type-theory worker unavailable"));
        const config = this.getWorkerSystemConfig();
        // The ordered definition prefix is persistent Worker state, not part
        // of the engine configuration. Sequential validation appends one slot
        // at a time; only a system-option or lexical-scope transition rebuilds
        // the already validated prefix.
        const configKey = JSON.stringify({ config, scopeFolderId });
        const generation = this.coreWorker.generation;
        if (this.coreWorkerGeneration === generation && this.coreWorkerConfigKey === configKey) {
            return this.coreWorkerMutations.wait();
        }
        const revision = ++this.coreWorkerStateRevision;
        this.coreWorkerGeneration = generation;
        this.coreWorkerConfigKey = configKey;
        const definitions = this.getWorkerDefinitionSlots(definitionEnd, scopeFolderId);
        this.coreWorkerLoadedThrough = definitions.length;
        const promise = this.coreWorkerMutations.enqueue(() => this.coreWorker.configure(config, definitions));
        this.coreWorkerConfigurePromise = promise.catch(error => {
            if (this.coreWorkerGeneration === generation
                && this.coreWorkerConfigKey === configKey
                && this.coreWorkerStateRevision === revision) {
                this.coreWorkerGeneration = -1;
                this.coreWorkerConfigKey = "";
                this.coreWorkerConfigurePromise = null;
                this.coreWorkerLoadedThrough = 0;
            }
            throw error;
        });
        return this.coreWorkerConfigurePromise;
    }
    private prepareAssistWorker(
        definitionEnd: number,
        config = this.getWorkerSystemConfig(),
        definitions?: TTDefinitionSlot[],
        scopeFolderId: string | null = null,
        definitionMode: "ordered" | "tactic" = "ordered"
    ) {
        if (!this.assistWorker) return Promise.reject(new Error("Proof-assistant worker unavailable"));
        const configKey = JSON.stringify({ config, definitionEnd, scopeFolderId, definitionMode });
        const generation = this.assistWorker.generation;
        if (this.assistWorkerGeneration === generation && this.assistWorkerConfigKey === configKey) {
            return this.assistWorkerMutations.wait();
        }
        this.assistWorkerGeneration = generation;
        this.assistWorkerConfigKey = configKey;
        this.assistWorkerSessionReady = false;
        const configuredDefinitions = definitions ?? this.getWorkerDefinitionSlots(definitionEnd, scopeFolderId);
        const promise = this.assistWorkerMutations.enqueue(() => this.assistWorker.configure(
            config,
            configuredDefinitions
        ));
        this.assistWorkerConfigurePromise = promise.catch(error => {
            if (this.assistWorkerGeneration === generation && this.assistWorkerConfigKey === configKey) {
                this.assistWorkerGeneration = -1;
                this.assistWorkerConfigKey = "";
                this.assistWorkerConfigurePromise = null;
            }
            throw error;
        });
        return this.assistWorkerConfigurePromise;
    }
    private invalidateWorkerDefinitions(startIndex: number) {
        this.invalidateHottDefCtxt(false);
        this.definitionRevision++;
        const start = Math.max(0, Math.floor(startIndex));
        if (this.coreWorker
            && this.coreWorkerGeneration === this.coreWorker.generation
            && this.coreWorkerConfigKey
            && start < this.coreWorkerLoadedThrough) {
            const generation = this.coreWorker.generation;
            const configKey = this.coreWorkerConfigKey;
            const revision = ++this.coreWorkerStateRevision;
            this.coreWorkerLoadedThrough = start;
            this.coreWorkerMutations.enqueue(() => this.coreWorker.truncate(start)).catch(() => {
                if (this.coreWorker.generation !== generation
                    || this.coreWorkerConfigKey !== configKey
                    || this.coreWorkerStateRevision !== revision) return;
                this.coreWorkerGeneration = -1;
                this.coreWorkerConfigKey = "";
                this.coreWorkerConfigurePromise = null;
                this.coreWorkerLoadedThrough = 0;
            });
        }
        if (this.assistWorker && this.assistWorkerGeneration === this.assistWorker.generation && this.assistWorkerConfigKey) {
            // The proof assistant is cold during theorem-list loading. Once it
            // has been used, a definition change merely marks that snapshot
            // stale; the next proof command rebuilds its position-independent
            // folder scope from the final validated UI caches.
            this.assistWorkerSessionReady = false;
            this.assistWorkerGeneration = -1;
            this.assistWorkerConfigKey = "";
            this.assistWorkerConfigurePromise = null;
        }
    }
    private syncCoreWorkerDefinition(index: number, definition: TTDefinitionSlot) {
        if (!this.coreWorker || this.coreWorkerGeneration !== this.coreWorker.generation || !this.coreWorkerConfigKey) return;
        const generation = this.coreWorker.generation;
        const configKey = this.coreWorkerConfigKey;
        const revision = this.coreWorkerStateRevision;
        this.coreWorkerMutations.enqueue(() => this.coreWorker.setDefinition(index, definition)).then(() => {
            if (this.coreWorker.generation === generation
                && this.coreWorkerConfigKey === configKey
                && this.coreWorkerStateRevision === revision) {
                this.coreWorkerLoadedThrough = index + 1;
            }
        }).catch(() => {
            if (this.coreWorker.generation !== generation
                || this.coreWorkerConfigKey !== configKey
                || this.coreWorkerStateRevision !== revision) return;
            this.coreWorkerGeneration = -1;
            this.coreWorkerConfigKey = "";
            this.coreWorkerConfigurePromise = null;
            this.coreWorkerLoadedThrough = 0;
        });
    }
    private validateCoreWorker(index: number, ast: AST, context: Context = [], timeout?: number) {
        if (!this.coreWorker) return Promise.reject(new Error("Type-theory worker unavailable"));
        const generation = this.coreWorker.generation;
        const configKey = this.coreWorkerConfigKey;
        const revision = this.coreWorkerStateRevision;
        return this.coreWorker.validate(index, ast, context, timeout).then(result => {
            if (this.coreWorker.generation === generation
                && this.coreWorkerConfigKey === configKey
                && this.coreWorkerStateRevision === revision) {
                this.coreWorkerLoadedThrough = index + 1;
            }
            return result;
        });
    }
    updateInhabitList(
        insertPos?: HTMLDivElement,
        destinationFolder?: Extract<TTTheoremItem, { kind: "folder" }>
    ) {
        // Inserting a row shifts every later theorem index.  Cancel any
        // in-flight checks in that suffix before changing the arrays; otherwise
        // an old Worker response can write its result into the new row's slot.
        let insertionItemIndex = this.theoremItems.length;
        if (destinationFolder) {
            insertionItemIndex = this.getFolderAppendIndex(destinationFolder);
        } else if (insertPos) {
            const afterIndex = this.theoremItems.findIndex(item => item.wrapper === insertPos);
            if (afterIndex >= 0) insertionItemIndex = afterIndex + 1;
        }
        if (insertionItemIndex < 0) insertionItemIndex = this.theoremItems.length;
        const previousInputs = this.restoringTheoremItems ? [] : this.getInhabitatArray();
        const workspace = this.syncTheoremWorkspaceFromDom(!this.restoringTheoremItems);
        const insertionInputIndex = this.restoringTheoremItems
            ? 0
            : workspace.theoremIndexBeforeItem(insertionItemIndex);
        if (!this.restoringTheoremItems) {
            const hasShiftedSuffix = insertionInputIndex < previousInputs.length;
            if (hasShiftedSuffix) this.invalidateTheoremChecks(insertionInputIndex, true);
            this.definitionRevision++;
            this.theoremStructureRevision++;
            this.gatePreviewStructureRevision = -1;
        }
        // A generated proof can be thousands of characters long.  Keep the
        // editor single-line in interaction semantics, but use a textarea so
        // the value can wrap and grow instead of creating horizontal scroll.
        const input = document.createElement("textarea") as unknown as HTMLInputElement;
        (input as unknown as HTMLTextAreaElement).rows = 1;
        input.classList.add("tt-theorem-input");

        const div = document.createElement("div");
        const button = document.createElement("button");
        div.classList.add("inhabitat-div");
        div.classList.add("hide");
        const localLabel = document.createElement("label");
        localLabel.className = "tt-local-const";
        const localCheckbox = document.createElement("input");
        localCheckbox.type = "checkbox";
        localCheckbox.setAttribute("aria-label", TR("局部常量"));
        localLabel.title = TR("局部常量仅在所在文件夹及子文件夹中可见");
        localLabel.appendChild(localCheckbox);
        let composing = false;
        const resizeTheoremInput = () => {
            const textarea = input as unknown as HTMLTextAreaElement;
            textarea.style.height = "auto";
            // Adding height can make the surrounding list gain a scrollbar,
            // narrowing the textarea and creating additional wrapped lines.
            // Re-measure until the layout settles so the final lines are not
            // clipped by `overflow: hidden`.
            for (let pass = 0; pass < 3; pass++) {
                const nextHeight = Math.max(textarea.scrollHeight, 21);
                const borderHeight = Math.max(0, textarea.offsetHeight - textarea.clientHeight);
                if (textarea.clientHeight >= nextHeight) break;
                textarea.style.height = `${nextHeight + borderHeight}px`;
            }
        };
        input.addEventListener("compositionstart", () => composing = true);
        input.addEventListener("compositionend", () => composing = false);
        input.addEventListener("keydown", ev => {
            if (composing || ev.isComposing || ev.keyCode === 229) return;
            if (ev.key === "Enter" || ev.key === "Escape") {
                ev.preventDefault();
                input.blur();
            }
        });
        input.addEventListener("focus", () => {
            input["editing"] = true;
            input["editingOriginalValue"] = input.value;
            resizeTheoremInput();
        });
        input.addEventListener("input", () => {
            resizeTheoremInput();
            const theoremItem = this.getTheoremItemForInput(input);
            if (theoremItem) {
                this.getTheoremWorkspace().updateTheorem(theoremItem.id, { value: input.value });
                const currentIdx = this.getInhabitatArray().indexOf(input);
                this.proofSessions.markTheoremTargetChanged(theoremItem.id, input.value, currentIdx);
                if (this.proofSessions.active?.theoremItemId === theoremItem.id
                    && this.mode instanceof Array) {
                    this.mode[0] = input.value;
                    this.assistSnapshot = null;
                    this.tacticDefinitionsRevision = -1;
                }
                this.renderTacticSessionTabs();
            }
            if (!input["validationInvalidated"]) {
                const currentIdx = this.getInhabitatArray().indexOf(input);
                if (currentIdx >= 0) this.invalidateTheoremChecks(currentIdx);
                input["validationInvalidated"] = true;
            }
            const originalValue = input["editingOriginalValue"] as string;
            if (originalValue?.includes(":=") || input.value.includes(":=")) input["needUpdate"] = true;
            input["editingCanReuseRenderedResult"] = false;
            this.onStateChange();
        });
        // updateDefs: true means update all inputs after it,
        // otherwise, update all inputs iff ast is xx := xxxx

        // todo: when remove a ":=", must be updated, so input must record value before edited
        // todo: left btn is to drag order(click: add new line after it), if trim ast str is empty, then remove it aotomatically
        input.onblur = ev => {
            const programmatic = !(ev instanceof FocusEvent);
            let validationRunId = typeof ev["validationRunId"] === "number" ? ev["validationRunId"] : null;
            if (programmatic && validationRunId !== null && !this.theoremValidation.isCurrent(validationRunId)) {
                this.completeTheoremValidation(validationRunId);
                return;
            }
            if (programmatic && input["editing"]) {
                input["pendingRevalidation"] = true;
                if (validationRunId !== null) this.completeTheoremValidation(validationRunId);
                return;
            }
            if (!programmatic) input["editing"] = false;
            if (!programmatic && input["pendingRevalidation"]) {
                ev["updateDefs"] = true;
                delete input["pendingRevalidation"];
            }
            if (!programmatic && validationRunId === null && input["validationInvalidated"] && this.theoremValidation.hasActiveRun) {
                const currentIdx = this.getInhabitatArray().indexOf(input);
                const queuedRun = this.theoremValidation.request(currentIdx);
                if (!queuedRun) {
                    input["pendingRevalidation"] = true;
                    return;
                }
                validationRunId = queuedRun.id;
                ev["validationRunId"] = validationRunId;
            }
            if (canReuseTheoremResultOnBlur({
                programmatic,
                canReuseRenderedResult: !!input["editingCanReuseRenderedResult"],
                originalValue: input["editingOriginalValue"],
                currentValue: input.value,
                validationInvalidated: !!input["validationInvalidated"],
                updateDefinitions: !!ev["updateDefs"] || !!input["needUpdate"]
            })) {
                delete input["editingOriginalValue"];
                delete input["editingCanReuseRenderedResult"];
                delete input["needUpdate"];
                this.restoreSuspendedTheoremTypeTag(input);
                input.classList.add("hide");
                div.classList.remove("hide");
                return;
            }
            delete input["editingOriginalValue"];
            delete input["editingCanReuseRenderedResult"];
            this.discardSuspendedTheoremTypeTag(input);
            if (Core.timeoutOccured) {
                document.getElementById("timeout").classList.remove("hide");
            }
            if (!ev["updateDefs"]) ev["updateDefs"] = input["needUpdate"];
            delete input["needUpdate"];
            this.onStateChange();
            // Worker validation does not need a main-thread definition
            // context. Materialize it only for synchronous checking, legacy
            // inference, or definition/cache commit; this keeps map movement
            // responsive while the isolated process validates the suffix.
            const currentIdx = this.getInhabitatArray().indexOf(input);
            const ensureMainContext = () => this.getHottDefCtxt(input);
            const validationItemId = this.getTheoremItemForInput(input)?.id ?? null;
            const rowPositionMatches = () => theoremValidationPositionMatches(
                this.getInhabitatArray(),
                input,
                currentIdx,
                validationItemId,
                currentInput => this.getTheoremItemForInput(currentInput)?.id ?? null
            );
            if (ev["updateDefs"]) this.invalidateWorkerDefinitions(currentIdx);
            this.invalidateTheoremTypeTags(currentIdx);
            input["validationInvalidated"] = true;
            const inputsarr = this.getInhabitatArray();
            const nextInput = inputsarr[currentIdx + 1];
            const continueValidation = (shouldContinue: boolean) => {
                if (validationRunId !== null && !this.theoremValidation.isCurrent(validationRunId)) {
                    this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (shouldContinue && nextInput?.isConnected) {
                    const nextEvent: any = { updateDefs: true };
                    if (validationRunId !== null) nextEvent.validationRunId = validationRunId;
                    nextInput.onblur(nextEvent);
                } else if (validationRunId !== null) {
                    this.completeTheoremValidation(validationRunId);
                }
            };
            const requestId = ++this.workerRequestId;
            input["workerRequestId"] = requestId;
            this.core.state.disableSimpleFn = this.disableSimpleFn;
            this.core.state.disableSimpleEq = this.disableSimpleEq;
            wrapper.classList.remove("error");
            wrapper.classList.remove("infering");
            if (!input.value.trim()) {
                const current = this.getInhabitatArray().indexOf(input);
                if (current < 0) {
                    if (validationRunId !== null) this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (current >= 0) this.invalidateTheoremChecks(current, true);
                this.definitionRevision++;
                this.theoremStructureRevision++;
                this.gatePreviewStructureRevision = -1;
                const [removed] = this.userDefinedConsts.splice(current, 1);
                const theoremItem = this.getTheoremItemForInput(input);
                if (theoremItem) this.proofSessions.detachTheorem(theoremItem.id);
                const workspace = this.syncTheoremWorkspaceFromDom(true);
                const mutation = theoremItem
                    ? workspace.removeTheorem(theoremItem.id)
                    : null;
                if (mutation?.changed) this.applyTheoremWorkspaceSnapshot(mutation.snapshot);
                this.reconcileProofSessionBindings(false);
                this.refreshUserConstNames();
                try { wrapper.remove(); } catch (e) { }
                if (removed) {
                    macro.delete(removed[0]);
                    this.invalidateHottDefCtxt(false);
                }
                this.renderTheoremStructure();
                continueValidation(!!nextInput && (!!removed || ev["updateDefs"]));
                return;
            }
            if (this.isTheoremInputDisabled(input)) {
                // Keep the last verified definition/cache while the row is
                // disabled. Visibility checks and Worker slots already omit
                // disabled rows, so retaining it cannot make the theorem
                // usable; it only lets re-enabling validate transactionally
                // instead of losing the known name during an interrupted run.
                this.refreshUserConstNames();
                wrapper.classList.remove("error", "infering", "checking");
                continueValidation(!!nextInput && !!ev["updateDefs"]);
                return;
            }
            this.userDefinedConsts[currentIdx] = null;
            this.refreshUserConstNames();
            let ast: AST;
            let parseError = "";
            let error = "";
            try {
                ast = parser.parse(input.value);
            } catch (e) {
                parseError = e;
                wrapper.classList.add("error");
            }
            if (!ast && !parseError) {
                continueValidation(!!nextInput && !!ev["updateDefs"]);
                return false;
            }
            div.classList.remove("hide");
            input.classList.add("hide");
            while (div.firstChild) {
                div.removeChild(div.firstChild);
            }
            const checkInfer = (ast: AST, trustValidatedHoles = false) => {
                const _checkInfer = (ast: AST, context: Context, expandConsts: Set<string>, checkType: boolean) => {
                    // if (checkType && ast.checked && !_checkInfer(ast.checked, context, expandConsts, false)) return false;
                    if (ast.type === "var") {
                        if (ast.name[0] === "?" || ast.name === "_") {
                            if (trustValidatedHoles) return true;
                            if (!ast.checked) return false;
                            // ast.checked can be ttt or xxx : ttt
                            const t = ast.checked.type === ":" ? ast.checked.nodes[1] : ast.checked;
                            if (t.name === "U@") return true;
                            if (t.type === "apply" && t.nodes[0].name === "U") return true;
                            // if ttt is not Universe or level number, we check xxx recursively
                            return ast.checked.type === ":" ? _checkInfer(ast.checked.nodes[0], context, expandConsts, checkType) : false;
                        }
                        if (!context.find(e => e[0] === ast.name)) {
                            // if this is a constant, check its value recursively
                            const pos = this.findVisibleDefinitionIndex(
                                ast.name,
                                currentIdx,
                                this.getDefaultTacticScope(input)
                            );
                            if (pos >= 0 && inputsarr[pos]?.parentElement?.classList.contains("infering")) {
                                expandConsts.add(ast.name);
                            }
                        }
                    }
                    if (ast.nodes) {
                        if (ast.type === "apply" && ast.nodes[0].name === "U" && ast.nodes[0].type === "var") return true;
                        if (!_checkInfer(ast.nodes[0], context, expandConsts, checkType)) return false;
                        if (ast.type === "P" || ast.type === "L" || ast.type === "W" || ast.type === "S") {
                            context = assignContext([ast.name, ast.nodes[0], 0], context);
                        }
                        if (ast.nodes[1] && !_checkInfer(ast.nodes[1], context, expandConsts, checkType)) return false;
                    }
                    return true;
                }

                let nast = ast;
                let expandConsts = new Set<string>;
                while (true) {
                    if (!_checkInfer(nast, [], expandConsts, true)) { wrapper.classList.add("infering"); return; }
                    if (!expandConsts.size) return;
                    if (nast === ast) { nast = Core.clone(ast); }
                    this.core.expandDef(nast, [], expandConsts);
                    this.core.checkType(nast, [], false);
                    expandConsts = new Set<string>;
                }
            }
            const clearBondId = (value: AST) => {
                value.bondVarId = null;
                if (value.nodes) for (const node of value.nodes) clearBondId(node);
                if (value.checked) clearBondId(value.checked);
                return value;
            };
            const finish = (
                checkedAst: AST,
                validationError = "",
                filledDefinition?: AST,
                definitionCache?: DefinitionTypeCacheSnapshot,
                workerCommitted = false,
                continueAfter = true,
                inferenceComplete?: boolean
            ) => {
                if (validationRunId !== null && !this.theoremValidation.isCurrent(validationRunId)) {
                    this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (input["workerRequestId"] !== requestId || !input.isConnected) {
                    if (validationRunId !== null) this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (!rowPositionMatches()) {
                    // The row moved while the Worker was checking it.  Its
                    // old index is no longer safe for definition/cache writes;
                    // the structural mutation will schedule a fresh suffix
                    // validation using the new position.
                    if (validationRunId !== null) this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (checkedAst) ast = checkedAst;
                error = validationError;
                wrapper.classList.remove("checking");
                if (Core.timeoutOccured) document.getElementById("timeout").classList.remove("hide");
                if (ast && !error) {
                    try {
                        const inferenceStatus = theoremInferenceStatus(inferenceComplete);
                        if (!workerCommitted || inferenceStatus === "legacy") {
                            ensureMainContext();
                        }
                        if (ast.type === ":=") {
                            const defname = ast.nodes[0].name;
                            const defContent = ast.nodes[1];
                            if (!filledDefinition) throw TR("类型检查未返回定义结果");
                            const filledAst = clearBondId(Core.clone(filledDefinition));
                            let storedDefinition: AST;
                            if (defContent.type === ":") {
                                storedDefinition = this.core.desugar(Core.clone(filledAst.nodes[0]), true);
                            } else {
                                storedDefinition = this.core.desugar(Core.clone(filledAst), true);
                            }
                            let storedCache = definitionCache;
                            if (!storedCache) {
                                ensureMainContext();
                                storedCache = this.core.serializeDefinitionCache(defname);
                            }
                            if (!storedCache) {
                                // Compatibility with an older/stale Worker
                                // response that validated the definition but
                                // omitted its transferable type cache. Without
                                // this repair the name remains visible while
                                // every semantic use reports unknown-constant.
                                ensureMainContext();
                                try {
                                    const recovered = this.core.checkDefinition(Core.clone(ast, true), []);
                                    storedCache = recovered.definitionCache;
                                    this.core.restoreDefinitionCache(defname, storedCache);
                                } catch { }
                            }
                            const storedSlot: Exclude<TTDefinitionSlot, null> = [
                                defname,
                                storedDefinition,
                                storedCache
                            ];
                            this.userDefinedConsts[currentIdx] = storedSlot;
                            this.invalidateHottDefCtxt(false);
                            // A previously rendered #t copy preview may have
                            // classified this name as a free variable.  Force
                            // its cached presentation to be rebuilt after the
                            // definition becomes valid.
                            this.gatePreviewRevision = -1;
                            this.refreshUserConstNames();
                            if (this.puzzleDefs.has(defname) && !this.queryDefPuzzle(defname)) {
                                delete this.userDefinedConsts[currentIdx];
                                this.refreshUserConstNames();
                                delete this.core.state.defTypes[defname];
                                this.invalidateWorkerDefinitions(currentIdx);
                                throw TR("该名称的常量需满足游戏中某个题目的要求");
                            }
                            if (workerCommitted) this.coreWorker?.rememberDefinition(currentIdx, storedSlot);
                            else this.syncCoreWorkerDefinition(currentIdx, storedSlot);
                            macro.add(defname);
                            this.invalidateHottDefCtxt(false);
                        }
                        // The Worker returns a fully elaborated definition while
                        // `ast` deliberately preserves the user's `_` spelling
                        // for display.  Re-running the legacy inference probe on
                        // that surface AST both marks solved holes as pending and
                        // can throw after expanding an earlier such definition.
                        const inferenceTarget = theoremInferenceTarget(ast, filledDefinition);
                        if (inferenceStatus === "incomplete") {
                            wrapper.classList.add("infering");
                        } else if (inferenceStatus === "legacy") {
                            // New Workers already checked the complete
                            // inference tree. Rewalking a large elaborated
                            // theorem on the UI thread only blocks the map.
                            checkInfer(inferenceTarget, false);
                            if (inferenceTarget.type === ":") {
                                checkInfer(inferenceTarget.nodes[1], false);
                            }
                        }
                    } catch (e) {
                        error += e;
                        wrapper.classList.add("error");
                    }
                }
                wrapper.classList.toggle("error", !!error || !!parseError);
                if (ast && !error && !parseError && !wrapper.classList.contains("infering")) {
                    this.setTheoremTypeTag(input, ast);
                }
                // This AST is the transient validation result owned by the
                // theorem row. Definition values and inference caches were
                // stored above in separate objects, so presentation renaming
                // can happen in place without deep-cloning a potentially huge
                // checked tree for every restored theorem.
                input["ttDisplayParseError"] = parseError;
                input["ttDisplayError"] = error;
                if (this.isTypePanelVisible()) {
                    const displayAst = ast
                        ? restoreSemanticMetaNamesForDisplay(ast)
                        : ast;
                    const newDom = parseError
                        ? this.addSpan(div, input.value + " - " + parseError)
                        : this.ast2HTML("", displayAst, [], [], currentIdx);
                    div.appendChild(newDom);
                    if (ast && error) this.addSpan(div, " - " + error);
                    if (ast && !error && ast.type[0] != ":") {
                        this.addSpan(div, " &nbsp; : &nbsp; ", true);
                        div.appendChild(this.ast2HTML("", displayAst.checked, [], [], currentIdx));
                    }
                    input["ttDisplayDeferred"] = false;
                } else {
                    input["ttDisplayDeferred"] = true;
                }
                continueValidation(continueAfter && !!nextInput && (ast?.type === ":=" || !!ev["updateDefs"]));
            };
            const validateSynchronously = () => {
                try {
                    ensureMainContext();
                    let filledDefinition: AST;
                    if (ast.type === ":=") {
                        if (ast.nodes[0].type !== "var") throw TR(":=符号左侧仅允许出现自定义常量");
                        const defname = ast.nodes[0].name;
                        if (this.hasDefinitionNameConflict(defname, currentIdx, this.getDefaultTacticScope(input))) {
                            throw defname + TR("的定义重复");
                        }
                        if (reservedConsts.has(defname)) throw defname + TR("由系统保留");
                        const checkedDefinition = this.core.checkDefinition(ast, []);
                        filledDefinition = checkedDefinition.filledDefinition;
                        this.core.restoreDefinitionCache(defname, checkedDefinition.definitionCache);
                    } else {
                        this.core.checkType(ast, [], false);
                    }
                    const inferenceTarget = theoremInferenceTarget(ast, filledDefinition);
                    const inferenceComplete = theoremInferenceComplete(inferenceTarget);
                    finish(ast, "", filledDefinition, undefined, false, true, inferenceComplete);
                } catch (e) {
                    finish(ast, String(e));
                }
            };
            if (!ast) {
                finish(ast, parseError);
                return;
            }
            if (ast.type === ":=") {
                try {
                    if (ast.nodes[0].type !== "var") throw TR(":=符号左侧仅允许出现自定义常量");
                    const defname = ast.nodes[0].name;
                    if (this.hasDefinitionNameConflict(defname, currentIdx, this.getDefaultTacticScope(input))) {
                        throw defname + TR("的定义重复");
                    }
                    if (reservedConsts.has(defname)) throw defname + TR("由系统保留");
                } catch (e) {
                    finish(ast, String(e));
                    return;
                }
            }
            if (!this.coreWorker || ev["forceSync"]) {
                validateSynchronously();
                return;
            }
            const inputValue = input.value;
            const workerScopeId = this.getDefaultTacticScope(input);
            wrapper.classList.add("checking");
            const rowStillCurrent = () => input["workerRequestId"] === requestId
                && input.value === inputValue
                && input.isConnected
                && rowPositionMatches();
            this.prepareCoreWorker(currentIdx, workerScopeId).then(() => {
                if (!rowStillCurrent()) {
                    if (validationRunId !== null) this.completeTheoremValidation(validationRunId);
                    return null;
                }
                return this.validateCoreWorker(currentIdx, Core.clone(ast, true), [], Core.timeout);
            }).then(result => {
                if (!result) return;
                if (input["workerRequestId"] !== requestId || input.value !== inputValue || !input.isConnected) {
                    if (validationRunId !== null) this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (!rowPositionMatches()) {
                    if (validationRunId !== null) this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (result.timeout) document.getElementById("timeout").classList.remove("hide");
                // `validate` mutates the remote ordered slot even when the
                // theorem is not a definition or fails. Record the null first;
                // a successful definition replaces it inside `finish` below.
                this.coreWorker?.rememberDefinition(currentIdx, null);
                if (result.ok) {
                    finish(
                        result.ast,
                        "",
                        result.filledDefinition,
                        result.definitionCache,
                        true,
                        true,
                        result.inferenceComplete
                    );
                }
                else finish(ast, result.error);
            }).catch(workerError => {
                if (input["workerRequestId"] !== requestId || input.value !== inputValue || !input.isConnected) {
                    if (validationRunId !== null) this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (!rowPositionMatches()) {
                    if (validationRunId !== null) this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (!shouldFallbackToSynchronousTheoremValidation(workerError)) {
                    const timedOut = typeTheoryValidationTimedOut(workerError);
                    if (timedOut) document.getElementById("timeout").classList.remove("hide");
                    finish(
                        ast,
                        timedOut
                            ? TR("类型论 Worker 验证超时，请增大单条定理判定的默认等待时间")
                            : String(workerError),
                        undefined,
                        undefined,
                        false,
                        false
                    );
                    return;
                }
                validateSynchronously();
            });
        };
        div.addEventListener("click", ev => {
            if ((this.mode === "tactic-begin" || this.tacticSelectingTarget)
                && !this.isTheoremInputDisabled(input)) {
                this.executeTactic(input.value, input);
            } else {
                input["editingCanReuseRenderedResult"] = true;
                this.suspendTheoremTypeTag(input);
                input.classList.remove("hide");
                input.focus();
                div.classList.add("hide");
            }
        });
        button.classList.add("inhabitat-modify");
        button.innerText = "+";
        const wrapper = document.createElement("div");
        wrapper.classList.add("wrapper");
        const id = this.createTheoremItemId("theorem");
        const previousDefinitions = this.restoringTheoremItems ? [] : this.userDefinedConsts.slice();
        this.createTheoremDragHandle(wrapper, id);
        wrapper.appendChild(button);
        wrapper.appendChild(localLabel);
        wrapper.appendChild(input);
        wrapper.appendChild(div);
        const theorem: Extract<TTTheoremItem, { kind: "theorem" }> = { kind: "theorem", id, wrapper, input, localCheckbox };
        if (!this.restoringTheoremItems) {
            const insertIndex = destinationFolder
                ? workspace.folderAppendIndex(destinationFolder.id)
                : insertionItemIndex;
            const parentFolderId = destinationFolder
                ? destinationFolder.id
                : insertPos ? undefined : null;
            const mutation = workspace.insertTheorem({
                kind: "theorem",
                id,
                value: input.value,
                local: localCheckbox.checked
            }, insertIndex, parentFolderId);
            this.applyTheoremWorkspaceSnapshot(mutation.snapshot, [theorem]);
            this.syncTheoremDomOrder();
            this.realignUserDefinitions(previousInputs, previousDefinitions);
            this.renderTheoremStructure();
            this.reconcileProofSessionBindings(false);
        }
        // The newly inserted row is intentionally left empty and focused.  If
        // there are existing rows after it, validate those rows starting after
        // the new row so they regain their correct definition slots.
        const suffixStart = insertionInputIndex + 1;
        if (!this.restoringTheoremItems && suffixStart < this.getInhabitatArray().length) {
            this.revalidateTheorems(suffixStart);
        }
        button.addEventListener("click", () => {
            this.updateInhabitList(wrapper);
        });
        localCheckbox.addEventListener("change", () => {
            const currentIdx = this.getInhabitatArray().indexOf(input);
            if (currentIdx < 0) return;
            const mutation = this.getTheoremWorkspace().updateTheorem(id, {
                local: localCheckbox.checked
            });
            if (mutation.changed) this.applyTheoremWorkspaceSnapshot(mutation.snapshot);
            this.definitionRevision++;
            this.theoremStructureRevision++;
            this.gatePreviewStructureRevision = -1;
            this.onStateChange();
            this.revalidateTheorems(currentIdx);
        });
        if (this.restoringTheoremItems) {
            // Restore builds the flat DOM list first. Inserting into the
            // workspace here would normalize folder lengths against a
            // partial suffix and destroy nested save structure.
            this.appendRestoredTheoremItem(theorem);
            return input;
        }
        if (!this.restoringTheoremItems) input.focus();
        return input;
    }
    private getTacticOutputInsertPosition() {
        const target = this.tacticTargetInput && this.getTheoremItemForInput(this.tacticTargetInput);
        if (target) return target.wrapper;
        return undefined;
    }
    private getTacticOutputFolder() {
        if (this.tacticTargetInput) return undefined;
        const scopeId = this.getActiveTacticScopeId();
        return this.theoremItems.find((item): item is Extract<TTTheoremItem, { kind: "folder" }> =>
            item.kind === "folder" && item.id === scopeId);
    }
    private getFolderAppendIndex(folder: Extract<TTTheoremItem, { kind: "folder" }>) {
        return this.syncTheoremWorkspaceFromDom().folderAppendIndex(folder.id);
    }
    private settlePendingTheorems(coordinateValidation = false) {
        const inputs = this.getInhabitatArray();
        const first = findEarliestPendingTheorem(
            inputs,
            input => !!input.parentElement?.classList.contains("checking"),
            input => this.isTheoremInputDisabled(input)
        );
        if (!first) return;
        if (coordinateValidation) {
            const startIndex = inputs.indexOf(first);
            if (startIndex >= 0) this.revalidateTheorems(startIndex);
            return;
        }
        first.onblur({ forceSync: true, updateDefs: true } as any);
    }
    private equalGateTypes(candidate: AST, target: AST) {
        return this.core.semanticTypePatternMatch(candidate, target);
    }
    // find whether user has inhabitat of given type
    queryType(typeStr: string) {
        if (this.gateQueryCache.has(typeStr)) return this.gateQueryCache.get(typeStr);
        const inputs = this.getInhabitatArray();
        let ref: AST;
        try {
            ref = parser.parse(typeStr);
        } catch (error) {
            this.gateQueryCache.set(typeStr, false);
            return false;
        }
        const refKey = parser.stringify(ref);
        const candidates: AST[] = [];
        for (const e of inputs) {
            if (this.isTheoremInputDisabled(e)) continue;
            const wrapper = e.parentElement;
            if (!wrapper || wrapper.classList.contains("error") || wrapper.classList.contains("infering") || wrapper.classList.contains("checking")) continue;
            const checked = e["validatedType"] as AST;
            if (!checked) continue;
            if (e.dataset.validatedTypeKey === refKey) {
                this.gateQueryCache.set(typeStr, true);
                return true;
            }
            candidates.push(checked);
        }
        if (candidates.length) {
            this.getHottDefCtxt(inputs.length);
            this.core.state.disableSimpleFn = this.disableSimpleFn;
            this.core.state.disableSimpleEq = this.disableSimpleEq;
        }
        for (const checked of candidates) {
            try {
                if (this.equalGateTypes(Core.clone(checked, true), Core.clone(ref, true))) {
                    this.gateQueryCache.set(typeStr, true);
                    return true;
                }
            } catch (e) {
                continue;
            }
        }
        this.gateQueryCache.set(typeStr, false);
        return false;
    }
    queryDefPuzzle(name: string) {
        this.settlePendingTheorems();
        this.getHottDefCtxt(this.getInhabitatArray().length);
        // Puzzle probes run on the main-thread Core after Worker validation.
        // Do not inherit a stale syntax mode from startup, type-list rebuilds,
        // or an earlier gate query: it can make a valid restored definition
        // fail only in the UI even though the Worker accepted it.
        this.core.state.disableSimpleFn = this.disableSimpleFn;
        this.core.state.disableSimpleEq = this.disableSimpleEq;

        const def = this.core.state.userDefs[name];
        if (!def) return false;
        const defvar = wrapVar(name);
        try {
            if (name === "code_nat") {
                const True = wrapVar("True"); const False = wrapVar("False");
                let testSet = ["0", "1", Math.round(Math.random() * 5 + 5).toString(), Math.round(Math.random() * 5 + 10).toString()];
                for (let i = 0; i < testSet.length; i++) {
                    const A = wrapVar(testSet[i]);
                    this.core.checkType({ type: "===", name: "", nodes: [wrapApply(defvar, A, Core.clone(A)), True] }, [], false);
                }
                let testSet2 = [Math.round(Math.random() * 5 + 5).toString(), "0", "3", "16"];
                for (let i = 0; i < testSet.length; i++) {
                    const A = wrapVar(testSet[i]);
                    const B = wrapVar(testSet2[i]);
                    this.core.checkType({ type: "===", name: "", nodes: [wrapApply(defvar, A, B), False] }, [], false);
                }
            } else if (name === "what") {
                this.core.checkType({ type: "===", name: "", nodes: [wrapApply(defvar, wrapVar("0b")), wrapApply(defvar, wrapVar("1b"), wrapVar("True"))] }, [], false);
            } else if (name === "ftr") {
                this.core.checkType({ type: "===", name: "", nodes: [wrapApply(defvar, wrapVar("0")), wrapVar("True")] }, [], false);
                let k = "True";
                for (let i = 1; i < 5; i++) {
                    k += "->True";
                    this.core.checkType(parser.parse(`ftr ${i} === ` + k), [], false);
                }
            } else if (name === "fillList") {
                this.core.checkType(parser.parse("fillList Bool 0b 2 === cons 0b (cons 0b nil)"), [], false);
                this.core.checkType(parser.parse("fillList nat 33 3 === cons 33 (cons 33 (cons 33 nil))"), [], false);
                this.core.checkType(parser.parse("fillList True true 0 === nil"), [], false);
            } else if (name === "joinList") {
                this.core.checkType(parser.parse("joinList nat (cons 10 nil) (cons 2 nil) === cons 10 (cons 2 nil)"), [], false);
                this.core.checkType(parser.parse("joinList nat nil (cons 2 nil) === (cons 2 nil)"), [], false);
                this.core.checkType(parser.parse("joinList False nil nil === nil"), [], false);
                this.core.checkType(parser.parse("joinList True (cons true (cons true nil)) nil === (cons true (cons true nil))"), [], false);
                this.core.checkType(parser.parse("joinList Bool (cons 0b (cons 0b nil)) (cons 1b nil) === (cons 0b (cons 0b (cons 1b nil)))"), [], false);
            } else if (name === "lenList") {
                this.core.checkType(parser.parse("lenList Bool (cons 0b nil) === 1"), [], false);
                this.core.checkType(parser.parse("lenList nat (cons 33 (cons 0 (cons 1 nil)))=== 3"), [], false);
                this.core.checkType(parser.parse("lenList False nil === 0"), [], false);
            } else if (name === "sumList") {
                this.core.checkType(parser.parse("sumList (cons 14 nil) === 14"), [], false);
                this.core.checkType(parser.parse("sumList (cons 0 (cons 0 (cons 0 nil)))=== 0"), [], false);
                this.core.checkType(parser.parse("sumList (cons 3 (cons 6 (cons 8 nil)))=== 17"), [], false);
                this.core.checkType(parser.parse("sumList nil === 0"), [], false);
            } else if (name === "mapList") {
                this.core.checkType(parser.parse("mapList False nat (ind_False (Lx:False,nat)) nil === nil"), [], false);
                this.core.checkType(parser.parse("mapList nat nat succ (cons 0 (cons 1 (cons 2 nil))) === (cons 1 (cons 2 (cons 3 nil)))"), [], false);
                this.core.checkType(parser.parse("mapList nat (natXnat) (Lx:nat.(x,succ x)) (cons 3 (cons 2 nil)) === (cons (3,4) (cons (2,3) nil))"), [], false);
            } else if (name === "invList") {
                this.core.checkType(parser.parse("invList Bool (cons 0b nil) === cons 0b nil"), [], false);
                this.core.checkType(parser.parse("invList nat (cons 23 (cons 0 (cons 1 nil))) === (cons 1 (cons 0 (cons 23 nil)))"), [], false);
                this.core.checkType(parser.parse("invList True nil === nil"), [], false);
            } else if (name === "firstList") {
                this.core.checkType(parser.parse("firstList False nil === none"), [], false);
                this.core.checkType(parser.parse("firstList Bool (cons 0b nil) === some 0b"), [], false);
                this.core.checkType(parser.parse("firstList nat (cons 12 (cons 3 (cons 45 nil))) === some 45"), [], false);
            } else if (name === "lastList") {
                this.core.checkType(parser.parse("lastList False nil === none"), [], false);
                this.core.checkType(parser.parse("lastList Bool (cons 1b nil) === some 1b"), [], false);
                this.core.checkType(parser.parse("lastList nat (cons 45 (cons 0 (cons 20 nil))) === some 45"), [], false);
            } else if (name === "del_0") {
                this.core.checkType(parser.parse("del_0 nil === nil"), [], false);
                this.core.checkType(parser.parse("del_0 (cons 0 nil) === nil"), [], false);
                this.core.checkType(parser.parse("del_0 (cons 45 (cons 0 (cons 20 nil))) === cons 45 (cons 20 nil)"), [], false);
            } else if (name === "count_0") {
                this.core.checkType(parser.parse("count_0 nil === 0"), [], false);
                this.core.checkType(parser.parse("count_0 (cons 0 nil) === 1"), [], false);
                this.core.checkType(parser.parse("count_0 (cons 45 (cons 0 (cons 20 (cons 0 nil)))) === 2"), [], false);
                // } else if (name === "Aleph") {
                //     let k = wrapVar("nat");
                //     for (let i = 0; i < 5; i++) {
                //         this.core.checkType({
                //             type: "===", name: "", nodes: [
                //                 wrapApply(defvar, wrapVar(String(i))), k
                //             ]
                //         }, [], false);
                //         k = wrapLambda("->", "", k, wrapVar("Bool"));
                //     }
            } else if (name === "ftreq") {
                let p = "";
                let a = "";
                let ap = "";
                for (let i = 0; i < 5; i++) {
                    this.core.checkType(parser.parse(`ftreq ${i} === Lx:ftr ${i},${p}eq (x ${a}) true`), [], false);
                    p += `Pa${ap}:True,`;
                    a += `a${ap} `;
                    ap += "'";
                }
            } else if (name === "Fin") {
                this.core.checkType({ type: "===", name: "", nodes: [wrapApply(defvar, wrapVar("0")), wrapVar("False")] }, [], false);
                let k = "False";
                for (let i = 1; i < 5; i++) {
                    k += "+True";
                    this.core.checkType(parser.parse(`Fin ${i} === ` + k), [], false);
                }
            } else if (name === "factorial2") {
                const table = [1, 1, 2, 3, 8, 15, 48, 105, 384, 945, 3840, 10395, 46080, 135135, 645120, 2027025, 10321920, 34459425, 185794560, 654729075, 3715891200, 13749310575, 81749606400, 316234143225, 1961990553600, 7905853580625, 51011754393600, 213458046676875];
                for (let i = Math.random() > 0.5 ? 2 : 1; i < 25; i += 3) {
                    ;
                    this.core.checkType(parser.parse(`factorial2 ${i} === ` + table[i]), [], false);
                }
            } else if (name === "Combin") {
                const combin = (a: number, b: number) => {
                    if (b === 0 || b === a) return 1;
                    let res = 1;
                    for (let i = 1; i <= b; i++) {
                        res = res * (a - i + 1) / i;
                    }
                    return res;
                };
                for (let i = 0; i < 10; i++) {
                    const a = Math.round(Math.random() * 8);
                    const b = Math.round(Math.random() * a);
                    this.core.checkType(parser.parse(`Combin ${a} ${b} === ` + combin(a, b)), [], false);
                }
            } else return false;
        } catch (e) {
            return false;
        }
        return true;
    }
    async executeTactic(
        value: string | AST,
        targetInput: HTMLInputElement | null = null,
        initialScopeFolderId?: string | null
    ) {
        if (this.tacticBusy) return;
        this.proofSessions ??= new TTProofSessionStore();
        this.settlePendingTheorems(true);
        const target = typeof value === "string" ? value : parser.stringify(value);
        this.captureActiveTacticSession();
        let session: TTProofSession;
        const theoremItem = targetInput ? this.getTheoremItemForInput(targetInput) : null;
        if (theoremItem?.kind === "theorem") {
            const targetTheoremIndex = this.getInhabitatArray().indexOf(targetInput);
            const scopeExplicit = initialScopeFolderId !== undefined;
            session = this.proofSessions.openTheorem({
                target,
                theoremItemId: theoremItem.id,
                targetTheoremIndex,
                scopeFolderId: scopeExplicit
                    ? initialScopeFolderId ?? null
                    : this.getDefaultTacticScope(targetInput),
                ...(scopeExplicit ? { scopeExplicit: true } : {})
            }, true);
        } else if (initialScopeFolderId !== undefined) {
            session = this.proofSessions.openGate({
                target,
                scopeFolderId: initialScopeFolderId,
                scopeExplicit: true
            }, true);
        } else {
            session = this.proofSessions.openManual({ target }, true);
        }
        this.tacticSelectingTarget = false;
        this.renderTacticSessionTabs();
        this.onStateChange();
        await this.activateTacticSession(session.id, false);
    }
    async addTactic(_noCheck: boolean) {
        const input = document.getElementById("tactic-input") as HTMLInputElement;
        const hint = document.getElementById("tactic-hint");
        if (!this.mode) {
            this.beginTacticTargetSelection();
            return;
        }
        if (!(this.mode instanceof Array) || this.tacticBusy) return;

        const value = input.value.trim();
        const commandEnd = value.indexOf(" ");
        const command = commandEnd === -1 ? value : value.slice(0, commandEnd);
        const parameter = commandEnd === -1 ? null : value.slice(commandEnd);
        const requestId = ++this.tacticRequestId;
        this.setTacticBusy(true);
        document.getElementById("tactic-errmsg").innerText = "";
        try {
            if (command === "qed") {
                const qedName = parameter?.trim();
                if (qedName) {
                    const nameAst = parser.parse(qedName);
                    if (nameAst?.type !== "var" || nameAst.name !== qedName) {
                        throw new Error(TR("qed命名参数必须是单个常量名"));
                    }
                }
                const result = await this.finishAssistProof();
                if (requestId !== this.tacticRequestId || !(this.mode instanceof Array)) return;
                const output = this.updateInhabitList(
                    this.getTacticOutputInsertPosition(),
                    this.getTacticOutputFolder()
                );
                output.focus();
                output.value = qedName
                    ? `${qedName}:=${result.proof}:${result.theorem}`
                    : `${result.proof}:${result.theorem}`;
                output.dispatchEvent(new Event("input"));
                this.resetTacticPage();
                output.blur();
                return;
            }

            if (this.unlockedTactics && !this.unlockedTactics.has(command)) {
                throw new Error(TR("未知的证明策略"));
            }
            const target = this.mode[0];
            const previousHistory = this.mode.slice(1);
            let snapshot = await this.applyAssistCommand(value);
            if (this.tacticDefinitionsRevision !== this.definitionRevision) {
                snapshot = await this.startAssistSession(target, [...previousHistory, value]);
                this.tacticDefinitionsRevision = this.definitionRevision;
            }
            if (requestId !== this.tacticRequestId || !(this.mode instanceof Array)) return;
            this.mode = [target, ...snapshot.history];
            if (this.proofSessions.activeId) {
                this.proofSessions.update(this.proofSessions.activeId, {
                    history: snapshot.history,
                    script: snapshot.history.join("\n"),
                    stale: false
                });
                if (this.tacticCaptureBlockedSessionId === this.proofSessions.activeId) {
                    this.tacticCaptureBlockedSessionId = null;
                }
            }
            input.value = "";
            this.resizeTacticInput();
            this.renderAssistSnapshot(snapshot);
            this.renderTacticSessionTabs();
            this.onStateChange();
            input.focus();
        } catch (error) {
            if (requestId === this.tacticRequestId) {
                document.getElementById("tactic-errmsg").innerText = this.formatTacticError(error);
                input.focus();
            }
        } finally {
            if (requestId === this.tacticRequestId) this.setTacticBusy(false);
        }
    }
    getInhabitatArray() {
        return this.getTheoremInputsFromItems();
    }
    unlock(str: string, update?: boolean) {
        this.unlockedTypes.add(str);
        if (update && !this.skipRendering) {
            this.updateTypeList(this.unlockedTypes);
            this.getInhabitatArray()[0]?.onblur({ updateDefs: true } as any);
        }
    }
    updateAfterUnlock() {
        if (this.skipRendering) return;
        this.updateTypeList(this.unlockedTypes);
        this.warmCoreWorkerWhenEmpty();
        this.revalidateTheorems();
        void this.restorePendingProofSessionsWhenReady();
    }

    /**
     * Install validated sandbox axioms into the creative type-layer context.
     * Survival mode never accepts this bridge, so sandbox state cannot alter
     * its unlocks, theorem rows, map gates, or achievements.
     */
    setSandboxAxioms(
        input: SandboxBridge | readonly [string, AST][],
        options: SandboxBridgeChangeOptions = {}
    ) {
        if (!this.creativeMode) return;
        const previousSandboxNames = new Set<string>([
            ...(this.sandboxAxiomNames ?? []),
            ...(this.sandboxDefinitionNames ?? [])
        ]);
        for (const bundle of this.sandboxInductives ?? []) {
            previousSandboxNames.add(bundle.type[0]);
            for (const [name] of bundle.auxiliaryTypes ?? []) previousSandboxNames.add(name);
            for (const [name] of bundle.constructors ?? []) previousSandboxNames.add(name);
            if (bundle.eliminator) previousSandboxNames.add(bundle.eliminator[0]);
            if (bundle.recursor) previousSandboxNames.add(bundle.recursor[0]);
            for (const [name] of bundle.definitions ?? []) previousSandboxNames.add(name);
        }
        for (const name of previousSandboxNames) {
            consts.delete(name);
            constructors.delete(name);
            destructors.delete(name);
            computeEqs.delete(name);
            macro.delete(name);
        }
        for (const name of this.sandboxAxiomNames ?? []) {
            this.core.setSystemType(name);
        }
        // Transparent definitions are a separate projection from axioms and
        // inductive bundles. Remove the previous projection first, otherwise
        // a disabled/replaced sandbox definition remains visible to delta
        // reduction and can trigger a false name conflict on re-install.
        for (const name of this.sandboxDefinitionNames ?? []) {
            this.core.setSystemDefinition(name);
            this.core.clearDefinitionCache(name);
        }
        this.sandboxAxioms = [];
        this.sandboxAxiomNames = new Set<string>();
        this.sandboxInductives = [];
        this.sandboxDefinitions = [];
        this.sandboxDefinitionNames = new Set<string>();
        this.sandboxDeclarationOrder = undefined;
        // Inductive bundles are installed as a transaction by Core. Clear the
        // previous sandbox projection before installing the new bridge so a
        // disabled/replaced declaration cannot survive as a stale constant.
        this.core.clearSystemInductives();
        const bridge: SandboxBridge = !Array.isArray(input) && input && "axioms" in input
            ? input
            : {
                axioms: Array.isArray(input) ? input as readonly [string, AST][] : [],
                inductives: [],
                definitions: []
            };
        const axioms = Array.isArray(bridge.axioms) ? bridge.axioms : [];
        const inductives = Array.isArray(bridge.inductives) ? bridge.inductives : [];
        const definitions = Array.isArray(bridge.definitions) ? bridge.definitions : [];
        const nextAxioms = axioms.map(([name, type]) => [
            name,
            Core.clone(type)
        ] as [string, AST]);
        const nextInductives = inductives.map(bundle => cloneInductiveBundle(bundle));
        const nextDefinitions = definitions.map(([name, definition]) => [
            name,
            Core.clone(definition)
        ] as [string, AST]);
        const nextOrder = bridge.order === undefined
            ? undefined
            : bridge.order.map(entry => ({ kind: entry.kind, name: entry.name }));
        installTrustedDeclarations(this.core, {
            trustedAxioms: nextAxioms,
            trustedInductives: nextInductives,
            trustedDefinitions: nextDefinitions,
            trustedDeclarationOrder: nextOrder
        });
        this.sandboxAxioms = nextAxioms;
        this.sandboxAxiomNames = new Set(this.sandboxAxioms.map(([name]) => name));
        this.sandboxInductives = nextInductives;
        this.sandboxDefinitions = nextDefinitions;
        this.sandboxDefinitionNames = new Set(this.sandboxDefinitions.map(([name]) => name));
        this.sandboxDeclarationOrder = nextOrder;
        this.core.syncSemanticDefinitions();
        this.core.syncSemanticTypes();
        this.invalidateHottDefCtxt();
        this.definitionRevision++;
        this.coreWorkerStateRevision++;
        this.coreWorkerGeneration = -1;
        this.coreWorkerConfigKey = "";
        this.coreWorkerConfigurePromise = null;
        this.coreWorkerLoadedThrough = 0;
        this.assistWorkerSessionReady = false;
        this.assistWorkerGeneration = -1;
        this.assistWorkerConfigKey = "";
        this.assistWorkerConfigurePromise = null;
        this.tacticDefinitionsRevision = -1;
        if (!this.skipRendering) {
            if (options.revalidate === false) {
                const inputs = this.getInhabitatArray();
                const previousUserNames = this.userDefinedConsts
                    .filter((definition): definition is definedConst => !!definition)
                    .map(definition => definition[0]);
                this.invalidateTheoremChecks(0, true);
                this.clearUserDefinitionContext();
                for (const name of previousUserNames) macro.delete(name);
                this.userDefinedConsts = inputs.map(() => null);
                for (const input of inputs) input["validationInvalidated"] = true;
                this.refreshUserConstNames();
                this.gateQueryCache.clear();
            } else {
                this.updateTypeList(this.unlockedTypes);
                this.revalidateTheorems();
                void this.restorePendingProofSessionsWhenReady();
            }
        }
    }
    private warmCoreWorkerWhenEmpty() {
        if (!this.coreWorker) return;
        const hasTheorems = this.theoremItems
            ? this.theoremItems.some(item => item.kind === "theorem" && item.input.value.trim())
            : !!this.userDefinedConsts?.length;
        if (hasTheorems) return;
        // Configuration is expensive but runs off the UI thread. Starting it
        // while the empty editor is idle means the first short expression can
        // reuse the ready session instead of paying the fixed bootstrap cost.
        void this.prepareCoreWorker(0, null).catch(() => { });
    }
    disableAxiom(...arr: string[]) {
        for (const a of arr) {
            this.unlockedTypes.add("// " + a);
            this.unlockedTypes.add("// @" + a);
        }
        this.updateAfterUnlock();
    }
    enableAxiom(...arr: string[]) {
        for (const a of arr) {
            this.unlockedTypes.delete("// " + a);
            this.unlockedTypes.delete("// @" + a);
        }
        this.updateAfterUnlock();
    }
}
