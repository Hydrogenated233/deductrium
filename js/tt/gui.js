import { langMgr, TR } from "../lang.js";
import { ASTParser, debugBoundVarId } from "./astparser.js";
import { Core, assignContext, wrapApply, wrapVar, wrapLambda } from "./core.js";
import { TTCoreWorkerClient } from "./core-worker-client.js";
import { TTAssistEngine } from "./assist-engine.js";
import { TTAssistWorkerClient } from "./assist-worker-client.js";
import { Assist } from "./assist.js";
import { TTWorkerMutationQueue } from "./worker-mutation-queue.js";
import { ListDragger } from "../fs/itemdragger.js";
import { initTypeSystem } from "./initial.js";
import { canReuseTheoremResultOnBlur, findEarliestPendingTheorem, isKnownTheoremIdentifier, shouldFallbackToSynchronousTheoremValidation, theoremInferenceComplete, theoremInferenceStatus, theoremInferenceTarget, theoremInputIndexBeforeItem, theoremPreviewNeedsRefresh, theoremValidationPositionMatches, TheoremValidationCoordinator } from "./theorem-validation.js";
const parser = new ASTParser;
const constructors = new Set();
const destructors = new Set();
const computeEqs = new Set();
const macro = new Set();
const sysmacro = new Set();
let consts = new Set;
const allrules = initTypeSystem();
const reservedConsts = new Set;
export class TTGui {
    puzzleDefs = new Set;
    skipRendering = true;
    onStateChange = () => { };
    core = new Core;
    disableSimpleFn = false;
    disableSimpleEq = false;
    displayPi = true;
    enablecopygate = false;
    lastGateTarget = "";
    // gamecore = new HoTTGame;
    typeList = document.getElementById("type-list");
    unlockedTypes;
    unlockedTactics;
    inhabitList = document.getElementById("inhabit-list");
    theoremItems = [];
    theoremItemSequence = 0;
    restoringTheoremItems = false;
    theoremDragger = new ListDragger(this.inhabitList);
    // tactic mode: tactic-begin for waiting clicking theorem
    mode = null;
    // "_" for infered, "@" for original
    inferDisplayMode = "_";
    userDefinedConsts = [];
    /** Names of successfully checked user definitions used by AST rendering. */
    userConstNames = new Set();
    sysDefinedConsts = [];
    coreWorker = null;
    assistWorker = null;
    assistWorkerGeneration = -1;
    assistWorkerConfigKey = "";
    assistWorkerConfigurePromise = null;
    assistWorkerMutations = new TTWorkerMutationQueue();
    assistFallback = new TTAssistEngine();
    assistOptions = {
        disableMultipleApply: true,
        disableDestructConds: true,
        disableDestructEq: true
    };
    assistSnapshot = null;
    assistWorkerSessionReady = false;
    tacticBusy = false;
    tacticRequestId = 0;
    tacticTargetInput = null;
    tacticScopeFolderId = null;
    tacticScopeExplicit = false;
    tacticDefinitionsRevision = -1;
    coreWorkerGeneration = -1;
    coreWorkerConfigKey = "";
    coreWorkerConfigurePromise = null;
    coreWorkerMutations = new TTWorkerMutationQueue();
    definitionRevision = 0;
    /** Changes whenever theorem rows are inserted, removed, or reordered. */
    theoremStructureRevision = 0;
    workerRequestId = 0;
    theoremValidation = new TheoremValidationCoordinator();
    gateQueryCache = new Map();
    gatePreviewRevision = -1;
    gatePreviewStructureRevision = -1;
    gatePreviewScopeId = null;
    /** Explicit scope used while synchronously rendering a gate preview. */
    astRenderScopeFolderId;
    initTypeList() {
        const expand = {};
        for (const rule of allrules) {
            if (rule.ast.type === ":=" && rule.ast.nodes[0].type === "var") {
                let sub = rule.ast.nodes[1];
                const applyList = [];
                let isInfer = true;
                while (sub.type === "apply") {
                    applyList.unshift(sub.nodes[1]);
                    if (sub.nodes[1].name !== "_" || sub.nodes[1].type !== "var")
                        isInfer = false;
                    sub = sub.nodes[0];
                }
                applyList.unshift(sub);
                if (sub.name[0] === "@" && isInfer)
                    this.core.opaque.push([rule.ast.nodes[0].name, applyList.length]);
                expand[rule.ast.nodes[0].name] = applyList;
            }
            if (rule.postfix === "计算" && rule.ast.type === "===" && rule.id !== "Function") {
                const applyList = [];
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
                let sub2;
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
    }
    constructor(creative, skipRendering) {
        if (typeof Worker !== "undefined") {
            try {
                this.coreWorker = new TTCoreWorkerClient();
            }
            catch (error) {
                console.warn("Type-theory worker unavailable", error);
            }
            try {
                this.assistWorker = new TTAssistWorkerClient();
            }
            catch (error) {
                console.warn("Proof-assistant worker unavailable", error);
            }
        }
        this.skipRendering = skipRendering;
        this.theoremDragger.cols = 1;
        this.theoremDragger.onExecute = (src, dst) => this.moveTheoremItem(src, dst === "+" ? " " : dst);
        this.unlockedTypes = new Set(creative ? allrules.map(r => r.id) : ["True", "False"]);
        if (!skipRendering)
            this.updateTypeList(this.unlockedTypes);
        if (!creative) {
            this.unlockedTactics = new Set(["qed"]);
            this.disableSimpleFn = true;
            this.disableSimpleEq = true;
            this.puzzleDefs = new Set([
                "what", "Fin", "code_nat", "ftr", "ftreq", "Combin", "factorial2",
                "fillList", "lastList", "firstList", "lenList", "invList", "sumList", "mapList",
                "count_0", "del_0", "joinList",
            ]);
        }
        else {
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
        const input = document.getElementById("tactic-input");
        input.addEventListener("keydown", (ev) => {
            if (ev.key === "Enter" || ev.key === "Escape") {
                document.getElementById("tactic-begin").click();
            }
        });
        document.getElementById('timeSelect').addEventListener('change', function () {
            Core.timeout = Number(this.value) * 1000;
        });
        document.getElementById("tactic-scope")?.addEventListener("change", () => {
            if (!(this.mode instanceof Array) || this.tacticBusy)
                return;
            const select = document.getElementById("tactic-scope");
            this.tacticScopeFolderId = select.value || null;
            this.tacticScopeExplicit = true;
            this.tacticDefinitionsRevision = -1;
            const requestId = ++this.tacticRequestId;
            this.renderTacticScopeOptions();
            this.ensureAssistSessionCurrent().then(snapshot => {
                if (requestId !== this.tacticRequestId || !(this.mode instanceof Array))
                    return;
                this.renderAssistSnapshot(snapshot);
            }).catch(error => {
                if (requestId === this.tacticRequestId) {
                    document.getElementById("tactic-errmsg").innerText = this.formatTacticError(error);
                }
            });
        });
        document.getElementById("tactic-remove").addEventListener("click", () => void this.removeTactic());
        document.getElementById("tactic-clear").addEventListener("click", () => void this.removeTactic(true));
        document.getElementById("tactic-begin").addEventListener("click", () => {
            this.addTactic(false);
        });
    }
    setLastGateTarget(target) {
        if (!theoremPreviewNeedsRefresh(target, this.lastGateTarget, this.definitionRevision, this.gatePreviewRevision, this.theoremStructureRevision, this.gatePreviewStructureRevision))
            return;
        if (target !== this.lastGateTarget)
            this.gatePreviewScopeId = null;
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
        btn.classList.add("inhabitat-modify");
        btn.innerText = "+";
        copygate.appendChild(btn);
        scopeSelect.value = this.gatePreviewScopeId ?? "";
        scopeSelect.addEventListener("change", () => {
            this.gatePreviewScopeId = scopeSelect.value || null;
            this.gatePreviewRevision = -1;
            this.setLastGateTarget(target);
        });
        btn.onclick = () => {
            this.executeTactic(target, null, scopeSelect.value || null);
        };
        copygate.appendChild(this.renderAstInScope("", parser.parse(target), [], [], this.getInhabitatArray().length, this.gatePreviewScopeId));
    }
    autofillTactics(allTactics) {
        let tactics;
        if (this.unlockedTactics) {
            tactics = [];
            // only for survival. If creative, this.unlockedTactics is undefined
            for (const t of allTactics) {
                const prefix = t.split(" ")[0];
                if (this.unlockedTactics.has(prefix)) {
                    tactics.push(t);
                }
            }
        }
        else {
            tactics = allTactics;
        }
        const div = document.getElementById("tactic-autofill");
        const inp = document.getElementById("tactic-input");
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
                }
                else {
                    inp.focus();
                    inp.selectionStart = t.indexOf("??");
                    inp.selectionEnd = inp.selectionStart + 2;
                }
            });
        }
    }
    updateTacticStateDisplay(snapshot, statediv) {
        if (!snapshot.goals.length) {
            this.addSpan(statediv, TR("无目标，请输入qed结束"));
        }
        for (let count = snapshot.goals.length - 1; count >= 0; count--) {
            const g = snapshot.goals[count];
            statediv.appendChild(document.createElement("hr"));
            const goalDiv = document.createElement("div");
            const scope = g.context.map(e => ({ type: "var", name: e[0], bondVarId: e[2] }));
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
            if (count) {
                goalDiv.style.opacity = "0.5";
                goalDiv.style.backgroundColor = "#DDD";
            }
            goalDiv.appendChild(document.createElement("br"));
            statediv.appendChild(goalDiv);
        }
    }
    setTacticBusy(busy) {
        this.tacticBusy = busy;
        // Keep the original assistant's controls interactive. The internal
        // flag still prevents overlapping async commands.
    }
    /**
     * Assist tactics are configured when a Worker session starts.  Keep the
     * option change in TTGui as the source of truth and invalidate the active
     * session so the next command is rebuilt with the newly unlocked tactic.
     */
    setAssistOption(option, value) {
        if (this.assistOptions[option] === value)
            return;
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
    closeTacticSession() {
        this.tacticRequestId++;
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
        document.getElementById("tactic-clear").classList.add("hide");
        document.getElementById("copygate").classList.remove("hide");
        const input = document.getElementById("tactic-input");
        input.value = "";
        input.classList.add("hide");
        this.setTacticBusy(false);
        this.assistWorker?.clear().catch(() => { });
        this.assistFallback.clear();
    }
    async removeTactic(all = false) {
        if (this.tacticBusy)
            return;
        if (!(this.mode instanceof Array) || this.mode.length <= 1 || all) {
            this.closeTacticSession();
            return;
        }
        this.mode.pop();
        this.setTacticBusy(true);
        const requestId = ++this.tacticRequestId;
        try {
            let snapshot;
            if (this.tacticDefinitionsRevision === this.definitionRevision && this.assistWorker) {
                try {
                    snapshot = await this.assistWorker.undo(Core.timeout);
                    this.assistWorkerSessionReady = true;
                }
                catch {
                    snapshot = await this.startAssistFallback(this.mode[0], this.mode.slice(1));
                    this.assistWorkerSessionReady = false;
                }
            }
            else {
                snapshot = await this.startAssistSession(this.mode[0], this.mode.slice(1));
            }
            if (requestId !== this.tacticRequestId || !(this.mode instanceof Array))
                return;
            this.tacticDefinitionsRevision = this.definitionRevision;
            this.mode = [this.mode[0], ...snapshot.history];
            this.renderAssistSnapshot(snapshot);
        }
        catch (error) {
            if (requestId === this.tacticRequestId) {
                document.getElementById("tactic-errmsg").innerText = this.formatTacticError(error);
            }
        }
        finally {
            if (requestId === this.tacticRequestId)
                this.setTacticBusy(false);
        }
    }
    async startAssistSession(target, history = []) {
        const definitionEnd = this.getTacticDefinitionEnd();
        const scopeFolderId = this.getActiveTacticScopeId();
        if (this.assistWorker) {
            try {
                await this.prepareAssistWorker(definitionEnd, this.getWorkerSystemConfig(), this.getTacticWorkerDefinitionSlots(scopeFolderId), scopeFolderId, "tactic");
                await this.assistWorkerMutations.wait();
                const snapshot = await this.assistWorker.start(target, this.assistOptions, history, Core.timeout);
                this.assistWorkerSessionReady = true;
                return snapshot;
            }
            catch (workerError) {
                try {
                    const snapshot = await this.startAssistFallback(target, history);
                    this.assistWorkerSessionReady = false;
                    return snapshot;
                }
                catch (fallbackError) {
                    throw fallbackError ?? workerError;
                }
            }
        }
        return this.startAssistFallback(target, history);
    }
    async startAssistFallback(target, history, config) {
        const scopeFolderId = this.getActiveTacticScopeId();
        config ??= this.getTacticWorkerConfig(scopeFolderId);
        this.assistFallback.configure(config);
        return this.assistFallback.start(target, this.assistOptions, history);
    }
    async ensureAssistSessionCurrent() {
        if (!(this.mode instanceof Array))
            throw new Error(TR("请在定理列表中点选待证命题"));
        const workerSessionCurrent = !this.assistWorker
            || (this.assistWorkerSessionReady && this.assistWorkerGeneration === this.assistWorker.generation);
        if (this.tacticDefinitionsRevision === this.definitionRevision
            && workerSessionCurrent)
            return this.assistSnapshot;
        const snapshot = await this.startAssistSession(this.mode[0], this.mode.slice(1));
        this.tacticDefinitionsRevision = this.definitionRevision;
        this.mode = [this.mode[0], ...snapshot.history];
        this.assistSnapshot = snapshot;
        return snapshot;
    }
    async applyAssistCommand(command) {
        await this.ensureAssistSessionCurrent();
        if (this.assistWorker) {
            try {
                const snapshot = await this.assistWorker.apply(command, Core.timeout);
                this.assistWorkerSessionReady = true;
                return snapshot;
            }
            catch (workerError) {
                if (workerError?.operationError)
                    throw workerError;
                try {
                    await this.startAssistFallback(this.mode[0], this.mode.slice(1));
                    const snapshot = this.assistFallback.apply(command);
                    this.assistWorkerSessionReady = false;
                    return snapshot;
                }
                catch (fallbackError) {
                    throw fallbackError ?? workerError;
                }
            }
        }
        await this.startAssistFallback(this.mode[0], this.mode.slice(1));
        return this.assistFallback.apply(command);
    }
    async finishAssistProof() {
        await this.ensureAssistSessionCurrent();
        if (this.assistWorker) {
            try {
                return await this.assistWorker.qed(Core.timeout);
            }
            catch (workerError) {
                if (workerError?.operationError)
                    throw workerError;
                try {
                    await this.startAssistFallback(this.mode[0], this.mode.slice(1));
                    return this.assistFallback.qed();
                }
                catch (fallbackError) {
                    throw fallbackError ?? workerError;
                }
            }
        }
        await this.startAssistFallback(this.mode[0], this.mode.slice(1));
        return this.assistFallback.qed();
    }
    renderAssistSnapshot(snapshot) {
        this.assistSnapshot = snapshot;
        this.getHottTacticDefCtxt(this.getActiveTacticScopeId());
        this.renderTacticScopeOptions();
        const hint = document.getElementById("tactic-hint");
        const statediv = document.getElementById("tactic-state");
        hint.innerHTML = "";
        statediv.innerHTML = "";
        if (this.mode instanceof Array) {
            for (const command of this.mode.slice(1)) {
                this.addSpan(statediv, command + " . ").className = "blocked";
            }
        }
        this.updateTacticStateDisplay(snapshot, statediv);
        this.autofillTactics(snapshot.tactics);
        const holes = snapshot.goals.map(goal => [goal.holeName, goal.type, 0]);
        hint.appendChild(this.ast2HTML("", {
            type: ":",
            name: "",
            nodes: [snapshot.elem, snapshot.theorem]
        }, [], holes, this.getInhabitatArray().length));
        document.getElementById("tactic-remove").classList.remove("hide");
        document.getElementById("tactic-clear").classList.remove("hide");
        document.getElementById("copygate").classList.add("hide");
        const input = document.getElementById("tactic-input");
        input.classList.remove("hide");
        window.scrollTo(0, document.body.clientHeight);
        const wrapperDiv = document.getElementById("tactic-list").parentElement;
        wrapperDiv.scrollTo(0, document.getElementById("tactic-list").clientHeight);
    }
    formatTacticError(error) {
        return String(error).replace(/^Error:\s*/, "");
    }
    renderAstInScope(idx, ast, scopes = [], context = [], userLineNumber = 0, scopeFolderId = null) {
        const previousScope = this.astRenderScopeFolderId;
        this.astRenderScopeFolderId = scopeFolderId;
        try {
            return this.ast2HTML(idx, ast, scopes, context, userLineNumber);
        }
        finally {
            this.astRenderScopeFolderId = previousScope;
        }
    }
    addSpan(parentSpan, text, parseHTML) {
        const span = document.createElement("span");
        if (parseHTML)
            span.innerHTML = text;
        else
            span.innerText = text;
        parentSpan.appendChild(span);
        return span;
    }
    ast2HTML(idx, ast, scopes = [], context = [], userLineNumber = 0) {
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
            let el;
            if (ast.name.startsWith("@") && (isFinite(Number(ast.name.slice(1))) || ast.name === "@succ" || ast.name === "@max")) {
                el = this.addSpan(varnode, "<sub>" + ast.name + "</sub>", true);
                el.classList.add("universe");
            }
            else if (ast.name.startsWith("U@")) {
                el = this.addSpan(varnode, "U<sub>" + ast.name.slice(1) + "</sub>", true);
                el.classList.add("universe");
            }
            else {
                el = this.addSpan(varnode, ast.name);
            }
            if (debugBoundVarId && ast.bondVarId) {
                this.addSpan(el, "<sup>" + ast.bondVarId + "</sup>", true);
            }
            const scopeStack = scopes.slice(0);
            const astname = ast.name.replace(/'+$/g, "");
            if (astname.match(/^[1-9][0-9]*$/))
                el.classList.add("constructors");
            else if (computeEqs.has(astname))
                el.classList.add("compute_eqs");
            else if (destructors.has(astname))
                el.classList.add("ind_fn");
            else if (constructors.has(astname))
                el.classList.add("constructors");
            else if (consts.has(astname))
                el.classList.add("constant");
            else if (this.isKnownTheoremName(astname, userLineNumber))
                el.classList.add("macro");
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
            }
            else {
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
        }
        else {
            switch (ast.type) {
                case "[]":
                case "[[]]":
                    this.addSpan(varnode, ast.type === "[]" ? " |" : " ||");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    this.addSpan(varnode, ast.type === "[]" ? "| " : "|| ");
                    break;
                case ":":
                case ":=":
                case "===":
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    this.addSpan(varnode, " &nbsp;" + (ast.type === "===" ? "≡" : ast.type) + "&nbsp; ", true);
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    break;
                case "->":
                case "X":
                case "+":
                    const b1 = !(((ast.type === "+" || ast.type === "->") && ast.nodes[0].type === "X") || ["var", "=", "~=", "*"].includes(ast.nodes[0].type) || ast.nodes[0].nodes[0].name == "U");
                    const b2 = !(((ast.type === "+" || ast.type === "->") && ast.nodes[1].type === "X") || (["var", "->", "X"].includes(ast.nodes[1].type) && ast.type !== "X") || ["var"].includes(ast.nodes[1].type) || ast.nodes[1].nodes[0].name == "U");
                    if (b1)
                        this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    if (b1)
                        this.addSpan(varnode, ")");
                    this.addSpan(varnode, ast.type === "X" ? "×" : ast.type === "+" ? "+" : "→");
                    if (b2)
                        this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    if (b2)
                        this.addSpan(varnode, ")");
                    break;
                case ",":
                case "~":
                case "~=":
                case "=":
                case "*":
                    const bra = !["var", ",", "*", "[[]]", "[]", "~=", "="].includes(ast.nodes[0].type) && ast.type !== ",";
                    const brb = !["var", ",", "*", "[[]]", "[]", "~=", "="].includes(ast.nodes[1].type) && ast.type !== ",";
                    if (!(bra && brb))
                        this.addSpan(varnode, "(");
                    if (bra)
                        this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    if (bra)
                        this.addSpan(varnode, ")");
                    this.addSpan(varnode, ast.type === "," ? "," : ast.type === "~" ? " ~ " : ast.type === "~=" ? " ≃ " : ast.type === "*" ? "▪" : " = ");
                    if (brb)
                        this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    if (brb)
                        this.addSpan(varnode, ")");
                    if (!(bra && brb))
                        this.addSpan(varnode, ")");
                    break;
                case "apply":
                    if (ast.nodes[0].name === "U") {
                        const sub = parser.stringify(ast.nodes[1]);
                        this.addSpan(varnode, `U<sub>${sub.replaceAll(/@([0-9])/g, "$1")}</sub>`, true).classList.add("universe");
                        break;
                    }
                    const br1 = !["apply", "var", ",", "=", "*", "~=", "[[]]", "[]"].includes(ast.nodes[0].type);
                    const br2 = !(["var", ",", "*", "=", "~=", "[[]]", "[]"].includes(ast.nodes[1].type) || ast.nodes[1].nodes[0].name == "U");
                    if (br1)
                        this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[0], scopes, context, userLineNumber));
                    if (br1)
                        this.addSpan(varnode, ")");
                    this.addSpan(varnode, "&nbsp;", true);
                    if (br2)
                        this.addSpan(varnode, "(");
                    varnode.appendChild(this.ast2HTML(idx, ast.nodes[1], scopes, context, userLineNumber));
                    if (br2)
                        this.addSpan(varnode, ")");
                    break;
                case "L":
                case "P":
                case "S":
                case "W":
                    const outterLayers = [];
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
                    const constrainedVars = Array.from(varnode.querySelectorAll("span")).filter(node => node.getAttribute("ast-scope") === astStr);
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
        const spans = Array.from(varnode.childNodes).filter(node => !node.getAttribute("ast-string"));
        const floatTypeDiv = document.querySelector(".float-type");
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
                    ? this.theoremItems.find((item) => item.kind === "theorem" && item.id === renderedItemId)?.input
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
                            : this.renderAstInScope("Checked", ast.checked, scopes, localCtxt, userLineNumber, renderedScopeOverride);
                        floatTypeDiv.appendChild(checkedHtml);
                    }
                    catch (e) {
                        floatTypeDiv.innerText = e;
                    }
                }
                else if (ast.err) {
                    floatTypeDiv.appendChild(document.createTextNode(ast.err));
                }
                else {
                    floatTypeDiv.style.display = "none";
                    return;
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
    mouseoutTimeout;
    refreshUserConstNames() {
        this.userConstNames.clear();
        const inputs = this.getInhabitatArray();
        for (let i = 0; i < this.userDefinedConsts.length; i++) {
            const definition = this.userDefinedConsts[i];
            if (!definition || this.isTheoremInputDisabled(inputs[i]))
                continue;
            const item = this.getTheoremItemForInput(i);
            if (item?.localCheckbox.checked)
                continue;
            this.userConstNames.add(definition[0]);
        }
    }
    isKnownTheoremName(name, userLineNumber) {
        if (isKnownTheoremIdentifier(name, consts, sysmacro))
            return true;
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
        if (this.userDefinedConsts[definitionEnd]?.[0] === name)
            return true;
        if (this.findVisibleDefinitionIndex(name, definitionEnd, scopeId) >= 0)
            return true;
        // System declarations are always available. User definitions are
        // handled above so a name from another local folder stays visually
        // unknown instead of appearing as an available macro.
        return Object.prototype.hasOwnProperty.call(this.core.state.sysTypes ?? {}, name)
            || Object.prototype.hasOwnProperty.call(this.core.state.sysDefs ?? {}, name);
    }
    updateTypeList(terms) {
        const list = this.typeList;
        consts.clear();
        while (list.lastChild) {
            list.removeChild(list.lastChild);
        }
        const pendingDefinitions = new Map();
        const disableSimpleEq = this.disableSimpleEq;
        const disableSimpleFn = this.disableSimpleFn;
        for (const rule of allrules) {
            // register systype and sysdef in core
            const vname = rule.ast.nodes?.[0]?.name;
            if (rule.ast.type !== "===") {
                reservedConsts.add(vname);
            }
            if (!terms.has(rule.id))
                continue;
            this.core.state.disableSimpleEq = false;
            this.core.state.disableSimpleFn = false;
            if (rule.ast.type === ":" && rule.ast.nodes[0].type === "var") {
                if (this.unlockedTypes.has("// " + vname))
                    this.core.setSystemType(vname);
                else
                    this.core.setSystemType(vname, this.core.desugar(Core.clone(rule.ast.nodes[1]), true));
            }
            // ast.nodes[0].type==="var" -> skip a X b := @Prod _ _ ...
            if (rule.ast.type === ":=" && rule.ast.nodes[0].type === "var") {
                const val = rule.ast.nodes[1].type === ":" ? rule.ast.nodes[1].nodes[0] : rule.ast.nodes[1];
                if (this.unlockedTypes.has("// " + vname))
                    this.core.setSystemDefinition(vname);
                else
                    this.core.setSystemDefinition(vname, this.core.desugar(Core.clone(val), true));
            }
            if (this.unlockedTypes.has("// " + vname)) {
                this.core.clearDefinitionCache(vname);
                continue;
            }
            // register in gui highlight, only ignore ====
            if (rule.ast.type === "var" || ((rule.ast.type === ":=" || rule.ast.type === ":") && rule.ast.nodes[0].type === "var")) {
                const vname = rule.ast.type === "var" ? rule.ast.name : rule.ast.nodes[0].name;
                if (rule.postfix === "类型")
                    consts.add(vname);
                if (rule.postfix === "构造")
                    constructors.add(vname);
                if (rule.postfix === "解构")
                    destructors.add(vname);
                if (rule.postfix === "计算")
                    computeEqs.add(vname);
                if (rule.postfix === "定义")
                    sysmacro.add(vname);
            }
            if ((rule.inferMode === "@" && this.inferDisplayMode === "_") || (rule.inferMode === "_" && this.inferDisplayMode === "@")) {
                if (rule.ast.type === ":=") {
                    if (rule.ast.nodes[1].type === ":") {
                        this.core.setSystemType(vname, this.core.desugar(Core.clone(rule.ast.nodes[1].nodes[1]), true));
                    }
                    else {
                        try {
                            this.core.registerSystemDefinition(vname, rule.ast.nodes[1]);
                        }
                        catch {
                            pendingDefinitions.set(vname, Core.clone(rule.ast.nodes[1]));
                        }
                    }
                }
                continue;
            }
            // register in gui type list
            const itIdx = document.createElement("div");
            list.appendChild(itIdx);
            itIdx.classList.add("idx");
            itIdx.style.width = "30px";
            itIdx.innerText = TR(rule.postfix);
            const itVal = document.createElement("div");
            list.appendChild(itVal);
            itVal.classList.add("val");
            const ast = Core.clone(rule.ast);
            // avoid check const for redefined const error
            // const def = this.core.state.sysDefs[vname];
            // delete this.core.state.sysDefs[vname];
            let error = false;
            this.core.state.disableSimpleEq = disableSimpleEq;
            this.core.state.disableSimpleFn = disableSimpleFn;
            // Compute equations are trusted system rewrite rules. Rechecking
            // them on every list render can block startup on meta-heavy rules.
            if (ast.type !== "===") {
                try {
                    this.core.checkType(ast, [], false);
                }
                catch (e) {
                    console.log(e);
                    error = true;
                }
            }
            // this.core.state.sysDefs[vname] = def;
            if (ast.type === "var") {
                itVal.appendChild(this.ast2HTML("", { type: ":", nodes: [ast, ast.checked], name: "" }));
            }
            else {
                itVal.appendChild(this.ast2HTML("", ast));
            }
            if (ast.type === ":=") {
                const val = rule.ast.nodes[1].type === ":" ? rule.ast.nodes[1].nodes[0] : rule.ast.nodes[1];
                if (rule.ast.nodes[1].type === ":") {
                    this.core.setSystemType(vname, this.core.desugar(Core.clone(rule.ast.nodes[1].nodes[1]), true));
                }
                else if (!error) {
                    try {
                        this.core.registerSystemDefinition(vname, val);
                    }
                    catch {
                        pendingDefinitions.set(vname, Core.clone(val));
                    }
                }
            }
            const infoArr = [];
            for (let i = 0; i < 6; i++) {
                const itInfo = document.createElement("div");
                list.appendChild(itInfo);
                itInfo.className = "info";
                infoArr.push(itInfo);
                if (!i)
                    itInfo.innerText = rule.prefix;
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
                }
                catch { }
            }
            if (!progress)
                break;
        }
        this.core.elaborateSemanticSystemTypes();
        this.core.syncSemanticDefinitions?.();
    }
    createTheoremItemId(prefix) {
        const uuid = globalThis.crypto?.randomUUID?.();
        return prefix + "-" + (uuid ?? ++this.theoremItemSequence);
    }
    createTheoremDragHandle(wrapper, id) {
        wrapper.dataset.dragRow = "true";
        wrapper.dataset.dragId = id;
        const handle = document.createElement("button");
        handle.type = "button";
        handle.className = "inhabitat-modify tt-drag-handle idx";
        handle.innerText = "↕";
        handle.title = TR("拖动排序");
        wrapper.appendChild(handle);
        this.theoremDragger.attachIdxListener(handle);
        return handle;
    }
    insertTheoremItem(item, after) {
        if (!after) {
            this.theoremItems.push(item);
            return;
        }
        const afterId = after.dataset.dragId;
        const afterIndex = this.theoremItems.findIndex(entry => entry.id === afterId);
        if (afterIndex < 0) {
            this.theoremItems.push(item);
            return;
        }
        const scopes = this.scanTheoremFolderScope([afterId]).get(afterId) ?? [];
        for (const folder of scopes)
            folder.length++;
        this.theoremItems.splice(afterIndex + 1, 0, item);
    }
    syncTheoremDomOrder() {
        const addButton = document.getElementById("add-btn");
        let nextSibling = addButton;
        for (let i = this.theoremItems.length - 1; i >= 0; i--) {
            const wrapper = this.theoremItems[i].wrapper;
            if (wrapper.parentElement !== this.inhabitList || wrapper.nextSibling !== nextSibling) {
                this.inhabitList.insertBefore(wrapper, nextSibling);
            }
            nextSibling = wrapper;
        }
    }
    normalizeTheoremFolderLengths() {
        for (let i = 0; i < this.theoremItems.length; i++) {
            const item = this.theoremItems[i];
            if (item.kind !== "folder")
                continue;
            item.length = Math.max(0, Math.min(item.length, this.theoremItems.length - i - 1));
        }
    }
    scanTheoremFolderScope(targets) {
        const targetSet = new Set(targets.filter(Boolean));
        const stack = [];
        const result = new Map;
        for (let i = 0; i < this.theoremItems.length; i++) {
            while (stack.length && stack[stack.length - 1].end < i)
                stack.pop();
            const item = this.theoremItems[i];
            if (item.kind === "folder") {
                const length = Math.max(0, Math.min(item.length, this.theoremItems.length - i - 1));
                stack.push({ folder: item, end: i + length });
            }
            if (targetSet.has(item.id))
                result.set(item.id, stack.map(entry => entry.folder));
        }
        return result;
    }
    getTheoremItemForInput(input) {
        const target = typeof input === "number" ? this.getInhabitatArray()[input] : input;
        return this.theoremItems.find((item) => item.kind === "theorem" && item.input === target) ?? null;
    }
    getFolderScopeForFolder(folderId) {
        if (!folderId)
            return [];
        return this.scanTheoremFolderScope([folderId]).get(folderId) ?? [];
    }
    getAllTheoremFolders() {
        return this.theoremItems.filter((item) => item.kind === "folder");
    }
    getFolderPath(folderId) {
        return this.getFolderScopeForFolder(folderId).map(folder => folder.name).join(" / ");
    }
    getFolderScopeForInput(input, selectedFolderId) {
        const item = this.getTheoremItemForInput(input);
        if (!item)
            return [];
        const scopes = this.scanTheoremFolderScope([item.id]).get(item.id) ?? [];
        if (selectedFolderId && scopes.some(folder => folder.id === selectedFolderId)) {
            return this.getFolderScopeForFolder(selectedFolderId);
        }
        return scopes;
    }
    getDefaultTacticScope(input) {
        const scopes = input ? this.getFolderScopeForInput(input) : [];
        return scopes.length ? scopes[scopes.length - 1].id : null;
    }
    getDefinitionFolderId(index) {
        const item = this.getTheoremItemForInput(index);
        if (!item)
            return null;
        const scopes = this.scanTheoremFolderScope([item.id]).get(item.id) ?? [];
        return scopes.length ? scopes[scopes.length - 1].id : null;
    }
    findVisibleDefinitionIndex(name, targetIndex, selectedFolderId) {
        for (let index = Math.min(targetIndex - 1, this.userDefinedConsts.length - 1); index >= 0; index--) {
            if (this.userDefinedConsts[index]?.[0] !== name)
                continue;
            if (this.isDefinitionVisible(index, targetIndex, selectedFolderId))
                return index;
        }
        return -1;
    }
    hasDefinitionNameConflict(name, currentIndex, selectedFolderId) {
        const currentItem = this.getTheoremItemForInput(currentIndex);
        const currentFolderId = this.getDefinitionFolderId(currentIndex);
        const currentIsLocal = !!currentItem?.localCheckbox.checked && !!currentFolderId;
        for (let index = currentIndex - 1; index >= 0; index--) {
            if (this.userDefinedConsts[index]?.[0] !== name)
                continue;
            if (!this.isDefinitionVisible(index, currentIndex, selectedFolderId))
                continue;
            const previousFolderId = this.getDefinitionFolderId(index);
            // A nested local scope may shadow an ancestor's local helper. A
            // duplicate in the same folder, or any collision with a global
            // definition, remains an error.
            if (currentIsLocal && previousFolderId && previousFolderId !== currentFolderId)
                continue;
            return true;
        }
        return false;
    }
    isDefinitionInScope(index, selectedFolderId) {
        const inputs = this.getInhabitatArray();
        if (this.isTheoremInputDisabled(inputs[index]))
            return false;
        const definition = this.userDefinedConsts[index];
        if (!definition)
            return false;
        const item = this.getTheoremItemForInput(index);
        if (!item?.localCheckbox.checked)
            return true;
        const definitionFolderId = this.getDefinitionFolderId(index);
        if (!definitionFolderId)
            return true;
        if (!selectedFolderId)
            return false;
        return this.getFolderScopeForFolder(selectedFolderId).some(folder => folder.id === definitionFolderId);
    }
    isDefinitionVisible(index, targetIndex, selectedFolderId) {
        return index < targetIndex && this.isDefinitionInScope(index, selectedFolderId);
    }
    isTacticDefinitionVisible(index, selectedFolderId) {
        const targetIndex = this.getTacticDefinitionEnd();
        return index !== targetIndex && this.isDefinitionInScope(index, selectedFolderId);
    }
    clearUserDefinitionContext() {
        const names = new Set(Object.keys(this.core.state.userDefs));
        for (const definition of this.userDefinedConsts) {
            if (definition)
                names.add(definition[0]);
        }
        for (const name of names)
            delete this.core.state.defTypes[name];
        if (typeof this.core.clearUserDefinitions === "function")
            this.core.clearUserDefinitions();
        else
            this.core.state.userDefs = {};
    }
    addUserDefinitionToContext(name, definition) {
        if (typeof this.core.setUserDefinition === "function")
            this.core.setUserDefinition(name, definition[1]);
        else
            this.core.state.userDefs[name] = definition[1];
        if (definition[2])
            this.core.restoreDefinitionCache(name, definition[2]);
    }
    getActiveTacticScopeId() {
        const scopes = this.getTacticScopeOptions();
        if (this.tacticScopeExplicit) {
            if (this.tacticScopeFolderId === null)
                return null;
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
    getTacticDefinitionEnd() {
        const inputs = this.getInhabitatArray();
        const targetIndex = this.tacticTargetInput ? inputs.indexOf(this.tacticTargetInput) : -1;
        return targetIndex >= 0 ? targetIndex : inputs.length;
    }
    getTacticScopeOptions() {
        return this.tacticTargetInput
            ? this.getFolderScopeForInput(this.tacticTargetInput)
            : this.getAllTheoremFolders();
    }
    renderTacticScopeOptions() {
        const select = document.getElementById("tactic-scope");
        const label = document.getElementById("tactic-scope-label");
        if (!select || !label)
            return;
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
        }
        else {
            this.tacticScopeFolderId = previous && scopes.some(folder => folder.id === previous)
                ? previous
                : defaultScope;
        }
        select.value = this.tacticScopeFolderId ?? "";
        label.classList.toggle("hide", !(this.mode instanceof Array) || scopes.length === 0);
    }
    renderTheoremStructure() {
        if (!this.restoringTheoremItems)
            this.normalizeTheoremFolderLengths();
        this.syncTheoremDomOrder();
        const stack = [];
        for (let i = 0; i < this.theoremItems.length; i++) {
            while (stack.length && stack[stack.length - 1].end < i)
                stack.pop();
            const item = this.theoremItems[i];
            const hidden = stack.some(entry => !entry.open);
            const disabled = stack.some(entry => entry.disabled);
            item.wrapper.classList.toggle("hide", hidden);
            item.wrapper.classList.toggle("tt-folder-disabled", disabled || (item.kind === "folder" && item.disabled));
            item.wrapper.style.setProperty("--tt-folder-depth", String(stack.length));
            if (item.kind === "theorem") {
                const canBeLocal = stack.length > 0;
                item.input.dataset.ttDisabled = String(disabled);
                item.wrapper.classList.toggle("tt-theorem-disabled", disabled);
                item.localCheckbox.disabled = !canBeLocal;
                if (!canBeLocal)
                    item.localCheckbox.checked = false;
                item.localCheckbox.title = TR(canBeLocal
                    ? "局部常量仅在所在文件夹及子文件夹中可见"
                    : "局部常量需放在文件夹中");
                item.localCheckbox.parentElement.title = item.localCheckbox.title;
                continue;
            }
            const folderLength = Math.max(0, Math.min(item.length, this.theoremItems.length - i - 1));
            item.title.innerText = item.name;
            item.title.classList.toggle("dir-open", item.open);
            item.title.classList.toggle("dir-close", !item.open);
            item.wrapper.dataset.dragFolderOpen = String(item.open);
            item.checkbox.checked = item.disabled;
            stack.push({ end: i + folderLength, open: item.open, disabled: disabled || item.disabled });
        }
    }
    isTheoremInputDisabled(input) {
        return input?.dataset.ttDisabled === "true";
    }
    invalidateTheoremTypeTags(startIndex = 0) {
        const inputs = this.getInhabitatArray();
        for (let i = Math.max(0, startIndex); i < inputs.length; i++) {
            const input = inputs[i];
            delete input["validatedType"];
            delete input.dataset.validatedTypeKey;
        }
        this.gateQueryCache.clear();
    }
    setTheoremTypeTag(input, ast) {
        if (!ast?.checked)
            return;
        const checked = Core.clone(ast.checked, true);
        input["validatedType"] = checked;
        input.dataset.validatedTypeKey = parser.stringify(checked);
        delete input["validationInvalidated"];
        this.gateQueryCache.clear();
    }
    suspendTheoremTypeTag(input) {
        input["editingValidatedType"] = input["validatedType"];
        input["editingValidatedTypeKey"] = input.dataset.validatedTypeKey;
        delete input["validatedType"];
        delete input.dataset.validatedTypeKey;
        this.gateQueryCache.clear();
    }
    restoreSuspendedTheoremTypeTag(input) {
        const checked = input["editingValidatedType"];
        const key = input["editingValidatedTypeKey"];
        if (checked)
            input["validatedType"] = checked;
        if (key)
            input.dataset.validatedTypeKey = key;
        delete input["editingValidatedType"];
        delete input["editingValidatedTypeKey"];
        this.gateQueryCache.clear();
    }
    discardSuspendedTheoremTypeTag(input) {
        delete input["editingValidatedType"];
        delete input["editingValidatedTypeKey"];
    }
    invalidateTheoremChecks(startIndex = 0, resetWorker = false) {
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
    revalidateTheorems(startIndex = 0) {
        const inputs = this.getInhabitatArray();
        const earliestChecking = inputs.findIndex(input => input.parentElement?.classList.contains("checking"));
        const effectiveStart = Math.min(Math.max(0, startIndex), ...(earliestChecking >= 0 ? [earliestChecking] : []));
        const run = this.theoremValidation.request(effectiveStart);
        this.invalidateTheoremChecks(effectiveStart, true);
        if (!run)
            return;
        const first = this.getInhabitatArray()[effectiveStart];
        if (first)
            first.onblur({ updateDefs: true, validationRunId: run.id });
        else
            this.completeTheoremValidation(run.id);
    }
    resetCoreWorkerSession() {
        if (!this.coreWorker)
            return;
        this.coreWorker.reset();
        this.coreWorkerGeneration = -1;
        this.coreWorkerConfigKey = "";
        this.coreWorkerConfigurePromise = null;
    }
    completeTheoremValidation(runId) {
        const next = this.theoremValidation.complete(runId);
        if (!next)
            return;
        this.invalidateTheoremChecks(next.startIndex, true);
        const first = this.getInhabitatArray()[next.startIndex];
        if (first)
            first.onblur({ updateDefs: true, validationRunId: next.id });
        else
            this.completeTheoremValidation(next.id);
    }
    theoremInputIndexAtItem(item) {
        return theoremInputIndexBeforeItem(this.theoremItems, this.theoremItems.indexOf(item));
    }
    getFolderTheoremRange(folder) {
        const folderIndex = this.theoremItems.indexOf(folder);
        if (folderIndex < 0)
            return null;
        const subtreeEnd = Math.min(this.theoremItems.length, folderIndex + Math.max(0, folder.length) + 1);
        return {
            startIndex: theoremInputIndexBeforeItem(this.theoremItems, folderIndex),
            endIndex: theoremInputIndexBeforeItem(this.theoremItems, subtreeEnd)
        };
    }
    realignUserDefinitions(previousInputs, previousDefinitions) {
        const byInput = new Map();
        previousInputs.forEach((input, index) => byInput.set(input, previousDefinitions[index]));
        this.userDefinedConsts = this.getInhabitatArray().map(input => byInput.get(input) ?? null);
        this.refreshUserConstNames();
    }
    moveTheoremItem(srcId, dstId) {
        if (!srcId)
            return;
        // Clamp malformed folder lengths before slicing a subtree.
        this.renderTheoremStructure();
        const srcIndex = this.theoremItems.findIndex(item => item.id === srcId);
        if (srcIndex < 0)
            return;
        const source = this.theoremItems[srcIndex];
        const movedCount = source.kind === "folder" ? source.length + 1 : 1;
        const samePosition = srcId === dstId;
        const moving = this.theoremItems.slice(srcIndex, srcIndex + movedCount);
        const insideFolderId = dstId.startsWith("inside:") ? dstId.slice("inside:".length) : null;
        const insideFolder = insideFolderId
            ? this.theoremItems.find(item => item.id === insideFolderId && item.kind === "folder")
            : null;
        if (insideFolderId && !insideFolder)
            return;
        if (insideFolder && !insideFolder.open)
            return;
        if (!samePosition && moving.some(item => item.id === (insideFolderId ?? dstId)))
            return;
        const dstIndex = insideFolder
            ? this.theoremItems.indexOf(insideFolder)
            : dstId === " " ? -1 : this.theoremItems.findIndex(item => item.id === dstId);
        if (dstIndex < 0 && dstId !== " ")
            return;
        const previousDestination = dstIndex < 0
            ? this.theoremItems[this.theoremItems.length - 1]
            : this.theoremItems[dstIndex - 1];
        if (!insideFolder && previousDestination && moving.some(item => item.id === previousDestination.id))
            return;
        const scopeTargets = [srcId, insideFolderId, previousDestination?.id].filter(Boolean);
        const scopes = this.scanTheoremFolderScope(scopeTargets);
        for (const folder of scopes.get(srcId) ?? []) {
            if (folder.id !== srcId)
                folder.length = Math.max(0, folder.length - movedCount);
        }
        if (insideFolder) {
            for (const folder of scopes.get(insideFolder.id) ?? [])
                folder.length += movedCount;
        }
        else {
            for (const folder of scopes.get(previousDestination?.id) ?? []) {
                if (!folder.open)
                    break;
                folder.length += movedCount;
            }
        }
        const previousInputs = this.getInhabitatArray();
        const previousDefinitions = this.userDefinedConsts.slice();
        const movingInputs = moving
            .filter((item) => item.kind === "theorem")
            .map(item => item.input);
        const previousTheoremPositions = movingInputs.map(input => previousInputs.indexOf(input)).filter(index => index >= 0);
        if (!samePosition) {
            this.theoremItems.splice(srcIndex, movedCount);
            const insertIndex = insideFolder
                ? this.theoremItems.findIndex(item => item.id === insideFolder.id) + 1
                : dstId === " "
                    ? this.theoremItems.length
                    : this.theoremItems.findIndex(item => item.id === dstId);
            this.theoremItems.splice(insertIndex < 0 ? this.theoremItems.length : insertIndex, 0, ...moving);
            this.syncTheoremDomOrder();
            this.realignUserDefinitions(previousInputs, previousDefinitions);
        }
        this.definitionRevision++;
        this.theoremStructureRevision++;
        this.gatePreviewStructureRevision = -1;
        this.renderTheoremStructure();
        this.onStateChange();
        if (movingInputs.length) {
            const nextInputs = this.getInhabitatArray();
            const nextTheoremPositions = movingInputs.map(input => nextInputs.indexOf(input)).filter(index => index >= 0);
            const earliestChecking = nextInputs.findIndex(input => input.parentElement?.classList.contains("checking"));
            const revalidateFrom = Math.min(...previousTheoremPositions, ...nextTheoremPositions, ...(earliestChecking >= 0 ? [earliestChecking] : []));
            this.revalidateTheorems(Number.isFinite(revalidateFrom) ? revalidateFrom : 0);
        }
    }
    addTheoremFolder(name, saved, silent = false) {
        if (name === undefined)
            name = prompt(TR("文件夹名称："), TR("新文件夹"))?.trim();
        if (!name)
            return;
        const id = saved?.id || this.createTheoremItemId("folder");
        const wrapper = document.createElement("div");
        wrapper.className = "wrapper tt-folder-row";
        wrapper.dataset.dragFolder = "true";
        this.createTheoremDragHandle(wrapper, id);
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
        const folder = {
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
            folder.open = !folder.open;
            this.renderTheoremStructure();
            this.onStateChange();
        });
        checkbox.addEventListener("change", () => {
            const theoremRange = this.getFolderTheoremRange(folder);
            folder.disabled = checkbox.checked;
            this.definitionRevision++;
            this.theoremStructureRevision++;
            this.gatePreviewStructureRevision = -1;
            this.renderTheoremStructure();
            this.onStateChange();
            // An empty folder changes no theorem visibility. In particular, a
            // newly created folder at the top must not restart the complete
            // validation chain merely because its checkbox changed.
            if (theoremRange && theoremRange.endIndex > theoremRange.startIndex) {
                this.revalidateTheorems(theoremRange.startIndex);
            }
        });
        addTheorem.addEventListener("click", () => {
            if (!folder.open)
                folder.open = true;
            this.renderTheoremStructure();
            this.updateInhabitList(undefined, folder);
        });
        rename.addEventListener("click", () => {
            const nextName = prompt(TR("文件夹名称："), folder.name)?.trim();
            if (!nextName)
                return;
            folder.name = nextName;
            this.renderTheoremStructure();
            this.onStateChange();
        });
        remove.addEventListener("click", () => {
            if (!confirm(TR("删除文件夹后，里面的定理会移动到上一级。确定继续吗？")))
                return;
            const index = this.theoremItems.indexOf(folder);
            const revalidateFrom = this.theoremInputIndexAtItem(folder);
            const scopes = this.scanTheoremFolderScope([folder.id]).get(folder.id) ?? [];
            for (const parent of scopes) {
                if (parent.id !== folder.id)
                    parent.length = Math.max(0, parent.length - 1);
            }
            if (index >= 0)
                this.theoremItems.splice(index, 1);
            wrapper.remove();
            this.definitionRevision++;
            this.theoremStructureRevision++;
            this.gatePreviewStructureRevision = -1;
            this.renderTheoremStructure();
            this.onStateChange();
            this.revalidateTheorems(revalidateFrom);
        });
        this.theoremItems.push(folder);
        this.renderTheoremStructure();
        if (!silent)
            this.onStateChange();
        return folder;
    }
    serializeTheoremItems() {
        this.normalizeTheoremFolderLengths();
        return this.theoremItems.map(item => item.kind === "theorem"
            ? { kind: "theorem", value: item.input.value, local: item.localCheckbox.checked }
            : {
                kind: "folder",
                id: item.id,
                name: item.name,
                length: item.length,
                open: item.open,
                disabled: item.disabled
            });
    }
    restoreTheoremItems(items) {
        this.definitionRevision++;
        this.theoremStructureRevision++;
        this.gatePreviewStructureRevision = -1;
        // Drop caches belonging to the previous theorem list before replacing
        // it. They are keyed by name and otherwise survive a save restore.
        for (const definition of this.userDefinedConsts) {
            if (definition)
                delete this.core.state.defTypes[definition[0]];
        }
        for (const item of this.theoremItems)
            item.wrapper.remove();
        this.theoremItems = [];
        this.userDefinedConsts = [];
        this.refreshUserConstNames();
        this.gateQueryCache.clear();
        this.restoringTheoremItems = true;
        try {
            for (const item of items) {
                if (item.kind === "folder") {
                    this.addTheoremFolder(item.name, item, true);
                }
                else {
                    this.updateInhabitList();
                    const theorem = this.theoremItems[this.theoremItems.length - 1];
                    if (theorem?.kind === "theorem") {
                        theorem.input.value = String(item.value ?? "");
                        theorem.localCheckbox.checked = !!item.local;
                    }
                }
            }
        }
        finally {
            this.restoringTheoremItems = false;
        }
        this.theoremItems.forEach((item, index) => {
            if (item.kind === "folder") {
                item.length = Math.max(0, Math.min(item.length, this.theoremItems.length - index - 1));
            }
        });
        this.renderTheoremStructure();
        if (!this.skipRendering)
            this.revalidateTheorems();
    }
    getHottDefCtxt(input, selectedFolderId = null) {
        macro.clear();
        for (const s of sysmacro)
            macro.add(s);
        this.clearUserDefinitionContext();
        const inputs = this.getInhabitatArray();
        const currentIdx = typeof input === "number" ? input : inputs.indexOf(input);
        const end = typeof input === "number" ? Math.min(inputs.length - 1, input) : currentIdx - 1;
        const scopeId = selectedFolderId ?? (typeof input === "number"
            ? this.getActiveTacticScopeId()
            : this.getDefaultTacticScope(input));
        for (let i = 0; i <= end; i++) {
            const def = this.userDefinedConsts[i];
            if (!def || !this.isDefinitionVisible(i, currentIdx + (typeof input === "number" ? 0 : 1), scopeId))
                continue;
            macro.add(def[0]);
            this.addUserDefinitionToContext(def[0], def);
        }
        return currentIdx;
    }
    getHottTacticDefCtxt(selectedFolderId) {
        macro.clear();
        for (const s of sysmacro)
            macro.add(s);
        this.clearUserDefinitionContext();
        for (let i = 0; i < this.getInhabitatArray().length; i++) {
            const definition = this.userDefinedConsts[i];
            if (!definition || !this.isTacticDefinitionVisible(i, selectedFolderId))
                continue;
            macro.add(definition[0]);
            this.addUserDefinitionToContext(definition[0], definition);
        }
    }
    getWorkerSystemConfig() {
        return {
            unlockedTypes: Array.from(this.unlockedTypes),
            disableSimpleFn: this.disableSimpleFn,
            disableSimpleEq: this.disableSimpleEq,
            inferDisplayMode: this.inferDisplayMode,
            timeout: Core.timeout,
            language: langMgr.lang,
        };
    }
    getWorkerDefinitionSlots(definitionEnd, scopeFolderId = null) {
        const definitions = [];
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
    getTacticWorkerDefinitionSlots(scopeFolderId = null) {
        const definitions = [];
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
    getWorkerConfig(definitionEnd, scopeFolderId = null) {
        const definitions = this.getWorkerDefinitionSlots(definitionEnd, scopeFolderId);
        return {
            ...this.getWorkerSystemConfig(),
            userDefinitions: definitions.filter(Boolean).map(definition => [definition[0], definition[1]]),
            userDefinitionCaches: definitions.filter(definition => definition?.[2]).map(definition => [definition[0], definition[2]])
        };
    }
    getTacticWorkerConfig(scopeFolderId = null) {
        const definitions = this.getTacticWorkerDefinitionSlots(scopeFolderId);
        return {
            ...this.getWorkerSystemConfig(),
            userDefinitions: definitions.filter(Boolean).map(definition => [definition[0], definition[1]]),
            userDefinitionCaches: definitions.filter(definition => definition?.[2]).map(definition => [definition[0], definition[2]])
        };
    }
    prepareCoreWorker(definitionEnd, scopeFolderId = null) {
        if (!this.coreWorker)
            return Promise.reject(new Error("Type-theory worker unavailable"));
        const config = this.getWorkerSystemConfig();
        const configKey = JSON.stringify({ config, definitionEnd, scopeFolderId });
        const generation = this.coreWorker.generation;
        if (this.coreWorkerGeneration === generation && this.coreWorkerConfigKey === configKey) {
            return this.coreWorkerMutations.wait();
        }
        this.coreWorkerGeneration = generation;
        this.coreWorkerConfigKey = configKey;
        const definitions = this.getWorkerDefinitionSlots(definitionEnd, scopeFolderId);
        const promise = this.coreWorkerMutations.enqueue(() => this.coreWorker.configure(config, definitions));
        this.prepareAssistWorker(definitionEnd, config, definitions, scopeFolderId).catch(() => { });
        this.coreWorkerConfigurePromise = promise.catch(error => {
            if (this.coreWorkerGeneration === generation && this.coreWorkerConfigKey === configKey) {
                this.coreWorkerGeneration = -1;
                this.coreWorkerConfigKey = "";
                this.coreWorkerConfigurePromise = null;
            }
            throw error;
        });
        return this.coreWorkerConfigurePromise;
    }
    prepareAssistWorker(definitionEnd, config = this.getWorkerSystemConfig(), definitions, scopeFolderId = null, definitionMode = "ordered") {
        if (!this.assistWorker)
            return Promise.reject(new Error("Proof-assistant worker unavailable"));
        const configKey = JSON.stringify({ config, definitionEnd, scopeFolderId, definitionMode });
        const generation = this.assistWorker.generation;
        if (this.assistWorkerGeneration === generation && this.assistWorkerConfigKey === configKey) {
            return this.assistWorkerMutations.wait();
        }
        this.assistWorkerGeneration = generation;
        this.assistWorkerConfigKey = configKey;
        this.assistWorkerSessionReady = false;
        const configuredDefinitions = definitions ?? this.getWorkerDefinitionSlots(definitionEnd, scopeFolderId);
        const promise = this.assistWorkerMutations.enqueue(() => this.assistWorker.configure(config, configuredDefinitions));
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
    invalidateWorkerDefinitions(startIndex) {
        this.definitionRevision++;
        if (this.coreWorker) {
            const generation = this.coreWorker.generation;
            this.coreWorkerMutations.enqueue(() => this.coreWorker.truncate(startIndex)).catch(() => {
                if (this.coreWorker.generation !== generation)
                    return;
                this.coreWorkerGeneration = -1;
                this.coreWorkerConfigKey = "";
                this.coreWorkerConfigurePromise = null;
            });
        }
        if (this.assistWorker && this.assistWorkerGeneration === this.assistWorker.generation && this.assistWorkerConfigKey) {
            this.assistWorkerSessionReady = false;
            const generation = this.assistWorker.generation;
            this.assistWorkerMutations.enqueue(() => this.assistWorker.truncate(startIndex)).catch(() => {
                if (this.assistWorker.generation !== generation)
                    return;
                this.assistWorkerGeneration = -1;
                this.assistWorkerConfigKey = "";
                this.assistWorkerConfigurePromise = null;
            });
        }
    }
    syncCoreWorkerDefinition(index, definition) {
        if (!this.coreWorker || this.coreWorkerGeneration !== this.coreWorker.generation || !this.coreWorkerConfigKey)
            return;
        const generation = this.coreWorker.generation;
        this.coreWorkerMutations.enqueue(() => this.coreWorker.setDefinition(index, definition)).catch(() => {
            if (this.coreWorker.generation !== generation)
                return;
            this.coreWorkerGeneration = -1;
            this.coreWorkerConfigKey = "";
            this.coreWorkerConfigurePromise = null;
        });
    }
    syncAssistWorkerDefinition(index, definition) {
        if (!this.assistWorker || this.assistWorkerGeneration !== this.assistWorker.generation || !this.assistWorkerConfigKey)
            return;
        this.assistWorkerSessionReady = false;
        const generation = this.assistWorker.generation;
        this.assistWorkerMutations.enqueue(() => this.assistWorker.setDefinition(index, definition)).catch(() => {
            if (this.assistWorker.generation !== generation)
                return;
            this.assistWorkerGeneration = -1;
            this.assistWorkerConfigKey = "";
            this.assistWorkerConfigurePromise = null;
        });
    }
    updateInhabitList(insertPos, destinationFolder) {
        // Inserting a row shifts every later theorem index.  Cancel any
        // in-flight checks in that suffix before changing the arrays; otherwise
        // an old Worker response can write its result into the new row's slot.
        let insertionItemIndex = this.theoremItems.length;
        if (destinationFolder) {
            insertionItemIndex = this.getFolderAppendIndex(destinationFolder);
        }
        else if (insertPos) {
            const afterIndex = this.theoremItems.findIndex(item => item.wrapper === insertPos);
            if (afterIndex >= 0)
                insertionItemIndex = afterIndex + 1;
        }
        if (insertionItemIndex < 0)
            insertionItemIndex = this.theoremItems.length;
        const previousInputs = this.getInhabitatArray();
        const insertionInputIndex = theoremInputIndexBeforeItem(this.theoremItems, insertionItemIndex);
        const hasShiftedSuffix = insertionInputIndex < previousInputs.length;
        if (hasShiftedSuffix)
            this.invalidateTheoremChecks(insertionInputIndex, true);
        this.definitionRevision++;
        this.theoremStructureRevision++;
        this.gatePreviewStructureRevision = -1;
        // A generated proof can be thousands of characters long.  Keep the
        // editor single-line in interaction semantics, but use a textarea so
        // the value can wrap and grow instead of creating horizontal scroll.
        const input = document.createElement("textarea");
        input.rows = 1;
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
            const textarea = input;
            textarea.style.height = "auto";
            // Adding height can make the surrounding list gain a scrollbar,
            // narrowing the textarea and creating additional wrapped lines.
            // Re-measure until the layout settles so the final lines are not
            // clipped by `overflow: hidden`.
            for (let pass = 0; pass < 3; pass++) {
                const nextHeight = Math.max(textarea.scrollHeight, 21);
                const borderHeight = Math.max(0, textarea.offsetHeight - textarea.clientHeight);
                if (textarea.clientHeight >= nextHeight)
                    break;
                textarea.style.height = `${nextHeight + borderHeight}px`;
            }
        };
        input.addEventListener("compositionstart", () => composing = true);
        input.addEventListener("compositionend", () => composing = false);
        input.addEventListener("keydown", ev => {
            if (composing || ev.isComposing || ev.keyCode === 229)
                return;
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
            if (!input["validationInvalidated"]) {
                const currentIdx = this.getInhabitatArray().indexOf(input);
                if (currentIdx >= 0)
                    this.invalidateTheoremChecks(currentIdx);
                input["validationInvalidated"] = true;
            }
            const originalValue = input["editingOriginalValue"];
            if (originalValue?.includes(":=") || input.value.includes(":="))
                input["needUpdate"] = true;
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
                if (validationRunId !== null)
                    this.completeTheoremValidation(validationRunId);
                return;
            }
            if (!programmatic)
                input["editing"] = false;
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
            if (!ev["updateDefs"])
                ev["updateDefs"] = input["needUpdate"];
            delete input["needUpdate"];
            this.onStateChange();
            const currentIdx = this.getHottDefCtxt(input);
            const validationItemId = this.getTheoremItemForInput(input)?.id ?? null;
            const rowPositionMatches = () => theoremValidationPositionMatches(this.getInhabitatArray(), input, currentIdx, validationItemId, currentInput => this.getTheoremItemForInput(currentInput)?.id ?? null);
            if (ev["updateDefs"])
                this.invalidateWorkerDefinitions(currentIdx);
            this.invalidateTheoremTypeTags(currentIdx);
            input["validationInvalidated"] = true;
            const inputsarr = this.getInhabitatArray();
            const nextInput = inputsarr[currentIdx + 1];
            const continueValidation = (shouldContinue) => {
                if (validationRunId !== null && !this.theoremValidation.isCurrent(validationRunId)) {
                    this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (shouldContinue && nextInput?.isConnected) {
                    const nextEvent = { updateDefs: true };
                    if (validationRunId !== null)
                        nextEvent.validationRunId = validationRunId;
                    nextInput.onblur(nextEvent);
                }
                else if (validationRunId !== null) {
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
                    if (validationRunId !== null)
                        this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (current >= 0)
                    this.invalidateTheoremChecks(current, true);
                this.definitionRevision++;
                this.theoremStructureRevision++;
                this.gatePreviewStructureRevision = -1;
                const [removed] = this.userDefinedConsts.splice(current, 1);
                const itemIndex = this.theoremItems.findIndex(item => item.kind === "theorem" && item.input === input);
                if (itemIndex >= 0) {
                    const item = this.theoremItems[itemIndex];
                    const scopes = this.scanTheoremFolderScope([item.id]).get(item.id) ?? [];
                    for (const folder of scopes)
                        folder.length = Math.max(0, folder.length - 1);
                    this.theoremItems.splice(itemIndex, 1);
                }
                this.refreshUserConstNames();
                try {
                    wrapper.remove();
                }
                catch (e) { }
                if (removed)
                    macro.delete(removed[0]);
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
            let ast;
            let parseError = "";
            let error = "";
            try {
                ast = parser.parse(input.value);
            }
            catch (e) {
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
            const checkInfer = (ast, trustValidatedHoles = false) => {
                const _checkInfer = (ast, context, expandConsts, checkType) => {
                    // if (checkType && ast.checked && !_checkInfer(ast.checked, context, expandConsts, false)) return false;
                    if (ast.type === "var") {
                        if (ast.name[0] === "?" || ast.name === "_") {
                            if (trustValidatedHoles)
                                return true;
                            if (!ast.checked)
                                return false;
                            // ast.checked can be ttt or xxx : ttt
                            const t = ast.checked.type === ":" ? ast.checked.nodes[1] : ast.checked;
                            if (t.name === "U@")
                                return true;
                            if (t.type === "apply" && t.nodes[0].name === "U")
                                return true;
                            // if ttt is not Universe or level number, we check xxx recursively
                            return ast.checked.type === ":" ? _checkInfer(ast.checked.nodes[0], context, expandConsts, checkType) : false;
                        }
                        if (!context.find(e => e[0] === ast.name)) {
                            // if this is a constant, check its value recursively
                            const pos = this.findVisibleDefinitionIndex(ast.name, currentIdx, this.getDefaultTacticScope(input));
                            if (pos >= 0 && inputsarr[pos]?.parentElement?.classList.contains("infering")) {
                                expandConsts.add(ast.name);
                            }
                        }
                    }
                    if (ast.nodes) {
                        if (ast.type === "apply" && ast.nodes[0].name === "U" && ast.nodes[0].type === "var")
                            return true;
                        if (!_checkInfer(ast.nodes[0], context, expandConsts, checkType))
                            return false;
                        if (ast.type === "P" || ast.type === "L" || ast.type === "W" || ast.type === "S") {
                            context = assignContext([ast.name, ast.nodes[0], 0], context);
                        }
                        if (ast.nodes[1] && !_checkInfer(ast.nodes[1], context, expandConsts, checkType))
                            return false;
                    }
                    return true;
                };
                let nast = ast;
                let expandConsts = new Set;
                while (true) {
                    if (!_checkInfer(nast, [], expandConsts, true)) {
                        wrapper.classList.add("infering");
                        return;
                    }
                    if (!expandConsts.size)
                        return;
                    if (nast === ast) {
                        nast = Core.clone(ast);
                    }
                    this.core.expandDef(nast, [], expandConsts);
                    this.core.checkType(nast, [], false);
                    expandConsts = new Set;
                }
            };
            const clearBondId = (value) => {
                value.bondVarId = null;
                if (value.nodes)
                    for (const node of value.nodes)
                        clearBondId(node);
                if (value.checked)
                    clearBondId(value.checked);
                return value;
            };
            const finish = (checkedAst, validationError = "", filledDefinition, definitionCache, workerCommitted = false, continueAfter = true, inferenceComplete) => {
                if (validationRunId !== null && !this.theoremValidation.isCurrent(validationRunId)) {
                    this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (input["workerRequestId"] !== requestId || !input.isConnected) {
                    if (validationRunId !== null)
                        this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (!rowPositionMatches()) {
                    // The row moved while the Worker was checking it.  Its
                    // old index is no longer safe for definition/cache writes;
                    // the structural mutation will schedule a fresh suffix
                    // validation using the new position.
                    if (validationRunId !== null)
                        this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (checkedAst)
                    ast = checkedAst;
                error = validationError;
                wrapper.classList.remove("checking");
                if (Core.timeoutOccured)
                    document.getElementById("timeout").classList.remove("hide");
                if (ast && !error) {
                    try {
                        if (ast.type === ":=") {
                            const defname = ast.nodes[0].name;
                            const defContent = ast.nodes[1];
                            if (!filledDefinition)
                                throw TR("类型检查未返回定义结果");
                            const filledAst = clearBondId(Core.clone(filledDefinition));
                            let storedDefinition;
                            if (defContent.type === ":") {
                                storedDefinition = this.core.desugar(Core.clone(filledAst.nodes[0]), true);
                            }
                            else {
                                storedDefinition = this.core.desugar(Core.clone(filledAst), true);
                            }
                            if (definitionCache)
                                this.core.restoreDefinitionCache(defname, definitionCache);
                            let storedCache = definitionCache
                                ?? this.core.serializeDefinitionCache(defname);
                            if (!storedCache) {
                                // Compatibility with an older/stale Worker
                                // response that validated the definition but
                                // omitted its transferable type cache. Without
                                // this repair the name remains visible while
                                // every semantic use reports unknown-constant.
                                try {
                                    const recovered = this.core.checkDefinition(Core.clone(ast, true), []);
                                    storedCache = recovered.definitionCache;
                                    this.core.restoreDefinitionCache(defname, storedCache);
                                }
                                catch { }
                            }
                            this.userDefinedConsts[currentIdx] = [defname, storedDefinition, storedCache];
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
                            if (!workerCommitted) {
                                this.syncCoreWorkerDefinition(currentIdx, [defname, storedDefinition, storedCache]);
                            }
                            this.syncAssistWorkerDefinition(currentIdx, [defname, storedDefinition, storedCache]);
                            macro.add(defname);
                        }
                        // The Worker returns a fully elaborated definition while
                        // `ast` deliberately preserves the user's `_` spelling
                        // for display.  Re-running the legacy inference probe on
                        // that surface AST both marks solved holes as pending and
                        // can throw after expanding an earlier such definition.
                        const inferenceTarget = theoremInferenceTarget(ast, filledDefinition);
                        const inferenceStatus = theoremInferenceStatus(inferenceComplete);
                        if (inferenceStatus === "incomplete") {
                            wrapper.classList.add("infering");
                        }
                        else {
                            const trustValidatedHoles = inferenceStatus === "complete";
                            checkInfer(inferenceTarget, trustValidatedHoles);
                            if (inferenceTarget.type === ":") {
                                checkInfer(inferenceTarget.nodes[1], trustValidatedHoles);
                            }
                        }
                    }
                    catch (e) {
                        error += e;
                        wrapper.classList.add("error");
                    }
                }
                wrapper.classList.toggle("error", !!error || !!parseError);
                if (ast && !error && !parseError && !wrapper.classList.contains("infering")) {
                    this.setTheoremTypeTag(input, ast);
                }
                const newDom = parseError ? this.addSpan(div, input.value + " - " + parseError) : this.ast2HTML("", ast, [], [], currentIdx);
                div.appendChild(newDom);
                if (ast && error)
                    this.addSpan(div, " - " + error);
                if (ast && !error && ast.type[0] != ":") {
                    this.addSpan(div, " &nbsp; : &nbsp; ", true);
                    div.appendChild(this.ast2HTML("", ast.checked, [], [], currentIdx));
                }
                continueValidation(continueAfter && !!nextInput && (ast?.type === ":=" || !!ev["updateDefs"]));
            };
            const validateSynchronously = () => {
                try {
                    let filledDefinition;
                    if (ast.type === ":=") {
                        if (ast.nodes[0].type !== "var")
                            throw TR(":=符号左侧仅允许出现自定义常量");
                        const defname = ast.nodes[0].name;
                        if (this.hasDefinitionNameConflict(defname, currentIdx, this.getDefaultTacticScope(input))) {
                            throw defname + TR("的定义重复");
                        }
                        if (reservedConsts.has(defname))
                            throw defname + TR("由系统保留");
                        const checkedDefinition = this.core.checkDefinition(ast, []);
                        filledDefinition = checkedDefinition.filledDefinition;
                        this.core.restoreDefinitionCache(defname, checkedDefinition.definitionCache);
                    }
                    else {
                        this.core.checkType(ast, [], false);
                    }
                    const inferenceTarget = theoremInferenceTarget(ast, filledDefinition);
                    const inferenceComplete = theoremInferenceComplete(inferenceTarget);
                    finish(ast, "", filledDefinition, undefined, false, true, inferenceComplete);
                }
                catch (e) {
                    finish(ast, String(e));
                }
            };
            if (!ast) {
                finish(ast, parseError);
                return;
            }
            if (ast.type === ":=") {
                try {
                    if (ast.nodes[0].type !== "var")
                        throw TR(":=符号左侧仅允许出现自定义常量");
                    const defname = ast.nodes[0].name;
                    if (this.hasDefinitionNameConflict(defname, currentIdx, this.getDefaultTacticScope(input))) {
                        throw defname + TR("的定义重复");
                    }
                    if (reservedConsts.has(defname))
                        throw defname + TR("由系统保留");
                }
                catch (e) {
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
                    if (validationRunId !== null)
                        this.completeTheoremValidation(validationRunId);
                    return null;
                }
                return this.coreWorker.validate(currentIdx, Core.clone(ast, true), [], Core.timeout);
            }).then(result => {
                if (!result)
                    return;
                if (input["workerRequestId"] !== requestId || input.value !== inputValue || !input.isConnected) {
                    if (validationRunId !== null)
                        this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (!rowPositionMatches()) {
                    if (validationRunId !== null)
                        this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (result.timeout)
                    document.getElementById("timeout").classList.remove("hide");
                if (result.ok) {
                    finish(result.ast, "", result.filledDefinition, result.definitionCache, true, true, result.inferenceComplete);
                }
                else
                    finish(ast, result.error);
            }).catch(workerError => {
                if (input["workerRequestId"] !== requestId || input.value !== inputValue || !input.isConnected) {
                    if (validationRunId !== null)
                        this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (!rowPositionMatches()) {
                    if (validationRunId !== null)
                        this.completeTheoremValidation(validationRunId);
                    return;
                }
                if (!shouldFallbackToSynchronousTheoremValidation(workerError)) {
                    document.getElementById("timeout").classList.remove("hide");
                    finish(ast, TR("类型论 Worker 验证超时，请增大单条定理判定的默认等待时间"), undefined, undefined, false, false);
                    return;
                }
                validateSynchronously();
            });
        };
        div.addEventListener("click", ev => {
            if (this.mode === "tactic-begin" && !this.isTheoremInputDisabled(input)) {
                this.executeTactic(input.value, input);
            }
            else {
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
        const previousDefinitions = this.userDefinedConsts.slice();
        this.createTheoremDragHandle(wrapper, id);
        wrapper.appendChild(button);
        wrapper.appendChild(localLabel);
        wrapper.appendChild(input);
        wrapper.appendChild(div);
        const theorem = { kind: "theorem", id, wrapper, input, localCheckbox };
        const insertIndex = destinationFolder ? this.getFolderAppendIndex(destinationFolder) : -1;
        if (insertIndex >= 0) {
            for (const folder of this.getFolderScopeForFolder(destinationFolder.id))
                folder.length++;
            this.theoremItems.splice(insertIndex, 0, theorem);
        }
        else {
            this.insertTheoremItem(theorem, insertPos);
        }
        this.syncTheoremDomOrder();
        this.realignUserDefinitions(previousInputs, previousDefinitions);
        this.renderTheoremStructure();
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
            if (currentIdx < 0)
                return;
            this.definitionRevision++;
            this.theoremStructureRevision++;
            this.gatePreviewStructureRevision = -1;
            this.onStateChange();
            this.revalidateTheorems(currentIdx);
        });
        if (!this.restoringTheoremItems)
            input.focus();
        return input;
    }
    getTacticOutputInsertPosition() {
        const target = this.tacticTargetInput && this.getTheoremItemForInput(this.tacticTargetInput);
        if (target)
            return target.wrapper;
        return undefined;
    }
    getTacticOutputFolder() {
        if (this.tacticTargetInput)
            return undefined;
        const scopeId = this.getActiveTacticScopeId();
        return this.theoremItems.find((item) => item.kind === "folder" && item.id === scopeId);
    }
    getFolderAppendIndex(folder) {
        const folderIndex = this.theoremItems.indexOf(folder);
        return folderIndex < 0
            ? -1
            : Math.min(this.theoremItems.length, folderIndex + folder.length + 1);
    }
    settlePendingTheorems(coordinateValidation = false) {
        const inputs = this.getInhabitatArray();
        const first = findEarliestPendingTheorem(inputs, input => !!input.parentElement?.classList.contains("checking"), input => this.isTheoremInputDisabled(input));
        if (!first)
            return;
        if (coordinateValidation) {
            const startIndex = inputs.indexOf(first);
            if (startIndex >= 0)
                this.revalidateTheorems(startIndex);
            return;
        }
        first.onblur({ forceSync: true, updateDefs: true });
    }
    equalGateTypes(candidate, target) {
        return this.core.semanticTypePatternMatch(candidate, target);
    }
    // find whether user has inhabitat of given type
    queryType(typeStr) {
        if (this.gateQueryCache.has(typeStr))
            return this.gateQueryCache.get(typeStr);
        const inputs = this.getInhabitatArray();
        let ref;
        try {
            ref = parser.parse(typeStr);
        }
        catch (error) {
            this.gateQueryCache.set(typeStr, false);
            return false;
        }
        const refKey = parser.stringify(ref);
        const candidates = [];
        for (const e of inputs) {
            if (this.isTheoremInputDisabled(e))
                continue;
            const wrapper = e.parentElement;
            if (!wrapper || wrapper.classList.contains("error") || wrapper.classList.contains("infering") || wrapper.classList.contains("checking"))
                continue;
            const checked = e["validatedType"];
            if (!checked)
                continue;
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
            }
            catch (e) {
                continue;
            }
        }
        this.gateQueryCache.set(typeStr, false);
        return false;
    }
    queryDefPuzzle(name) {
        this.settlePendingTheorems();
        this.getHottDefCtxt(this.getInhabitatArray().length);
        // Puzzle probes run on the main-thread Core after Worker validation.
        // Do not inherit a stale syntax mode from startup, type-list rebuilds,
        // or an earlier gate query: it can make a valid restored definition
        // fail only in the UI even though the Worker accepted it.
        this.core.state.disableSimpleFn = this.disableSimpleFn;
        this.core.state.disableSimpleEq = this.disableSimpleEq;
        const def = this.core.state.userDefs[name];
        if (!def)
            return false;
        const defvar = wrapVar(name);
        try {
            if (name === "code_nat") {
                const True = wrapVar("True");
                const False = wrapVar("False");
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
            }
            else if (name === "what") {
                this.core.checkType({ type: "===", name: "", nodes: [wrapApply(defvar, wrapVar("0b")), wrapApply(defvar, wrapVar("1b"), wrapVar("True"))] }, [], false);
            }
            else if (name === "ftr") {
                this.core.checkType({ type: "===", name: "", nodes: [wrapApply(defvar, wrapVar("0")), wrapVar("True")] }, [], false);
                let k = "True";
                for (let i = 1; i < 5; i++) {
                    k += "->True";
                    this.core.checkType(parser.parse(`ftr ${i} === ` + k), [], false);
                }
            }
            else if (name === "fillList") {
                this.core.checkType(parser.parse("fillList Bool 0b 2 === cons 0b (cons 0b nil)"), [], false);
                this.core.checkType(parser.parse("fillList nat 33 3 === cons 33 (cons 33 (cons 33 nil))"), [], false);
                this.core.checkType(parser.parse("fillList True true 0 === nil"), [], false);
            }
            else if (name === "joinList") {
                this.core.checkType(parser.parse("joinList nat (cons 10 nil) (cons 2 nil) === cons 10 (cons 2 nil)"), [], false);
                this.core.checkType(parser.parse("joinList nat nil (cons 2 nil) === (cons 2 nil)"), [], false);
                this.core.checkType(parser.parse("joinList False nil nil === nil"), [], false);
                this.core.checkType(parser.parse("joinList True (cons true (cons true nil)) nil === (cons true (cons true nil))"), [], false);
                this.core.checkType(parser.parse("joinList Bool (cons 0b (cons 0b nil)) (cons 1b nil) === (cons 0b (cons 0b (cons 1b nil)))"), [], false);
            }
            else if (name === "lenList") {
                this.core.checkType(parser.parse("lenList Bool (cons 0b nil) === 1"), [], false);
                this.core.checkType(parser.parse("lenList nat (cons 33 (cons 0 (cons 1 nil)))=== 3"), [], false);
                this.core.checkType(parser.parse("lenList False nil === 0"), [], false);
            }
            else if (name === "sumList") {
                this.core.checkType(parser.parse("sumList (cons 14 nil) === 14"), [], false);
                this.core.checkType(parser.parse("sumList (cons 0 (cons 0 (cons 0 nil)))=== 0"), [], false);
                this.core.checkType(parser.parse("sumList (cons 3 (cons 6 (cons 8 nil)))=== 17"), [], false);
                this.core.checkType(parser.parse("sumList nil === 0"), [], false);
            }
            else if (name === "mapList") {
                this.core.checkType(parser.parse("mapList False nat (ind_False (Lx:False,nat)) nil === nil"), [], false);
                this.core.checkType(parser.parse("mapList nat nat succ (cons 0 (cons 1 (cons 2 nil))) === (cons 1 (cons 2 (cons 3 nil)))"), [], false);
                this.core.checkType(parser.parse("mapList nat (natXnat) (Lx:nat.(x,succ x)) (cons 3 (cons 2 nil)) === (cons (3,4) (cons (2,3) nil))"), [], false);
            }
            else if (name === "invList") {
                this.core.checkType(parser.parse("invList Bool (cons 0b nil) === cons 0b nil"), [], false);
                this.core.checkType(parser.parse("invList nat (cons 23 (cons 0 (cons 1 nil))) === (cons 1 (cons 0 (cons 23 nil)))"), [], false);
                this.core.checkType(parser.parse("invList True nil === nil"), [], false);
            }
            else if (name === "firstList") {
                this.core.checkType(parser.parse("firstList False nil === none"), [], false);
                this.core.checkType(parser.parse("firstList Bool (cons 0b nil) === some 0b"), [], false);
                this.core.checkType(parser.parse("firstList nat (cons 12 (cons 3 (cons 45 nil))) === some 45"), [], false);
            }
            else if (name === "lastList") {
                this.core.checkType(parser.parse("lastList False nil === none"), [], false);
                this.core.checkType(parser.parse("lastList Bool (cons 1b nil) === some 1b"), [], false);
                this.core.checkType(parser.parse("lastList nat (cons 45 (cons 0 (cons 20 nil))) === some 45"), [], false);
            }
            else if (name === "del_0") {
                this.core.checkType(parser.parse("del_0 nil === nil"), [], false);
                this.core.checkType(parser.parse("del_0 (cons 0 nil) === nil"), [], false);
                this.core.checkType(parser.parse("del_0 (cons 45 (cons 0 (cons 20 nil))) === cons 45 (cons 20 nil)"), [], false);
            }
            else if (name === "count_0") {
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
            }
            else if (name === "ftreq") {
                let p = "";
                let a = "";
                let ap = "";
                for (let i = 0; i < 5; i++) {
                    this.core.checkType(parser.parse(`ftreq ${i} === Lx:ftr ${i},${p}eq (x ${a}) true`), [], false);
                    p += `Pa${ap}:True,`;
                    a += `a${ap} `;
                    ap += "'";
                }
            }
            else if (name === "Fin") {
                this.core.checkType({ type: "===", name: "", nodes: [wrapApply(defvar, wrapVar("0")), wrapVar("False")] }, [], false);
                let k = "False";
                for (let i = 1; i < 5; i++) {
                    k += "+True";
                    this.core.checkType(parser.parse(`Fin ${i} === ` + k), [], false);
                }
            }
            else if (name === "factorial2") {
                const table = [1, 1, 2, 3, 8, 15, 48, 105, 384, 945, 3840, 10395, 46080, 135135, 645120, 2027025, 10321920, 34459425, 185794560, 654729075, 3715891200, 13749310575, 81749606400, 316234143225, 1961990553600, 7905853580625, 51011754393600, 213458046676875];
                for (let i = Math.random() > 0.5 ? 2 : 1; i < 25; i += 3) {
                    ;
                    this.core.checkType(parser.parse(`factorial2 ${i} === ` + table[i]), [], false);
                }
            }
            else if (name === "Combin") {
                const combin = (a, b) => {
                    if (b === 0 || b === a)
                        return 1;
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
            }
            else
                return false;
        }
        catch (e) {
            return false;
        }
        return true;
    }
    async executeTactic(value, targetInput = null, initialScopeFolderId) {
        if (this.tacticBusy)
            return;
        // A definition immediately above may still be in the Core Worker.
        // Commit that pending validation before taking the definition snapshot
        // used by the proof-assistant Worker.
        this.settlePendingTheorems(true);
        const target = typeof value === "string" ? value : parser.stringify(value);
        const requestId = ++this.tacticRequestId;
        this.tacticTargetInput = targetInput;
        this.tacticScopeExplicit = initialScopeFolderId !== undefined;
        this.tacticScopeFolderId = this.tacticScopeExplicit
            ? initialScopeFolderId
            : this.getDefaultTacticScope(targetInput);
        this.renderTacticScopeOptions();
        this.mode = [target];
        this.setTacticBusy(true);
        document.getElementById("tactic-errmsg").innerText = "";
        try {
            await this.theoremValidation.waitForIdle();
            if (requestId !== this.tacticRequestId || !(this.mode instanceof Array))
                return;
            const snapshot = await this.startAssistSession(target);
            if (requestId !== this.tacticRequestId || !(this.mode instanceof Array))
                return;
            this.tacticDefinitionsRevision = this.definitionRevision;
            this.mode = [target, ...snapshot.history];
            this.renderAssistSnapshot(snapshot);
            const input = document.getElementById("tactic-input");
            input.value = "";
            input.focus();
        }
        catch (error) {
            if (requestId !== this.tacticRequestId)
                return;
            document.getElementById("tactic-hint").innerText = TR("命题格式有误：") + this.formatTacticError(error);
            document.getElementById("tactic-remove").classList.add("hide");
            document.getElementById("tactic-clear").classList.add("hide");
            document.getElementById("copygate").classList.remove("hide");
            document.getElementById("tactic-input").classList.add("hide");
            this.mode = null;
            this.assistSnapshot = null;
            this.tacticTargetInput = null;
            this.tacticScopeFolderId = null;
            this.tacticScopeExplicit = false;
            this.renderTacticScopeOptions();
        }
        finally {
            if (requestId === this.tacticRequestId)
                this.setTacticBusy(false);
        }
        document.getElementById("tactic-list").parentElement.scrollTo(0, 1e8);
    }
    async addTactic(_noCheck) {
        const input = document.getElementById("tactic-input");
        const hint = document.getElementById("tactic-hint");
        if (!this.mode) {
            hint.innerText = TR("请在定理列表中点选待证命题");
            this.mode = "tactic-begin";
            document.getElementById("tactic-clear").classList.add("hide");
            document.getElementById("copygate").classList.remove("hide");
            return;
        }
        if (!(this.mode instanceof Array) || this.tacticBusy)
            return;
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
                if (requestId !== this.tacticRequestId || !(this.mode instanceof Array))
                    return;
                const output = this.updateInhabitList(this.getTacticOutputInsertPosition(), this.getTacticOutputFolder());
                output.focus();
                output.value = qedName
                    ? `${qedName}:=${result.proof}:${result.theorem}`
                    : `${result.proof}:${result.theorem}`;
                output.dispatchEvent(new Event("input"));
                this.closeTacticSession();
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
            if (requestId !== this.tacticRequestId || !(this.mode instanceof Array))
                return;
            this.mode = [target, ...snapshot.history];
            input.value = "";
            this.renderAssistSnapshot(snapshot);
            input.focus();
        }
        catch (error) {
            if (requestId === this.tacticRequestId) {
                document.getElementById("tactic-errmsg").innerText = this.formatTacticError(error);
                input.focus();
            }
        }
        finally {
            if (requestId === this.tacticRequestId)
                this.setTacticBusy(false);
        }
    }
    getInhabitatArray() {
        return Array.from(document.querySelectorAll(".inhabitat .tt-theorem-input"));
    }
    unlock(str, update) {
        this.unlockedTypes.add(str);
        if (update && !this.skipRendering) {
            this.updateTypeList(this.unlockedTypes);
            this.getInhabitatArray()[0]?.onblur({ updateDefs: true });
        }
    }
    updateAfterUnlock() {
        if (this.skipRendering)
            return;
        this.updateTypeList(this.unlockedTypes);
        this.getInhabitatArray()[0]?.onblur({ updateDefs: true });
    }
    disableAxiom(...arr) {
        for (const a of arr) {
            this.unlockedTypes.add("// " + a);
            this.unlockedTypes.add("// @" + a);
        }
        this.updateAfterUnlock();
    }
    enableAxiom(...arr) {
        for (const a of arr) {
            this.unlockedTypes.delete("// " + a);
            this.unlockedTypes.delete("// @" + a);
        }
        this.updateAfterUnlock();
    }
}
//# sourceMappingURL=gui.js.map