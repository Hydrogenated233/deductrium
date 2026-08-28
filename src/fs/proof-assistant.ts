import { TR } from "../lang.js";
import { AST, ASTMgr, ReplvarMatchTable } from "./astmgr.js";
import { ASTParser } from "./astparser.js";
import { DEFERRED_ASSISTANT_STEP, registerDeferredAssistantMaterializer } from "./formalsystem.js";
import type {
    DeferredAssistantPayload,
    Deduction,
    DeductionStep,
    FormalSystem,
    Proposition
} from "./formalsystem.js";
import { Proof } from "./proof.js";
import { InferencePageStore } from "./inference-pages.js";

const astmgr = new ASTMgr();
const parser = new ASTParser();

export type InferenceProofHypothesisKind = "intro" | "variable" | "have" | "page";

export interface InferenceProofHypothesis {
    name: string;
    proposition?: AST;
    /** Original binder for a variable introduced from a universal quantifier. */
    binder?: AST;
    kind: InferenceProofHypothesisKind;
    /** A have hypothesis is available only after its subgoal is solved. */
    sourceNodeId?: number;
}

export interface InferenceProofGoalSnapshot {
    id: number;
    target: AST;
    hypotheses: InferenceProofHypothesis[];
}

export interface InferenceProofSnapshot {
    theorem: AST;
    pageId: string;
    goals: InferenceProofGoalSnapshot[];
    history: string[];
    complete: boolean;
}

export interface InferenceProofMaterializedProposition extends Proposition {
    /** A tauto result is represented as one deferred CPT node. */
    deferredKind?: "cpt" | "assistant";
}

export interface InferenceProofQedResult {
    theorem: AST;
    propositions: InferenceProofMaterializedProposition[];
    steps: DeductionStep[];
    macroName?: string;
    /** Internal rule name used by a bare qed; named qed uses macroName. */
    deductionName?: string;
    recordMacro: boolean;
    /** True when the result is stored as a deferred proof-assistant step. */
    deferred: boolean;
    /** Number of rows already present in the selected page at proof start. */
    existingPropositionCount: number;
    /** True once qed has appended rows/recorded a macro in the page. */
    committed: boolean;
    /** Private provenance marker; only this assistant may commit the preview. */
    sessionToken?: symbol;
    /** Draft revision and page fingerprint captured by materializeQed. */
    revision?: number;
    pageFingerprint?: string;
}

export interface InferenceProofOptions {
    /** Stable inference-page id or page name. Defaults to the active page. */
    pageId?: string;
    history?: string[];
    /** Names currently available in the selected proof-assistant scope. */
    ruleNames?: Iterable<string>;
    /** Fast metarule prefixes currently unlocked; omitted for legacy unrestricted callers. */
    fastMetaRules?: string;
    /** Whether MCPT may close/materialize pure propositional goals. */
    allowMcpt?: boolean;
}

export interface InferenceProofRecommendationOptions {
    /** Only unlocked/visible shared rules should be offered by the UI. */
    ruleNames?: Iterable<string>;
    /** `tauto` is available only after the CPT metarule is unlocked. */
    canTauto?: boolean;
}

type SourceRef =
    | { kind: "hypothesis"; name: string; nodeId?: number }
    | { kind: "page"; index: number; pageId: string }
    | { kind: "rule"; name: string; replaceValues: AST[] };

/**
 * A shared deduction uses `$` names as schema metavariables.  Those names
 * must not share a namespace with `$` atoms written by a proof user.  The
 * assistant therefore gives every application a private, collision-free
 * spelling and only exposes the original names in diagnostics/commands.
 */
type RuleMetavariableContext = {
    names: string[];
    internalByOriginal: Map<string, string>;
    originalByInternal: Map<string, string>;
    conditions: AST[];
    conclusion: AST;
    replaceNames: string[];
    replaceTypes: { [name: string]: boolean };
};

type RuleExplicitArguments = {
    positional: AST[];
    named: Map<string, AST>;
};

type RuleMatchResult = {
    context: RuleMetavariableContext;
    /** Keys are private names from `context`, never user-facing `$` names. */
    matchTable: ReplvarMatchTable;
    /** Original names that remain unbound after conclusion/environment matching. */
    unresolved: string[];
};

type RuleApplicationMatch = {
    premises: AST[];
    conclusion: AST;
    context: RuleMetavariableContext;
    matchTable: ReplvarMatchTable;
    unresolved: string[];
};

type StrategyRuleResolution = {
    name: string;
    /** Maps canonical metavariables ($0, $1, ...) to a user rule's names. */
    metavariables: Map<string, string>;
};

type DeductionAccess =
    | { allowed: true }
    | { allowed: false; kind: "metarule" | "rule"; name: string };

type GeneratedRuleSelection = {
    name: string;
    deduction: Deduction;
    replaceValues: AST[];
};

type RewriteStep = {
    before: AST;
    after: AST;
    /** One-based occurrence of the inserted destination used to restore before. */
    inverseNth: number;
};

interface DraftNode {
    id: number;
    target: AST;
    hypotheses: InferenceProofHypothesis[];
    kind: "pending" | "apply" | "have" | "haveApply" | "revert" | "exact" | "tauto";
    children: DraftNode[];
    ruleName?: string;
    replaceValues?: AST[];
    source?: SourceRef;
    /** Instantiated conclusion/source proposition used by implication apply. */
    appliedProposition?: AST;
    /** Number of leading children required by a shared rule's `⊢` conditions. */
    ruleConditionCount?: number;
    tautoName?: string;
    haveName?: string;
    /** Direct `have name := source arg...` application metadata. */
    haveSource?: SourceRef;
    haveArguments?: AST[];
    haveProposition?: AST;
    revertSource?: SourceRef;
    introBindings: InferenceProofHypothesis[];
}

type EmitResult = { index: number; proposition: AST };

type FormalSystemMutableSnapshot = {
    deductions: { [key: string]: Deduction };
    metaRules: { [key: string]: any };
    metaMacro: { [key: string]: any };
    fastmetarules: string;
    disabledMetaRules: string[];
    consts: string[];
    fns: string[];
    verbs: string[];
};

/**
 * DOM-free proof assistant for the deduction layer.
 *
 * The type-theory assistant has a separate goal engine.  This class deliberately
 * stores only proposition ASTs and a small proof tree; the active inference page
 * is untouched until the caller consumes the result of qed().
 */
export class InferenceProofAssistant {
    readonly fs: FormalSystem;
    readonly pageId: string;
    theorem: AST;
    private targetSource: string;
    private root: DraftNode;
    private history: string[] = [];
    private availableRuleNames?: Set<string>;
    private availableFastMetaRules?: string;
    private allowMcpt = true;
    private nextNodeId = 1;
    private committed = false;
    private readonly sessionToken = Symbol("inference-proof-session");
    private revision = 0;

    constructor(fs: FormalSystem, targetOrPage?: AST | string, options: InferenceProofOptions = {}) {
        this.fs = fs;
        const pageRef = options.pageId ?? (typeof targetOrPage === "string" && fs.inferencePages.page(targetOrPage) ? targetOrPage : undefined);
        const page = pageRef ? fs.inferencePages.page(pageRef) : fs.inferencePages.active;
        if (!page) throw new Error(TR("推理表不存在"));
        this.pageId = page.id;
        this.availableRuleNames = options.ruleNames ? new Set(options.ruleNames) : undefined;
        this.availableFastMetaRules = options.fastMetaRules;
        this.allowMcpt = options.allowMcpt !== false;
        this.theorem = null;
        this.root = null;
        if (typeof targetOrPage !== "string" || !fs.inferencePages.page(targetOrPage) || options.pageId) {
            if (targetOrPage === undefined) throw new Error(TR("空表达式"));
            this.start(targetOrPage, options);
        }
    }

    /** Initialize or restart a proof on this assistant's selected page. */
    start(target: AST | string, options: Pick<InferenceProofOptions, "history"> = {}): InferenceProofSnapshot {
        const ast = this.parseProposition(target);
        this.theorem = astmgr.clone(ast);
        this.targetSource = parser.stringifyTight(ast);
        this.nextNodeId = 1;
        this.root = this.makeNode(ast, []);
        this.history = [];
        this.committed = false;
        this.revision = 0;
        if (options.history?.length) {
            const systemSnapshot = this.captureFormalSystemState();
            const root = this.cloneDraftNode(this.root);
            try {
                this.replayHistory(options.history);
            } catch (error) {
                this.restoreFormalSystemState(systemSnapshot);
                this.root = root;
                this.history = [];
                this.nextNodeId = 2;
                throw error;
            }
        }
        return this.snapshot();
    }

    /** Start from proposition pN in the selected inference page. */
    static fromPageProposition(fs: FormalSystem, index: number, pageId?: string): InferenceProofAssistant {
        const page = pageId ? fs.inferencePages.page(pageId) : fs.inferencePages.active;
        if (!page) throw new Error(TR("推理表不存在"));
        const proposition = page.propositions[index];
        if (!proposition) throw new Error(TR("定理不存在"));
        return new InferenceProofAssistant(fs, proposition.value, { pageId: page.id });
    }

    get commands(): readonly string[] {
        return this.history;
    }

    get currentGoal(): InferenceProofGoalSnapshot | undefined {
        return this.goals[0];
    }

    get goals(): InferenceProofGoalSnapshot[] {
        return this.openNodes().map(node => ({
            id: node.id,
            target: astmgr.clone(node.target),
            hypotheses: this.cloneHypotheses(node.hypotheses)
        }));
    }

    snapshot(): InferenceProofSnapshot {
        if (!this.root || !this.theorem) throw new Error(TR("请先启动证明助手"));
        return {
            theorem: astmgr.clone(this.theorem),
            pageId: this.pageId,
            goals: this.goals,
            history: this.history.slice(),
            complete: this.openNodes().length === 0
        };
    }

    getSnapshot(): InferenceProofSnapshot {
        return this.snapshot();
    }

    /** Return syntax-based candidates only; applying one still performs full validation. */
    recommendations(options: InferenceProofRecommendationOptions = {}): string[] {
        const node = this.openNodes()[0];
        if (!node) return [];
        const availableRuleNames = options.ruleNames
            ? new Set(options.ruleNames)
            : this.availableRuleNames;
        const commands: string[] = [];
        const add = (command: string) => {
            if (!commands.includes(command)) commands.push(command);
        };
        if (this.canIntroduceTarget(node.target)) add("intro");

        const addPropositionSource = (name: string, proposition: AST, allowApply: boolean) => {
            if (this.fixedPropositionMayMatch(proposition, node.target)) add(`exact ${name}`);
            if (!allowApply) return;
            try {
                if (this.matchPropositionApplication(proposition, node.target).premises.length) add(`apply ${name}`);
            } catch { }
        };
        for (const hypothesis of node.hypotheses) {
            if (hypothesis.proposition && this.isHypothesisAvailable(hypothesis)) {
                addPropositionSource(hypothesis.name, hypothesis.proposition, true);
                if (this.canRewriteTarget(node.target, hypothesis.proposition, false, availableRuleNames)) {
                    add(`rw ${hypothesis.name}`);
                }
                const simplifyDirection = this.simplifyDirection(hypothesis.proposition);
                if (simplifyDirection !== null
                    && this.canRewriteTarget(node.target, hypothesis.proposition, simplifyDirection, availableRuleNames)) {
                    add("simp");
                }
                add(`revert ${hypothesis.name}`);
                if (hypothesis.proposition.type === "sym" && ["&", "<>"].includes(hypothesis.proposition.name)
                    && hypothesis.proposition.nodes?.length === 2) {
                    const rules = hypothesis.proposition.name === "&" ? [".&1", ".&2"] : [".<>1", ".<>2"];
                    if (rules.every(rule => this.resolveStrategyRule(rule, availableRuleNames))) {
                        const names = this.nextHypothesisNames(node, 2);
                        add(`obtain <${names[0]},${names[1]}> := ${hypothesis.name}`);
                    }
                }
                if (hypothesis.proposition.type === "sym" && hypothesis.proposition.name === "|"
                    && hypothesis.proposition.nodes?.length === 2
                    && this.canUseFastMetaRule("c")
                    && this.resolveStrategyRule(".|m", availableRuleNames)) {
                    const names = this.nextHypothesisNames(node, 2);
                    add(`obtain ${names[0]} | ${names[1]} := ${hypothesis.name}`);
                }
            }
        }
        if (this.findMatchingHypothesis(node)) add("assumption");
        if (this.isConstructorTarget(node.target)
            && this.resolveStrategyRule(node.target.name === "&" ? ".&" : ".<>", availableRuleNames)) {
            add("constructor");
        }
        if (node.target.type === "sym" && node.target.name === "|" && node.target.nodes?.length === 2) {
            if (this.resolveStrategyRule(".|1", availableRuleNames)) add("left");
            if (this.resolveStrategyRule(".|2", availableRuleNames)) add("right");
        }
        if (this.isSymmetryTarget(node.target)
            && this.resolveStrategyRule(node.target.name === "=" ? ".=s" : ".<>s", availableRuleNames)) {
            add("symm");
        }
        if (this.isReflexiveEqualityTarget(node.target) && this.resolveStrategyRule("a7", availableRuleNames)) {
            add("rfl");
        }
        if (this.findContradictionPair(node) && this.resolveStrategyRule(".m", availableRuleNames)) {
            add("contradiction");
        }
        if (this.canUseFastMetaRule("c") && this.resolveStrategyRule(".mn", availableRuleNames)) {
            add("by_contra");
        }
        if (this.canUseFastMetaRule("c") && this.resolveStrategyRule(".m2", availableRuleNames)) {
            add("by_cases h : ??");
        }
        if (node.target.type === "sym" && node.target.name === ">" && node.target.nodes?.length === 2
            && this.resolveStrategyRule("a3", availableRuleNames)) {
            add("contrapose");
        }
        const page = this.fs.inferencePages.page(this.pageId);
        page?.propositions.forEach((proposition, index) => {
            addPropositionSource(`p${index}`, proposition.value, false);
            if (this.canRewriteTarget(node.target, proposition.value, false, availableRuleNames)) add(`rw p${index}`);
            const simplifyDirection = this.simplifyDirection(proposition.value);
            if (simplifyDirection !== null
                && this.canRewriteTarget(node.target, proposition.value, simplifyDirection, availableRuleNames)) {
                add("simp");
            }
        });

        for (const name of options.ruleNames ?? []) {
            const deduction = this.fs.deductions[name];
            if (deduction && !deduction.conditions.length && this.syntaxMayMatch(deduction.conclusion, node.target)) {
                add(`exact ${name}`);
            }
        }
        if (options.canTauto && this.isPurePropositionalSyntax(node.target)) add("tauto");
        return commands;
    }

    apply(command: string): InferenceProofSnapshot {
        if (!this.root) throw new Error(TR("请先启动证明助手"));
        const value = String(command ?? "").trim();
        if (!value) throw new Error(TR("空命令"));
        const previous = this.history.slice();
        const previousRoot = this.cloneDraftNode(this.root);
        const previousNextNodeId = this.nextNodeId;
        const previousCommitted = this.committed;
        const previousRevision = this.revision;
        const systemSnapshot = this.captureFormalSystemState();
        try {
            this.execute(value);
            this.history.push(value);
            this.revision++;
            return this.snapshot();
        } catch (error) {
            this.restoreFormalSystemState(systemSnapshot);
            this.root = previousRoot;
            this.history = previous;
            this.nextNodeId = previousNextNodeId;
            this.committed = previousCommitted;
            this.revision = previousRevision;
            throw error;
        }
    }

    undo(): InferenceProofSnapshot {
        if (!this.root) throw new Error(TR("请先启动证明助手"));
        if (!this.history.length) return this.snapshot();
        const previousRoot = this.cloneDraftNode(this.root);
        const previousHistory = this.history.slice();
        const previousNextNodeId = this.nextNodeId;
        const previousCommitted = this.committed;
        const previousRevision = this.revision;
        const systemSnapshot = this.captureFormalSystemState();
        try {
            const remaining = this.history.slice(0, -1);
            this.replayHistory(remaining);
            this.committed = false;
            this.revision++;
            return this.snapshot();
        } catch (error) {
            this.restoreFormalSystemState(systemSnapshot);
            this.root = previousRoot;
            this.history = previousHistory;
            this.nextNodeId = previousNextNodeId;
            this.committed = previousCommitted;
            this.revision = previousRevision;
            throw error;
        }
    }

    restore(snapshot: InferenceProofSnapshot): InferenceProofSnapshot {
        if (!snapshot || !Array.isArray(snapshot.history)) throw new Error(TR("证明助手状态无效"));
        if (!this.root) throw new Error(TR("请先启动证明助手"));
        if (snapshot.pageId !== this.pageId || !snapshot.theorem
            || !astmgr.equal(snapshot.theorem, this.theorem)) {
            throw new Error(TR("证明助手状态与当前命题不匹配"));
        }
        const previous = this.history.slice();
        const previousRoot = this.cloneDraftNode(this.root);
        const previousNextNodeId = this.nextNodeId;
        const previousCommitted = this.committed;
        const previousRevision = this.revision;
        const systemSnapshot = this.captureFormalSystemState();
        try {
            this.replayHistory(snapshot.history);
            this.committed = false;
            this.revision++;
        } catch (error) {
            this.restoreFormalSystemState(systemSnapshot);
            this.root = previousRoot;
            this.history = previous;
            this.nextNodeId = previousNextNodeId;
            this.committed = previousCommitted;
            this.revision = previousRevision;
            throw error;
        }
        return this.snapshot();
    }

    /** Finish a proof as one deferred, atomic inference step. */
    qed(name?: string): InferenceProofQedResult {
        const result = this.materializeQed(name);
        return this.commit(result);
    }

    /**
     * Build a preview without expanding the proof tree.  Only the command
     * history and the page premises are retained; `entr`/`inln` replay them
     * later when the generated step is explicitly expanded.
     */
    materializeQed(name?: string): InferenceProofQedResult {
        if (!this.root) throw new Error(TR("请先启动证明助手"));
        if (this.committed) throw new Error(TR("证明已经完成"));
        if (this.openNodes().length) throw new Error(TR("仍有未完成的证明目标"));
        this.validateMacroName(name);
        const page = this.fs.inferencePages.page(this.pageId);
        if (!page) throw new Error(TR("推理表不存在"));
        const data = this.buildDeferredQed(name);
        return {
            theorem: astmgr.clone(this.theorem),
            propositions: [data.row],
            steps: [data.step],
            macroName: name,
            deductionName: data.deductionName,
            recordMacro: name !== undefined,
            deferred: true,
            existingPropositionCount: page.propositions.length,
            committed: false,
            sessionToken: this.sessionToken,
            revision: this.revision,
            pageFingerprint: this.pageFingerprint(page)
        };
    }

    /** Append a preview returned by materializeQed without expanding it. */
    commit(result: InferenceProofQedResult): InferenceProofQedResult {
        if (result.committed) throw new Error(TR("证明已经提交"));
        if ((result as InferenceProofQedResult & { sessionToken?: symbol }).sessionToken !== this.sessionToken) {
            throw new Error(TR("证明结果不属于当前证明助手"));
        }
        if (result.revision !== this.revision) {
            throw new Error(TR("证明结果已过期，请重新结束证明"));
        }
        this.validateMacroName(result.macroName);
        if (!result.theorem || !astmgr.equal(result.theorem, this.theorem)) {
            throw new Error(TR("证明结果与当前命题不匹配"));
        }
        const page = this.fs.inferencePages.page(this.pageId);
        if (!page) throw new Error(TR("推理表不存在"));
        if (result.existingPropositionCount !== page.propositions.length) {
            throw new Error(TR("证明结果已过期，请重新结束证明"));
        }
        if (result.pageFingerprint !== this.pageFingerprint(page)) {
            throw new Error(TR("证明结果已过期，请重新结束证明"));
        }
        const previousActive = this.fs.inferencePages.activeId;
        const previousRows = page.propositions.slice();
        const systemSnapshot = this.captureFormalSystemState();
        try {
            this.ensureTautoRules(this.root);
            const data = this.buildDeferredQed(result.macroName, result.deductionName);
            result.deductionName = data.deductionName;
            result.propositions = [data.row];
            result.steps = [data.step];
            result.deferred = true;
            if (result.macroName) {
                this.fs.addDeduction(data.deductionName, data.value, "证明助手录制*");
                const deduction = this.fs.deductions[data.deductionName];
                deduction.deferredKind = "assistant";
                deduction.deferredPayload = data.payload;
                // A named qed is a real user rule; its replace parameters are
                // inferred from the generated rule as before.  The row is only
                // shown for the bare-qed branch below.
            } else {
                // Retain one compatibility marker for callers that inspect the
                // old `result.deductionName`/`fs.deductions[...]` surface, but
                // reuse it for every proof.  The actual recipe lives on the
                // proposition step, so this marker is never the source of
                // truth for expansion and is not persisted as a user rule.
                let marker = this.fs.deductions[DEFERRED_ASSISTANT_STEP];
                if (!marker) {
                    this.fs.addDeduction(DEFERRED_ASSISTANT_STEP, data.value, "证明助手录制*");
                    marker = this.fs.deductions[DEFERRED_ASSISTANT_STEP];
                }
                marker.deferredKind = "assistant";
                // Keep the marker and row pointed at the same payload object.
                // The row remains authoritative, while this compatibility
                // alias lets legacy callers that edited the old marker payload
                // invalidate/retry a recipe without a stale duplicate.
                marker.deferredPayload = data.payload;
                marker.steps = undefined;
                marker.replaceNames = [];
                page.propositions.push({
                    value: astmgr.clone(data.row.value),
                    from: {
                        deductionIdx: data.step.deductionIdx,
                        conditionIdxs: [...data.step.conditionIdxs],
                        replaceValues: [],
                        assistant: marker.deferredPayload
                    },
                    deferredKind: "assistant"
                });
            }
            if (result.macroName) {
                // Preserve legacy `qed name`/`m name` semantics: the active
                // proof table is consumed after recording the named rule.
                page.propositions = [];
            }
            if (previousActive !== page.id) this.fs.inferencePages.activate(previousActive);
            result.committed = true;
            this.committed = true;
            return result;
        } catch (error) {
            page.propositions = previousRows;
            this.restoreFormalSystemState(systemSnapshot);
            if (previousActive !== page.id) this.fs.inferencePages.activate(previousActive);
            throw error;
        }
    }

    private validateMacroName(name: string | undefined): void {
        if (name === undefined) return;
        if (typeof name !== "string" || !name) {
            throw new Error(TR("qed命名参数必须是单个常量名"));
        }
        const error = this.fs.validateNewDeductionName(name);
        if (error) throw new Error(error);
    }

    private captureFormalSystemState(): FormalSystemMutableSnapshot {
        return {
            deductions: Object.fromEntries(Object.entries(this.fs.deductions)
                .map(([name, deduction]) => [name, this.cloneDeduction(deduction)])),
            metaRules: Object.fromEntries(Object.entries(this.fs.metaRules)
                .map(([name, rule]) => [name, this.cloneMetaRule(rule)])),
            metaMacro: Object.fromEntries(Object.entries(this.fs.metaMacro)
                .map(([name, macro]) => [name, this.cloneMetaMacro(macro)])),
            fastmetarules: this.fs.fastmetarules,
            disabledMetaRules: [...this.fs.disabledMetaRules],
            consts: [...this.fs.consts],
            fns: [...this.fs.fns],
            verbs: [...this.fs.verbs]
        };
    }

    private restoreFormalSystemState(snapshot: FormalSystemMutableSnapshot): void {
        this.fs.deductions = Object.fromEntries(Object.entries(snapshot.deductions)
            .map(([name, deduction]) => [name, this.cloneDeduction(deduction)]));
        this.fs.metaRules = Object.fromEntries(Object.entries(snapshot.metaRules)
            .map(([name, rule]) => [name, this.cloneMetaRule(rule)]));
        this.fs.metaMacro = Object.fromEntries(Object.entries(snapshot.metaMacro)
            .map(([name, macro]) => [name, this.cloneMetaMacro(macro)]));
        this.fs.fastmetarules = snapshot.fastmetarules;
        this.fs.disabledMetaRules = [...snapshot.disabledMetaRules];
        this.fs.consts.clear();
        snapshot.consts.forEach(name => this.fs.consts.add(name));
        this.fs.fns.clear();
        snapshot.fns.forEach(name => this.fs.fns.add(name));
        this.fs.verbs.clear();
        snapshot.verbs.forEach(name => this.fs.verbs.add(name));
    }

    private cloneDeduction(deduction: Deduction): Deduction {
        return {
            value: astmgr.clone(deduction.value),
            conditions: deduction.conditions.map(value => astmgr.clone(value)),
            conclusion: astmgr.clone(deduction.conclusion),
            replaceNames: [...deduction.replaceNames],
            replaceTypes: { ...deduction.replaceTypes },
            from: deduction.from,
            steps: deduction.steps?.map(step => ({
                deductionIdx: step.deductionIdx,
                conditionIdxs: [...step.conditionIdxs],
                replaceValues: step.replaceValues.map(value => astmgr.clone(value)),
                ...(step.assistant ? { assistant: this.cloneDeferredAssistantPayload(step.assistant) } : {})
            })),
            deferredKind: deduction.deferredKind,
            deferredPayload: deduction.deferredPayload ? {
                kind: "assistant",
                version: 1,
                pageId: deduction.deferredPayload.pageId,
                theorem: astmgr.clone(deduction.deferredPayload.theorem),
                history: [...deduction.deferredPayload.history],
                ...(deduction.deferredPayload.ruleNames ? { ruleNames: [...deduction.deferredPayload.ruleNames] } : {}),
                ...(deduction.deferredPayload.fastMetaRules !== undefined
                    ? { fastMetaRules: deduction.deferredPayload.fastMetaRules } : {}),
                ...(deduction.deferredPayload.allowMcpt !== undefined
                    ? { allowMcpt: deduction.deferredPayload.allowMcpt } : {}),
                premises: deduction.deferredPayload.premises.map(premise => ({
                    pageId: premise.pageId,
                    index: premise.index,
                    value: astmgr.clone(premise.value)
                }))
            } : undefined,
            tempvars: new Set(deduction.tempvars ?? [])
        };
    }

    private cloneDeferredAssistantPayload(payload: DeferredAssistantPayload): DeferredAssistantPayload {
        return {
            kind: "assistant",
            version: 1,
            pageId: payload.pageId,
            theorem: astmgr.clone(payload.theorem),
            history: [...payload.history],
            ...(payload.ruleNames ? { ruleNames: [...payload.ruleNames] } : {}),
            ...(payload.fastMetaRules !== undefined ? { fastMetaRules: payload.fastMetaRules } : {}),
            ...(payload.allowMcpt !== undefined ? { allowMcpt: payload.allowMcpt } : {}),
            premises: payload.premises.map(premise => ({
                ...(premise.pageId ? { pageId: premise.pageId } : {}),
                index: premise.index,
                value: astmgr.clone(premise.value)
            }))
        };
    }

    private cloneMetaRule(rule: any): any {
        return {
            value: astmgr.clone(rule.value),
            conditions: (rule.conditions ?? []).map(value => astmgr.clone(value)),
            conclusions: (rule.conclusions ?? []).map(value => astmgr.clone(value)),
            replaceNames: [...(rule.replaceNames ?? [])],
            conditionDeductionIdxs: [...(rule.conditionDeductionIdxs ?? [])],
            from: rule.from
        };
    }

    private cloneMetaMacro(macro: any): any {
        const cloneTree = (tree: any): any => Array.isArray(tree) ? tree.map(cloneTree) : tree;
        return {
            inputs: [...(macro.inputs ?? [])],
            output: cloneTree(macro.output),
            from: macro.from
        };
    }

    private cloneSource(source?: SourceRef): SourceRef | undefined {
        if (!source) return undefined;
        if (source.kind === "rule") {
            return { kind: "rule", name: source.name, replaceValues: source.replaceValues.map(value => astmgr.clone(value)) };
        }
        return { ...source };
    }

    private cloneDraftNode(node: DraftNode): DraftNode {
        return {
            id: node.id,
            target: astmgr.clone(node.target),
            hypotheses: this.cloneHypotheses(node.hypotheses),
            kind: node.kind,
            children: node.children.map(child => this.cloneDraftNode(child)),
            ruleName: node.ruleName,
            replaceValues: node.replaceValues?.map(value => astmgr.clone(value)),
            source: this.cloneSource(node.source),
            appliedProposition: node.appliedProposition ? astmgr.clone(node.appliedProposition) : undefined,
            ruleConditionCount: node.ruleConditionCount,
            tautoName: node.tautoName,
            haveName: node.haveName,
            haveSource: this.cloneSource(node.haveSource),
            haveArguments: node.haveArguments?.map(value => astmgr.clone(value)),
            haveProposition: node.haveProposition ? astmgr.clone(node.haveProposition) : undefined,
            revertSource: this.cloneSource(node.revertSource),
            introBindings: this.cloneHypotheses(node.introBindings)
        };
    }

    private pageFingerprint(page: { propositions: Proposition[] }): string {
        return page.propositions.map(proposition => {
            const from = proposition.from;
            if (!from) return parser.stringifyTight(proposition.value);
            return [
                parser.stringifyTight(proposition.value),
                from.deductionIdx,
                from.conditionIdxs.join(","),
                from.replaceValues.map(value => parser.stringifyTight(value)).join(",")
            ].join("\u0000");
        }).join("\u0001");
    }

    private collectExternalPremises(): DeferredAssistantPayload["premises"] {
        const page = this.fs.inferencePages.page(this.pageId);
        const result: DeferredAssistantPayload["premises"] = [];
        const seen = new Set<string>();
        const visit = (node: DraftNode | null) => {
            if (!node) return;
            const source = node.kind === "haveApply" ? node.haveSource : node.source;
            if ((node.kind === "exact" || node.kind === "apply" || node.kind === "haveApply")
                && source?.kind === "page") {
                const key = `${source.pageId}:${source.index}`;
                if (!seen.has(key)) {
                    const proposition = this.fs.inferencePages.page(source.pageId)?.propositions[source.index];
                    if (!proposition) throw new Error(TR("证明助手引用了不存在的推理表定理"));
                    seen.add(key);
                    result.push({
                        pageId: source.pageId,
                        index: source.index,
                        value: astmgr.clone(proposition.value)
                    });
                }
            }
            node.children.forEach(visit);
        };
        visit(this.root);
        // Keep the selected page in the payload even when no external premise
        // is used.  This makes old drafts deterministic across page switches.
        if (!page) throw new Error(TR("推理表不存在"));
        return result;
    }

    private buildDeferredQed(name?: string, preferredName?: string): {
        deductionName?: string;
        value: AST;
        row: InferenceProofMaterializedProposition;
        step: DeductionStep;
        payload: DeferredAssistantPayload;
    } {
        const premises = this.collectExternalPremises();
        // Named qed keeps its user-facing deduction.  A bare qed is instead a
        // virtual assistant step carrying its own recipe; allocating one
        // `__assist_N` rule per proof needlessly pollutes the shared rule table.
        const deductionName = name ?? (
            preferredName === DEFERRED_ASSISTANT_STEP
                ? DEFERRED_ASSISTANT_STEP
                : preferredName && !this.fs.deductions[preferredName]
                    ? preferredName
                    : DEFERRED_ASSISTANT_STEP
        );
        const theorem = astmgr.clone(this.theorem);
        const value: AST = {
            type: "meta",
            name: "⊢",
            nodes: [
                { type: "fn", name: "#array", nodes: premises.map(premise => astmgr.clone(premise.value)) },
                { type: "fn", name: "#array", nodes: [astmgr.clone(theorem)] }
            ]
        };
        const payload: DeferredAssistantPayload = {
            kind: "assistant",
            version: 1,
            pageId: this.pageId,
            theorem: astmgr.clone(theorem),
            history: this.history.slice(),
            ...(this.availableRuleNames ? { ruleNames: [...this.availableRuleNames] } : {}),
            ...(this.availableFastMetaRules !== undefined ? { fastMetaRules: this.availableFastMetaRules } : {}),
            allowMcpt: this.allowMcpt,
            premises: premises.map(premise => ({
                pageId: premise.pageId,
                index: premise.index,
                value: astmgr.clone(premise.value)
            }))
        };
        const step: DeductionStep = {
            deductionIdx: deductionName ?? DEFERRED_ASSISTANT_STEP,
            conditionIdxs: premises.map(premise => premise.index),
            replaceValues: [],
            assistant: payload
        };
        return {
            deductionName,
            value,
            step,
            payload,
            row: {
                value: astmgr.clone(theorem),
                from: {
                    deductionIdx: step.deductionIdx,
                    conditionIdxs: [...step.conditionIdxs],
                    replaceValues: [],
                    assistant: this.cloneDeferredAssistantPayload(payload)
                },
                deferredKind: "assistant"
            }
        };
    }

    /** Replay and fully materialize a deferred assistant proof on demand. */
    materializeForDeferred(): {
        propositions: InferenceProofMaterializedProposition[];
        steps: DeductionStep[];
        value: AST;
        tempvars: Set<string>;
    } {
        if (!this.root) throw new Error(TR("请先启动证明助手"));
        if (this.openNodes().length) throw new Error(TR("证明助手仍有未完成的证明目标"));
        this.ensureTautoRules(this.root);
        const materialized = this.materialize(true);
        const previous = this.fs.propositions;
        try {
            // `materialize(true)` keeps the replay page's base length in
            // condition indexes.  Macro compilation expects indexes local to
            // the temporary proposition list, so strip that base offset first.
            const normalized = materialized.propositions.map(row => row.from ? {
                value: astmgr.clone(row.value),
                from: {
                    deductionIdx: row.from.deductionIdx,
                    conditionIdxs: row.from.conditionIdxs.map(index =>
                        index >= materialized.basePropositionCount
                            ? index - materialized.basePropositionCount
                            : index
                    ),
                    replaceValues: row.from.replaceValues.map(value => astmgr.clone(value)),
                    ...(row.from.assistant ? { assistant: this.cloneDeferredAssistantPayload(row.from.assistant) } : {})
                },
                ...(row.deferredKind ? { deferredKind: row.deferredKind } : {})
            } as InferenceProofMaterializedProposition : {
                value: astmgr.clone(row.value),
                from: null
            });
            this.fs.propositions = normalized;
            const compiled = this.fs.compileMacroFromPropositions();
            return {
                propositions: normalized,
                steps: compiled.steps,
                value: compiled.value,
                tempvars: this.fs.findLocalNamesInDeductionStep(compiled.steps)
            };
        } finally {
            this.fs.propositions = previous;
        }
    }

    /** Materialize deferred MCPT rules only at the commit boundary. */
    private ensureTautoRules(node: DraftNode | null): void {
        if (!node) return;
        if (node.kind === "tauto" && node.tautoName) {
            const existing = this.fs.deductions[node.tautoName];
            if (!existing) {
                this.fs.metaCompleteTheorem(astmgr.clone(node.target), node.tautoName, "证明助手tauto*");
            } else {
                if (existing.deferredKind !== "cpt") {
                    throw new Error(TR("tauto内部规则名称冲突：") + node.tautoName);
                }
                try {
                    this.assertSameProposition(existing.conclusion, node.target);
                } catch {
                    throw new Error(TR("tauto内部规则名称冲突：") + node.tautoName);
                }
            }
        }
        for (const child of node.children) this.ensureTautoRules(child);
    }

    private execute(command: string): void {
        const match = /^([^\s]+)(?:\s+([\s\S]*))?$/.exec(command);
        if (!match) throw new Error(TR("无效命令"));
        const name = match[1];
        const args = match[2]?.trim() ?? "";
        switch (name) {
            case "intro": return this.intro(args);
            case "intros": return this.intros(args);
            case "exact": return this.exact(args);
            case "apply": return this.applyRule(args);
            case "have": return this.have(args);
            case "obtain": return this.obtain(args);
            case "revert": return this.revert(args);
            case "assumption": return this.assumption(args);
            case "constructor": return this.constructorStrategy(args);
            case "left": return this.disjunctionStrategy("left", args);
            case "right": return this.disjunctionStrategy("right", args);
            case "symm": return this.symm(args);
            case "rfl": return this.rfl(args);
            case "rw": return this.rewrite(args);
            case "nth_rw": return this.nthRewrite(args);
            case "simp": return this.simplify(args);
            case "contradiction": return this.contradiction(args);
            case "by_contra": return this.byContra(args);
            case "by_cases": return this.byCases(args);
            case "contrapose": return this.contrapose(args);
            case "tauto": return this.tauto(args);
            case "qed": throw new Error(TR("qed请使用结束证明按钮"));
            default: throw new Error(TR("未知的证明策略") + name);
        }
    }

    private intro(argument: string): void {
        const name = argument.trim();
        this.introNode(this.requireCurrentNode(), name);
    }

    private canUseFastMetaRule(prefix: string): boolean {
        return this.availableFastMetaRules === undefined || this.availableFastMetaRules.includes(prefix);
    }

    private canIntroduceTarget(target: AST): boolean {
        if (target.type !== "sym" || ![">", "V"].includes(target.name)) return false;
        return target.name === ">"
            ? this.canUseFastMetaRule("c") && this.canUseFastMetaRule("<")
            : this.canUseFastMetaRule("v");
    }

    private assertIntroMetaRule(target: AST): void {
        if (target.name === ">" && !this.canUseFastMetaRule("c")) {
            throw new Error(TR("intro需要解锁条件演绎元定理"));
        }
        if (target.name === ">" && !this.canUseFastMetaRule("<")) {
            throw new Error(TR("intro自动生成条件演绎步骤还需要解锁逆演绎元定理"));
        }
        if (target.name === "V" && !this.canUseFastMetaRule("v")) {
            throw new Error(TR("intro需要解锁条件概括元定理"));
        }
    }

    /** Introduce several leading binders as one atomic assistant command. */
    private intros(argument: string): void {
        const value = argument.trim();
        const names = value ? value.split(/[\s,]+/).filter(Boolean) : [];
        const node = this.requireCurrentNode();
        if (!names.length) {
            let introduced = 0;
            while (node.target.type === "sym" && [">", "V"].includes(node.target.name)) {
                this.introNode(node, "");
                introduced++;
            }
            if (!introduced) throw new Error(TR("intros需要至少一个名称或可引入的前提"));
            return;
        }
        for (const name of names) this.introNode(node, name);
    }

    private introNode(node: DraftNode, name: string): void {
        if (name && !/^[^\s,]+$/.test(name)) throw new Error(TR("intro名称无效"));
        const target = node.target;
        if (target.type !== "sym" || ![">", "V"].includes(target.name)) {
            throw new Error(TR("intro只能处理蕴含或全称量词"));
        }
        this.assertIntroMetaRule(target);
        if (target.name === ">") {
            const proposition = astmgr.clone(target.nodes[0]);
            const hypothesis: InferenceProofHypothesis = {
                name: name || this.nextHypothesisName(node),
                proposition,
                kind: "intro"
            };
            this.assertUniqueHypothesis(node, hypothesis.name);
            node.hypotheses = [...node.hypotheses, hypothesis];
            node.introBindings.push(hypothesis);
            node.target = astmgr.clone(target.nodes[1]);
            return;
        }

        const binder = target.nodes[0];
        if (binder.type !== "replvar") throw new Error(TR("全称量词约束变量无效"));
        const replacement = name || this.nextHypothesisName(node);
        if (!/^[^\s,]+$/.test(replacement)) throw new Error(TR("intro名称无效"));
        this.assertUniqueHypothesis(node, replacement);
        node.target = this.substituteBound(target.nodes[1], binder.name, replacement);
        const hypothesis: InferenceProofHypothesis = {
            name: replacement,
            binder: astmgr.clone(binder),
            kind: "variable"
        };
        node.hypotheses = [...node.hypotheses, hypothesis];
        node.introBindings.push(hypothesis);
    }

    private exact(argument: string): void {
        const node = this.requireCurrentNode();
        if (!argument.trim()) throw new Error(TR("exact需要一个证明来源"));
        const source = this.resolveSource(argument.trim(), node);
        if (source.kind !== "rule") {
            this.assertSameProposition(this.getSourceProposition(source, node), node.target);
        } else {
            const deduction = this.requireDeduction(source.name);
            if (deduction.conditions.length) throw new Error(TR("该规则包含条件，请使用apply"));
            const match = this.matchConclusion(deduction, node.target, {
                positional: [],
                named: new Map()
            }, deduction.conclusion, node);
            this.assertRuleMatchComplete(match, source.name);
            source.replaceValues = deduction.replaceNames.map(name => {
                const value = match.matchTable[match.context.internalByOriginal.get(name)!];
                if (!value) throw new Error(TR("无法从目标推断规则参数") + name);
                return astmgr.clone(value);
            });
        }
        node.kind = "exact";
        node.source = source;
        node.children = [];
    }

    /** Close the goal with a directly matching local hypothesis. */
    private assumption(argument: string): void {
        if (argument.trim()) throw new Error(TR("assumption不接受参数"));
        const node = this.requireCurrentNode();
        const name = this.findMatchingHypothesis(node);
        if (!name) throw new Error(TR("未找到与当前目标匹配的假设"));
        this.exact(name);
    }

    /** Apply the canonical constructor rule for conjunction/equivalence. */
    private constructorStrategy(argument: string): void {
        if (argument.trim()) throw new Error(TR("constructor不接受参数"));
        const node = this.requireCurrentNode();
        if (node.target.type !== "sym" || node.target.nodes?.length !== 2) {
            throw new Error(TR("constructor只能作用于合取或等价目标"));
        }
        if (node.target.name === "&") {
            const rule = this.resolveStrategyRule(".&");
            if (!rule) throw new Error(TR("constructor需要解锁合取构造规则或提供等价推理规则"));
            this.applyRule(rule.name);
            return;
        }
        if (node.target.name === "<>") {
            const rule = this.resolveStrategyRule(".<>");
            if (!rule) throw new Error(TR("constructor需要解锁等价构造规则或提供等价推理规则"));
            this.applyRule(rule.name);
            return;
        }
        throw new Error(TR("constructor只能作用于合取或等价目标"));
    }

    /** Select one side of a disjunction goal through an available intro rule. */
    private disjunctionStrategy(side: "left" | "right", argument: string): void {
        if (argument.trim()) throw new Error(TR(side + "不接受参数"));
        const node = this.requireCurrentNode();
        if (node.target.type !== "sym" || node.target.name !== "|" || node.target.nodes?.length !== 2) {
            throw new Error(TR(side + "只能作用于析取目标"));
        }
        const ruleName = side === "left" ? ".|1" : ".|2";
        const rule = this.resolveStrategyRule(ruleName);
        if (!rule) throw new Error(TR(side + "需要解锁析取构造规则或提供等价推理规则"));
        this.applyRule(rule.name);
    }

    /** Swap both sides of an equality or equivalence target. */
    private symm(argument: string): void {
        if (argument.trim()) throw new Error(TR("symm不接受参数"));
        const node = this.requireCurrentNode();
        if (!this.isSymmetryTarget(node.target)) {
            throw new Error(TR("symm只能作用于等式或等价目标"));
        }
        const rule = this.resolveStrategyRule(node.target.name === "=" ? ".=s" : ".<>s");
        if (!rule) throw new Error(TR("symm需要解锁对称规则或提供等价推理规则"));
        this.applyRule(rule.name);
    }

    /** Close a reflexive equality through an unlocked/equivalent a7 rule. */
    private rfl(argument: string): void {
        if (argument.trim()) throw new Error(TR("rfl不接受参数"));
        const node = this.requireCurrentNode();
        if (!this.isReflexiveEqualityTarget(node.target)) {
            throw new Error(TR("rfl只能证明两端定义相同的等式"));
        }
        const rule = this.resolveStrategyRule("a7");
        if (!rule) throw new Error(TR("rfl需要解锁等式自反规则或提供等价推理规则"));
        this.exact(rule.name);
    }

    /** Rewrite every matching target occurrence using one or more equalities. */
    private rewrite(argument: string): void {
        const text = argument.trim();
        if (!text) throw new Error(TR("rw需要一个等式来源"));
        if (/\s+at\s+/i.test(text)) throw new Error(TR("rw at 假设改写尚未支持"));
        const sourceList = text.startsWith("[") && text.endsWith("]")
            ? text.slice(1, -1).split(",").map(value => value.trim()).filter(Boolean)
            : [text];
        if (!sourceList.length) throw new Error(TR("rw等式列表为空"));
        for (const value of sourceList) {
            const spec = this.parseRewriteSource(value);
            this.rewriteWithSource(spec.source, spec.reverse, null);
        }
    }

    /** Rewrite one left-to-right occurrence, numbered from one. */
    private nthRewrite(argument: string): void {
        const match = /^([1-9][0-9]*)\s+([\s\S]+)$/.exec(argument.trim());
        if (!match) throw new Error(TR("nth_rw语法应为 nth_rw 序号 等式来源"));
        const spec = this.parseRewriteSource(match[2].trim().replace(/^\[(.*)\]$/, "$1"));
        this.rewriteWithSource(spec.source, spec.reverse, Number(match[1]));
    }

    /** Normalize the target with local/page equalities in a terminating order. */
    private simplify(argument: string): void {
        const text = argument.trim();
        if (/\bat\s+/i.test(text)) throw new Error(TR("simp at 假设化简尚未支持"));
        let only = false;
        let specified: string[] = [];
        if (text) {
            const match = /^(only\s+)?\[([^\]]*)\]$/.exec(text);
            if (!match) throw new Error(TR("simp语法应为 simp、simp [h,g] 或 simp only [h,g]"));
            only = !!match[1];
            specified = match[2].split(",").map(value => value.trim()).filter(Boolean);
        }
        const node = this.requireCurrentNode();
        const names: string[] = [];
        const addName = (name: string) => {
            if (!names.includes(name)) names.push(name);
        };
        if (!only) {
            for (const hypothesis of node.hypotheses) {
                if (hypothesis.proposition && this.isHypothesisAvailable(hypothesis)
                    && this.simplifyDirection(hypothesis.proposition) !== null) addName(hypothesis.name);
            }
            this.fs.inferencePages.page(this.pageId)?.propositions.forEach((proposition, index) => {
                if (this.simplifyDirection(proposition.value) !== null) addName(`p${index}`);
            });
        }
        specified.forEach(addName);

        const sources = names.map(name => {
            const current = this.requireCurrentNode();
            const source = this.resolveSource(name, current);
            if (source.kind === "rule") {
                throw new Error(TR("simp目前只支持假设或页面等式；请先用have实例化推理规则"));
            }
            const equality = this.getSourceProposition(source, current);
            const reverse = this.simplifyDirection(equality);
            if (reverse === null) throw new Error(TR("simp来源必须是两端不同的等式：") + name);
            return { name, reverse };
        });

        let changed = false;
        const maxRounds = 64;
        for (let round = 0; round < maxRounds; round++) {
            let roundChanged = false;
            for (const source of sources) {
                const current = this.requireCurrentNode();
                const resolved = this.resolveSource(source.name, current);
                const equality = this.getSourceProposition(resolved, current);
                const left = source.reverse ? equality.nodes?.[1] : equality.nodes?.[0];
                const right = source.reverse ? equality.nodes?.[0] : equality.nodes?.[1];
                if (!left || !right) continue;
                try {
                    if (!this.planRewrite(current.target, left, right, null).length) continue;
                } catch {
                    continue;
                }
                this.rewriteWithSource(source.name, source.reverse, null);
                changed = true;
                roundChanged = true;
            }
            if (!roundChanged) break;
            if (round === maxRounds - 1) throw new Error(TR("simp达到最大化简轮次，可能存在循环规则"));
        }
        const current = this.requireCurrentNode();
        if (this.isReflexiveEqualityTarget(current.target) && this.resolveStrategyRule("a7")) {
            this.rfl("");
            return;
        }
        if (!changed && sources.length) return;
    }

    private parseRewriteSource(value: string): { source: string; reverse: boolean } {
        let source = value.trim();
        let reverse = false;
        if (source.startsWith("←")) {
            reverse = true;
            source = source.slice(1).trim();
        } else if (source.startsWith("<-")) {
            reverse = true;
            source = source.slice(2).trim();
        }
        if (!source || /\s/.test(source)) throw new Error(TR("rw等式来源应为一个假设或页面命题名称"));
        return { source, reverse };
    }

    /** True means use the equality right-to-left; null means it is not a simp rule. */
    private simplifyDirection(equality: AST): boolean | null {
        if (equality.type !== "sym" || equality.name !== "=" || equality.nodes?.length !== 2) return null;
        const [left, right] = equality.nodes;
        if (astmgr.equal(left, right)) return null;
        const leftSize = this.astSize(left);
        const rightSize = this.astSize(right);
        if (leftSize !== rightSize) return rightSize > leftSize;
        const leftText = parser.stringifyTight(left);
        const rightText = parser.stringifyTight(right);
        return rightText > leftText;
    }

    private astSize(ast: AST): number {
        return 1 + (ast.nodes?.reduce((total, child) => total + this.astSize(child), 0) ?? 0);
    }

    private canRewriteTarget(target: AST, equality: AST, reverse: boolean,
        available = this.availableRuleNames): boolean {
        if (!this.resolveStrategyRule("a8", available)) return false;
        if (!reverse && !this.resolveStrategyRule(".=s", available)) return false;
        if (equality.type !== "sym" || equality.name !== "=" || equality.nodes?.length !== 2) return false;
        const source = reverse ? equality.nodes[1] : equality.nodes[0];
        const destination = reverse ? equality.nodes[0] : equality.nodes[1];
        try {
            return this.planRewrite(target, source, destination, null).length > 0;
        } catch {
            return false;
        }
    }

    private rewriteWithSource(sourceText: string, reverse: boolean, nth: number | null): void {
        const node = this.requireCurrentNode();
        const source = this.resolveSource(sourceText, node);
        if (source.kind === "rule") {
            throw new Error(TR("rw目前只支持假设或页面等式；请先用have实例化推理规则"));
        }
        const equality = this.getSourceProposition(source, node);
        if (equality.type !== "sym" || equality.name !== "=" || equality.nodes?.length !== 2) {
            throw new Error(TR("rw来源必须是等式"));
        }
        const sourceTerm = reverse ? equality.nodes[1] : equality.nodes[0];
        const destinationTerm = reverse ? equality.nodes[0] : equality.nodes[1];
        const substitution = this.resolveStrategyRule("a8");
        if (!substitution) throw new Error(TR("rw需要解锁等式替换规则或提供等价推理规则"));
        const symmetry = reverse ? undefined : this.resolveStrategyRule(".=s");
        if (!reverse && !symmetry) throw new Error(TR("rw正向改写需要解锁等式对称规则或提供等价推理规则"));
        const steps = this.planRewrite(node.target, sourceTerm, destinationTerm, nth);

        for (const step of steps) {
            const current = this.requireCurrentNode();
            this.assertSameProposition(current.target, step.before);
            const srcMeta = substitution.metavariables.get("$0") ?? "$0";
            const dstMeta = substitution.metavariables.get("$1") ?? "$1";
            const propositionMeta = substitution.metavariables.get("$2") ?? "$2";
            const nthMeta = substitution.metavariables.get("$3") ?? "$3";
            const inverseSource = parser.stringifyTight(destinationTerm);
            const inverseDestination = parser.stringifyTight(sourceTerm);
            const rewrittenTarget = parser.stringifyTight(step.after);
            this.applyRule(`${substitution.name} ${srcMeta}=${inverseSource} ${dstMeta}=${inverseDestination} `
                + `${propositionMeta}=${rewrittenTarget} ${nthMeta}=${step.inverseNth}`);
            if (reverse) {
                this.exact(sourceText);
            } else {
                this.applyRule(symmetry!.name);
                this.exact(sourceText);
            }
            this.assertSameProposition(this.requireCurrentNode().target, step.after);
        }
    }

    private planRewrite(target: AST, source: AST, destination: AST, nth: number | null): RewriteStep[] {
        if (astmgr.equal(source, destination)) throw new Error(TR("rw等式两端相同，没有可执行的改写"));
        const probe = astmgr.clone(target);
        const allMatches = this.fs.assert.getSubAstMatchTimesAndReplace(
            probe, astmgr.clone(source), astmgr.clone(destination), -1, [], [], false
        );
        if (allMatches === false) throw new Error(TR("rw无法确认替换是否会捕获变量"));
        if (!allMatches.length) throw new Error(TR("当前目标中未找到可改写项"));
        if (nth !== null && nth > allMatches.length) {
            throw new Error(TR("nth_rw序号超出匹配数量：") + allMatches.length);
        }
        const indexes = nth === null
            ? Array.from({ length: allMatches.length }, (_, index) => allMatches.length - index - 1)
            : [nth - 1];
        let current = astmgr.clone(target);
        const steps: RewriteStep[] = [];
        for (const index of indexes) {
            const before = astmgr.clone(current);
            const after = astmgr.clone(current);
            const matches = this.fs.assert.getSubAstMatchTimesAndReplace(
                after, astmgr.clone(source), astmgr.clone(destination), index, [], [], false
            );
            if (matches === false || matches.length <= index || astmgr.equal(before, after)) {
                throw new Error(TR("rw未能替换指定出现位置"));
            }
            const inverseNth = this.findInverseRewriteOccurrence(before, after, destination, source);
            steps.push({ before, after, inverseNth });
            current = after;
        }
        return steps;
    }

    private findInverseRewriteOccurrence(before: AST, after: AST, source: AST, destination: AST): number {
        const probe = astmgr.clone(after);
        const matches = this.fs.assert.getSubAstMatchTimesAndReplace(
            probe, astmgr.clone(source), astmgr.clone(destination), -1, [], [], false
        );
        if (matches === false) throw new Error(TR("rw无法构造反向替换证明"));
        for (let index = 0; index < matches.length; index++) {
            const candidate = astmgr.clone(after);
            const result = this.fs.assert.getSubAstMatchTimesAndReplace(
                candidate, astmgr.clone(source), astmgr.clone(destination), index, [], [], false
            );
            if (result !== false && result.length > index && astmgr.equal(candidate, before)) return index + 1;
        }
        throw new Error(TR("rw无法定位可还原原目标的替换位置"));
    }

    /** Derive any target from a matching proposition/negation pair. */
    private contradiction(argument: string): void {
        if (argument.trim()) throw new Error(TR("contradiction不接受参数"));
        const node = this.requireCurrentNode();
        const pair = this.findContradictionPair(node);
        if (!pair) throw new Error(TR("未找到相反命题假设"));
        const rule = this.resolveStrategyRule(".m");
        if (!rule) throw new Error(TR("contradiction需要解锁矛盾规则或提供等价推理规则"));
        const proposition = parser.stringifyTight(pair.proposition);
        const metavariable = rule.metavariables.get("$0") ?? "$0";
        this.applyRule(`${rule.name} ${metavariable}=${proposition}`);
        this.exact(pair.positiveName);
        this.exact(pair.negativeName);
    }

    /** Start classical reductio using (~P -> P) -> P, then name ~P. */
    private byContra(argument: string): void {
        const node = this.requireCurrentNode();
        const name = argument.trim();
        if (name && !/^[^\s,]+$/.test(name)) throw new Error(TR("by_contra名称无效"));
        const rule = this.resolveStrategyRule(".mn");
        if (!rule) throw new Error(TR("by_contra需要解锁反证规则或提供等价推理规则"));
        const originalTarget = parser.stringifyTight(node.target);
        this.applyRule(rule.name);
        const implication = this.requireCurrentNode().target;
        if (implication.type !== "sym" || implication.name !== ">" || implication.nodes?.length !== 2) {
            throw new Error(TR("反证规则没有生成预期的蕴含目标"));
        }
        this.intro(name);
        const current = this.requireCurrentNode();
        if (parser.stringifyTight(current.target) !== originalTarget) {
            throw new Error(TR("反证规则生成的目标与原目标不一致"));
        }
    }

    /** Split the current target into P and ~P branches through case analysis. */
    private byCases(argument: string): void {
        const match = /^([^\s,:=]+)\s*:\s*([\s\S]+)$/.exec(argument.trim());
        if (!match) throw new Error(TR("by_cases语法应为 by_cases h : P"));
        const name = match[1];
        const proposition = this.parseProposition(match[2]);
        const node = this.requireCurrentNode();
        this.assertUniqueHypothesis(node, name);
        const rule = this.resolveStrategyRule(".m2");
        if (!rule) throw new Error(TR("by_cases需要解锁分类讨论规则或提供等价推理规则"));
        const propositionMeta = rule.metavariables.get("$0") ?? "$0";
        const targetMeta = rule.metavariables.get("$1") ?? "$1";
        this.applyRule(`${rule.name} ${propositionMeta}=${parser.stringifyTight(proposition)} `
            + `${targetMeta}=${parser.stringifyTight(node.target)}`);
        if (node.kind !== "apply" || node.children.length !== 2 || node.ruleConditionCount !== 2) {
            throw new Error(TR("分类讨论规则没有生成预期的两个分支"));
        }
        this.introNode(node.children[0], name);
        this.introNode(node.children[1], name);
    }

    /** Replace A -> B with its classical contrapositive ~B -> ~A. */
    private contrapose(argument: string): void {
        if (argument.trim()) throw new Error(TR("contrapose不接受参数"));
        const node = this.requireCurrentNode();
        if (node.target.type !== "sym" || node.target.name !== ">" || node.target.nodes?.length !== 2) {
            throw new Error(TR("contrapose只能作用于蕴含目标"));
        }
        const rule = this.resolveStrategyRule("a3");
        if (!rule) throw new Error(TR("contrapose需要解锁逆否规则或提供等价推理规则"));
        this.applyRule(rule.name);
    }

    private applyRule(argument: string): void {
        const node = this.requireCurrentNode();
        const parts = argument.trim() ? argument.trim().split(/\s+/) : [];
        if (!parts.length) throw new Error(TR("apply需要一个证明来源或推理规则"));
        const sourceName = parts.shift();
        if (sourceName === "_") throw new Error(TR("推理层证明助手暂不支持_模糊匹配"));
        const source = this.resolveSource(sourceName, node);
        if (source.kind === "rule") {
            const deduction = this.requireDeduction(source.name);
            const explicit = this.parseRuleArguments(parts, deduction);
            const application = this.matchRuleApplication(deduction, node.target, explicit, node);
            this.assertRuleMatchComplete(application, source.name);
            const matchTable = application.matchTable;
            const implicationPremises = application.premises;
            const replaceValues = deduction.replaceNames.map(name => {
                const value = matchTable[application.context.internalByOriginal.get(name)!];
                if (!value) throw new Error(TR("无法从目标推断规则参数") + name);
                return astmgr.clone(value);
            });
            const instantiate = (value: AST) => {
                const result = this.instantiateRuleAst(value, application.context, matchTable);
                if (this.astContainsFunction(result, "#rp")) this.fs.assert.expand(result, false);
                this.fs.assert.checkGrammer(result, "p");
                return result;
            };
            const conditions = [
                ...application.context.conditions,
                ...implicationPremises.map(condition => this.renameRuleMetavariables(
                    astmgr.clone(condition), application.context.internalByOriginal
                ))
            ].map(condition => {
                return instantiate(condition);
            });
            node.kind = "apply";
            node.source = source;
            node.ruleName = source.name;
            node.replaceValues = replaceValues;
            node.appliedProposition = instantiate(deduction.conclusion);
            node.ruleConditionCount = deduction.conditions.length;
            node.children = conditions.map(condition => this.makeNode(condition, this.cloneHypotheses(node.hypotheses)));
            return;
        }

        if (parts.length) throw new Error(TR("对假设或定理使用apply时不能附加参数"));
        const proposition = this.getSourceProposition(source, node);
        const application = this.matchPropositionApplication(proposition, node.target);
        const matchTable = application.matchTable;
        const appliedProposition = astmgr.clone(proposition);
        astmgr.replaceByMatchTable(appliedProposition, matchTable);
        const instantiatedPremises = application.premises.map(premise => {
            const result = astmgr.clone(premise);
            astmgr.replaceByMatchTable(result, matchTable);
            return result;
        });
        if (!instantiatedPremises.length) {
            this.assertSameProposition(appliedProposition, node.target);
            node.kind = "exact";
            node.source = source;
            node.ruleName = undefined;
            node.replaceValues = undefined;
            node.appliedProposition = undefined;
            node.ruleConditionCount = undefined;
            node.children = [];
            return;
        }
        node.kind = "apply";
        node.source = source;
        node.ruleName = undefined;
        node.replaceValues = undefined;
        node.appliedProposition = appliedProposition;
        node.ruleConditionCount = 0;
        node.children = instantiatedPremises.map(condition => this.makeNode(condition, this.cloneHypotheses(node.hypotheses)));
    }

    private have(argument: string): void {
        const node = this.requireCurrentNode();
        const value = argument.trim();
        if (!value) throw new Error(TR("have需要命题和名称，例如have $0 h233"));

        // Lean-style inferred declaration: `have h := source arg...`.  This
        // creates an immediately available fact by specializing universal
        // quantifiers of a local/page proposition; it does not open a proof
        // subgoal.
        const assignment = /^([^\s,:=]+)\s*:=\s*([\s\S]+)$/.exec(value);
        if (assignment) {
            const name = assignment[1];
            this.assertUniqueHypothesis(node, name);
            const terms = this.splitApplicationTerms(assignment[2]);
            if (!terms.length) throw new Error(TR("have := 需要一个局部或页面命题来源"));
            const source = this.resolveSource(terms.shift()!, node);
            if (source.kind === "rule") {
                throw new Error(TR("have := 只支持局部或页面命题，不支持推理规则"));
            }
            const sourceProposition = this.getSourceProposition(source, node);
            const args = terms.map(term => this.parsePropositionOrItem(term));
            const proposition = this.instantiateUniversalApplication(sourceProposition, args);
            this.fs.assert.checkGrammer(proposition, "p");
            const continuationHypotheses = this.cloneHypotheses(node.hypotheses);
            continuationHypotheses.push({
                name,
                proposition: astmgr.clone(proposition),
                kind: "have"
            });
            const continuation = this.makeNode(node.target, continuationHypotheses);
            node.kind = "haveApply";
            node.haveName = name;
            node.haveSource = this.cloneSource(source);
            node.haveArguments = args.map(arg => astmgr.clone(arg));
            node.haveProposition = astmgr.clone(proposition);
            node.children = [continuation];
            return;
        }

        // Lean-style declaration: `have h : proposition`.  Requiring a
        // whitespace-separated name keeps the legacy `have Vx:P(x) h` form
        // unambiguous, since colons are part of quantified propositions.
        const declaration = /^([^\s,:=]+)\s+:\s*([\s\S]+)$/.exec(value);
        if (declaration) {
            const name = declaration[1];
            this.assertUniqueHypothesis(node, name);
            const proposition = this.parseProposition(declaration[2]);
            this.createHaveGoal(node, name, proposition);
            return;
        }

        // Legacy form: `have proposition name`.
        const parts = value.split(/\s+/);
        if (parts.length < 2) throw new Error(TR("have需要命题和名称，例如have $0 h233"));
        const name = parts.pop()!;
        if (!/^[^\s,]+$/.test(name)) throw new Error(TR("have名称无效"));
        this.assertUniqueHypothesis(node, name);
        const proposition = this.parseProposition(parts.join(" "));
        this.createHaveGoal(node, name, proposition);
    }

    private createHaveGoal(node: DraftNode, name: string, proposition: AST): void {
        const subgoal = this.makeNode(proposition, this.cloneHypotheses(node.hypotheses));
        const continuationHypotheses = this.cloneHypotheses(node.hypotheses);
        continuationHypotheses.push({ name, proposition: astmgr.clone(proposition), kind: "have", sourceNodeId: subgoal.id });
        const continuation = this.makeNode(node.target, continuationHypotheses);
        node.kind = "have";
        node.haveName = name;
        node.children = [subgoal, continuation];
    }

    /** Split conjunction/equivalence facts into two materializable local facts. */
    private obtain(argument: string): void {
        const branchMatch = /^([^\s|,:=]+)\s*\|\s*([^\s|,:=]+)\s*:=\s*([\s\S]+)$/.exec(argument.trim());
        if (branchMatch) {
            this.obtainDisjunction(branchMatch[1], branchMatch[2], branchMatch[3].trim());
            return;
        }
        const match = /^(?:<|⟨)\s*([^,\s<>⟩]+)\s*,\s*([^,\s<>⟩]+)\s*(?:>|⟩)\s*:=\s*([\s\S]+)$/.exec(argument.trim());
        if (!match) throw new Error(TR("obtain语法应为 obtain <h1,h2> := h"));
        const [, firstName, secondName, sourceTextValue] = match;
        const sourceText = sourceTextValue.trim();
        if (!sourceText) throw new Error(TR("obtain需要一个假设或页面命题来源"));
        if (firstName === secondName) throw new Error(TR("obtain生成的两个假设名称不能相同"));

        const node = this.requireCurrentNode();
        this.assertUniqueHypothesis(node, firstName);
        this.assertUniqueHypothesis(node, secondName);
        const source = this.resolveSource(sourceText, node);
        if (source.kind === "rule") throw new Error(TR("obtain只支持假设或页面命题来源"));
        const proposition = this.getSourceProposition(source, node);
        if (proposition.type !== "sym" || proposition.nodes?.length !== 2) {
            throw new Error(TR("obtain来源必须是合取、等价或析取命题"));
        }

        let facts: [AST, string][];
        if (proposition.name === "&") {
            facts = [[proposition.nodes[0], ".&1"], [proposition.nodes[1], ".&2"]];
        } else if (proposition.name === "<>") {
            facts = [
                [parser.parse(`${parser.stringifyTight(proposition.nodes[0])}>${parser.stringifyTight(proposition.nodes[1])}`), ".<>1"],
                [parser.parse(`${parser.stringifyTight(proposition.nodes[1])}>${parser.stringifyTight(proposition.nodes[0])}`), ".<>2"]
            ];
        } else if (proposition.name === "|") {
            throw new Error(TR("析取obtain语法应为 obtain h1 | h2 := h"));
        } else {
            throw new Error(TR("obtain来源必须是合取、等价或析取命题"));
        }

        for (const [index, [fact, canonicalRule]] of facts.entries()) {
            const rule = this.resolveStrategyRule(canonicalRule);
            if (!rule) throw new Error(TR("obtain需要解锁消去规则或提供等价推理规则：") + canonicalRule);
            const current = this.requireCurrentNode();
            this.createHaveGoal(current, index === 0 ? firstName : secondName, astmgr.clone(fact));
            this.applyRule(rule.name);
            this.exact(sourceText);
        }
    }

    private obtainDisjunction(firstName: string, secondName: string, sourceText: string): void {
        if (!sourceText) throw new Error(TR("obtain需要一个假设或页面命题来源"));
        const node = this.requireCurrentNode();
        this.assertUniqueHypothesis(node, firstName);
        this.assertUniqueHypothesis(node, secondName);
        const source = this.resolveSource(sourceText, node);
        if (source.kind === "rule") throw new Error(TR("obtain只支持假设或页面命题来源"));
        const proposition = this.getSourceProposition(source, node);
        if (proposition.type !== "sym" || proposition.name !== "|" || proposition.nodes?.length !== 2) {
            throw new Error(TR("分支obtain来源必须是析取命题"));
        }
        const rule = this.resolveStrategyRule(".|m");
        if (!rule) throw new Error(TR("obtain需要解锁析取消去规则或提供等价推理规则：.|m"));
        const leftMeta = rule.metavariables.get("$0") ?? "$0";
        const rightMeta = rule.metavariables.get("$1") ?? "$1";
        const resultMeta = rule.metavariables.get("$2") ?? "$2";
        const left = parser.stringifyTight(proposition.nodes[0]);
        const right = parser.stringifyTight(proposition.nodes[1]);
        const result = parser.stringifyTight(node.target);
        this.applyRule(`${rule.name} ${leftMeta}=${left} ${rightMeta}=${right} ${resultMeta}=${result}`);
        if (node.kind !== "apply" || node.children.length !== 3 || node.ruleConditionCount !== 2) {
            throw new Error(TR("析取消去规则没有生成预期的两个分支和来源前提"));
        }
        this.introNode(node.children[0], firstName);
        this.introNode(node.children[1], secondName);
        const sourceGoal = node.children[2];
        this.assertSameProposition(this.getSourceProposition(source, sourceGoal), sourceGoal.target);
        sourceGoal.kind = "exact";
        sourceGoal.source = this.cloneSource(source);
        sourceGoal.children = [];
    }

    /** Move a proposition hypothesis back into the current implication target. */
    private revert(argument: string): void {
        const name = argument.trim();
        if (!name || !/^[^\s,]+$/.test(name)) throw new Error(TR("revert需要一个假设名称"));
        const node = this.requireCurrentNode();
        const hypothesis = node.hypotheses.find(item => item.name === name);
        if (!hypothesis) throw new Error(TR("未找到要恢复的假设：") + name);
        if (!hypothesis.proposition) throw new Error(TR("revert暂不支持全称变量：") + name);
        if (hypothesis.kind === "have" && !this.isHypothesisAvailable(hypothesis)) {
            throw new Error(TR("该假设尚未完成"));
        }
        const childTarget: AST = {
            type: "sym",
            name: ">",
            nodes: [astmgr.clone(hypothesis.proposition), astmgr.clone(node.target)]
        };
        const child = this.makeNode(childTarget,
            this.cloneHypotheses(node.hypotheses.filter(item => item.name !== name)));
        node.kind = "revert";
        node.revertSource = { kind: "hypothesis", name, nodeId: hypothesis.sourceNodeId };
        node.children = [child];
    }

    private splitApplicationTerms(value: string): string[] {
        const terms: string[] = [];
        let current = "";
        let depth = 0;
        const push = () => {
            const term = current.trim();
            if (term) terms.push(term);
            current = "";
        };
        for (const char of value) {
            if (/\s/.test(char) && depth === 0) {
                push();
                continue;
            }
            current += char;
            if (["(", "{", "["].includes(char)) depth++;
            else if ([")", "}", "]"].includes(char)) depth = Math.max(0, depth - 1);
        }
        push();
        return terms;
    }

    private instantiateUniversalApplication(proposition: AST, args: AST[]): AST {
        let result = astmgr.clone(proposition);
        for (const argument of args) {
            if (result.type !== "sym" || result.name !== "V" || result.nodes?.length !== 2) {
                throw new Error(TR("have应用参数过多，来源命题不是足够的全称命题"));
            }
            const binderName = this.fs.assert.getVarName(result.nodes[0]);
            if (!binderName) throw new Error(TR("have来源命题的全称量词变量无效"));
            result = this.substituteBoundValue(result.nodes[1], binderName, argument);
        }
        return result;
    }

    private tauto(argument: string): void {
        if (argument.trim()) throw new Error(TR("tauto不接受参数"));
        if (!this.allowMcpt) throw new Error(TR("尚未解锁MCPT，不能使用tauto"));
        const node = this.requireCurrentNode();
        // Keep MCPT's exhaustive check as the authority.  Do not add a
        // generated rule here: applying a tactic is a draft-only operation and
        // must not mutate the shared FormalSystem.  The deferred rule is
        // created transactionally by commit() when the result is accepted.
        const name = this.nextTautoName(node.target);
        new Proof(this.fs).assertTautology(node.target);
        node.kind = "tauto";
        node.tautoName = name;
        node.children = [];
    }

    private nextTautoName(target?: AST): string {
        // Replays of a persisted assistant proof should bind to the same
        // deferred CPT helper instead of allocating a fresh name on every
        // expansion.
        if (target) {
            for (const [name, deduction] of Object.entries(this.fs.deductions)) {
                if (!name.startsWith("__tauto_") || deduction.deferredKind !== "cpt") continue;
                try {
                    this.assertSameProposition(deduction.conclusion, target);
                    return name;
                } catch { }
            }
        }
        let index = 1;
        // The helper is not added to the GUI's deduction list.  It remains in
        // the formal-system map so a page row can be validated after reload;
        // its deferred CPT payload contains no enumeration steps.
        while (this.fs.deductions[`__tauto_${index}`] || this.hasTautoName(this.root, `__tauto_${index}`)) index++;
        return `__tauto_${index}`;
    }

    private hasTautoName(node: DraftNode | null, name: string): boolean {
        if (!node) return false;
        if (node.tautoName === name) return true;
        return node.children.some(child => this.hasTautoName(child, name));
    }

    private fastMetaRuleLabel(prefix: string): string {
        return ({
            ">": "演绎元定理",
            "<": "逆演绎元定理",
            "c": "条件演绎元定理",
            "v": "条件概括元定理",
            "u": "概括元定理",
            "e": "特称元定理",
            ":": "组合元定理"
        } as Record<string, string>)[prefix] ?? (TR("元定理") + prefix);
    }

    private generatedLiteralRuleAvailable(name: string): boolean {
        const fast = this.availableFastMetaRules ?? this.fs.fastmetarules;
        const oldFastMetaRules = this.fs.fastmetarules;
        try {
            this.fs.fastmetarules = fast;
            if (name.startsWith(".")) {
                return !!(
                    (fast.includes("#")
                        && (this.fs.generateNatLiteralOp(name) || this.fs.generateNatLiteralIsNat(name)))
                    || (fast.includes("Z")
                        && (this.fs.generateZLiteralIsZ(name) || this.fs.generateZLiteralOp(name)))
                );
            }
            if (name.startsWith("a") || name.startsWith("d")) {
                return !!(
                    (fast.includes("#") && this.fs.generateNatLiteralDef(name))
                    || (fast.includes("z") && this.fs.generateZLiteralDef(name))
                    || (fast.includes("R") && this.fs.generateRLiteralDef(name))
                    || (fast.includes("Q") && this.fs.generateQLiteralDef(name))
                );
            }
            return false;
        } finally {
            this.fs.fastmetarules = oldFastMetaRules;
        }
    }

    private deductionTreeAccess(tree: any): DeductionAccess {
        if (!Array.isArray(tree) || !tree.length) return { allowed: false, kind: "rule", name: "" };
        if (tree.length === 1) {
            const name = String(tree[0]);
            if (name === "#" || !this.availableRuleNames || this.availableRuleNames.has(name)
                || this.generatedLiteralRuleAvailable(name)) {
                return { allowed: true };
            }
            return { allowed: false, kind: "rule", name };
        }

        const prefix = String(tree[0]);
        const unlocked = this.availableFastMetaRules === undefined
            || this.availableFastMetaRules.includes(prefix)
            || (prefix === "v" && this.availableFastMetaRules.includes("q"));
        if (!["<", ">", "c", "e", "v", "u", ":"].includes(prefix) || !unlocked) {
            return { allowed: false, kind: "metarule", name: prefix };
        }
        for (const child of tree.slice(1)) {
            const access = this.deductionTreeAccess(child);
            if (!access.allowed) return access;
        }
        return { allowed: true };
    }

    private assertRuleNameMetaPrefixesAvailable(name: string, generated: boolean): void {
        if (this.availableFastMetaRules === undefined) return;
        let tree: any;
        try {
            tree = this.fs.getDeductionTokens(name);
        } catch {
            return;
        }
        const visit = (value: any): void => {
            if (!Array.isArray(value) || value.length <= 1) return;
            const prefix = String(value[0]);
            if (["<", ">", "c", "e", "v", "u", ":"].includes(prefix)) {
                const unlocked = this.availableFastMetaRules!.includes(prefix)
                    || (prefix === "v" && this.availableFastMetaRules!.includes("q"));
                if (!unlocked) {
                    const lead = generated ? TR("自动生成证明步骤需要解锁") : TR("尚未解锁");
                    throw new Error(lead + this.fastMetaRuleLabel(prefix) + "：" + name);
                }
            }
            value.slice(1).forEach(visit);
        };
        visit(tree);
    }

    private assertGeneratedDeductionMetaRules(name: string, existingNames: Set<string>,
        visited = new Set<string>()): void {
        if (this.availableFastMetaRules === undefined || visited.has(name)) return;
        visited.add(name);
        this.assertRuleNameMetaPrefixesAvailable(name, true);
        let generatedExpression = false;
        try {
            generatedExpression = this.fs.getDeductionTokens(name)?.length > 1;
        } catch { }
        if (existingNames.has(name) && !generatedExpression) return;
        const deduction = this.fs.deductions[name];
        deduction?.steps?.forEach(step => {
            this.assertRuleNameMetaPrefixesAvailable(step.deductionIdx, true);
            this.assertGeneratedDeductionMetaRules(step.deductionIdx, existingNames, visited);
        });
    }

    /** Enumerate a bounded prefix search space without making unlock guesses. */
    private generatedRuleCandidates(baseName: string, prefixes: string[], maxDepth = 2): string[] {
        const candidates = [baseName];
        let frontier = [baseName];
        const seen = new Set(candidates);
        for (let depth = 0; depth < maxDepth; depth++) {
            const next: string[] = [];
            for (const current of frontier) {
                for (const prefix of prefixes) {
                    if (!this.canUseFastMetaRule(prefix)) continue;
                    const candidate = prefix + current;
                    if (seen.has(candidate)) continue;
                    seen.add(candidate);
                    next.push(candidate);
                    candidates.push(candidate);
                }
            }
            frontier = next;
            if (!frontier.length) break;
        }
        return candidates;
    }

    private generatedDeductionCost(name: string, visiting = new Set<string>()): number {
        const deduction = this.fs.deductions[name];
        if (!deduction) return Number.POSITIVE_INFINITY;
        if (visiting.has(name)) return Number.POSITIVE_INFINITY;
        if (!deduction.steps?.length) return 1;
        const next = new Set(visiting);
        next.add(name);
        let cost = 1;
        for (const step of deduction.steps) {
            const child = this.generatedDeductionCost(step.deductionIdx, next);
            if (!Number.isFinite(child)) return Number.POSITIVE_INFINITY;
            cost += child;
        }
        return cost;
    }

    private selectGeneratedRule(baseName: string, target: AST, expectedConditions: AST[],
        prefixes: string[], explicitValues: AST[] = []): GeneratedRuleSelection | undefined {
        const oldFastMetaRules = this.fs.fastmetarules;
        const existingNames = new Set(Object.keys(this.fs.deductions));
        const candidates: GeneratedRuleSelection[] = [];
        try {
            this.fs.fastmetarules = this.availableFastMetaRules ?? "cvuqe><:#zZQR";
            for (const candidateName of this.generatedRuleCandidates(baseName, prefixes)) {
                let deduction: Deduction | undefined;
                try {
                    deduction = this.fs.deductions[candidateName] ?? this.fs.generateDeduction(candidateName);
                    if (!deduction) continue;
                    this.assertGeneratedDeductionMetaRules(candidateName, existingNames);
                    const match = this.matchConclusion(
                        deduction,
                        target,
                        { positional: explicitValues.map(value => astmgr.clone(value)), named: new Map() },
                        deduction.conclusion,
                        undefined,
                        undefined,
                        undefined,
                        expectedConditions
                    );
                    this.assertRuleMatchComplete(match, candidateName);
                    const instantiate = (value: AST) => {
                        const result = this.instantiateRuleAst(value, match.context, match.matchTable);
                        if (this.astContainsFunction(result, "#rp")) this.fs.assert.expand(result, false);
                        this.fs.assert.checkGrammer(result, "p");
                        return result;
                    };
                    const conditions = deduction.conditions.map(instantiate);
                    if (conditions.length !== expectedConditions.length
                        || conditions.some((condition, index) => {
                            try {
                                this.assertSameProposition(condition, expectedConditions[index]);
                                return false;
                            } catch {
                                return true;
                            }
                        })) continue;
                    const replaceValues = deduction.replaceNames.map(name => {
                        const value = match.matchTable[match.context.internalByOriginal.get(name)!];
                        if (!value) throw new Error(TR("无法从自动生成规则推断参数：") + name);
                        return astmgr.clone(value);
                    });
                    candidates.push({ name: candidateName, deduction, replaceValues });
                } catch {
                    // Invalid candidates are expected during bounded search.
                }
            }
        } finally {
            this.fs.fastmetarules = oldFastMetaRules;
        }
        candidates.sort((left, right) => {
            const cost = this.generatedDeductionCost(left.name) - this.generatedDeductionCost(right.name);
            if (cost !== 0) return cost;
            return left.name.length - right.name.length;
        });
        return candidates[0];
    }

    private resolveVisibleDeduction(name: string): Deduction | undefined {
        let tree: any;
        try {
            tree = this.fs.getDeductionTokens(name);
        } catch {
            return undefined;
        }
        const access = this.deductionTreeAccess(tree);
        if ("kind" in access) {
            if (access.kind === "metarule") {
                throw new Error(TR("尚未解锁") + this.fastMetaRuleLabel(access.name) + "：" + name);
            }
            if (!this.fs.deductions[access.name]) return undefined;
            throw new Error(TR("推理规则不在当前证明助手作用域：") + access.name);
        }

        const oldFastMetaRules = this.fs.fastmetarules;
        const existingNames = new Set(Object.keys(this.fs.deductions));
        try {
            if (this.availableFastMetaRules !== undefined) {
                this.fs.fastmetarules = this.availableFastMetaRules;
            }
            const deduction = this.fs.deductions[name] ?? this.fs.generateDeduction(name);
            if (deduction) this.assertGeneratedDeductionMetaRules(name, existingNames);
            return deduction;
        } finally {
            this.fs.fastmetarules = oldFastMetaRules;
        }
    }

    private requireCurrentNode(): DraftNode {
        const current = this.openNodes()[0];
        if (!current) throw new Error(TR("无证明目标，请使用qed命令结束证明"));
        return current;
    }

    private resolveSource(argument: string, node: DraftNode): SourceRef {
        const local = node.hypotheses.find(h => h.name === argument);
        if (local) return { kind: "hypothesis", name: argument, nodeId: local.sourceNodeId };
        // A `have` fact is introduced into the continuation branch only after
        // its proof is complete.  Still resolve its name while the subgoal is
        // active so the user receives the actionable "尚未完成" diagnostic
        // instead of an unrelated unknown-source error.
        const pendingHave = this.findPendingHaveForNode(node, argument);
        if (pendingHave) return { kind: "hypothesis", name: argument, nodeId: pendingHave.sourceNodeId };
        const pageMatch = /^p([0-9]+)$/.exec(argument);
        if (pageMatch) {
            const index = Number(pageMatch[1]);
            if (!this.fs.inferencePages.page(this.pageId)?.propositions[index]) throw new Error(TR("定理不存在"));
            return { kind: "page", index, pageId: this.pageId };
        }
        // A proposition may be referred to by its surface expression rather
        // than by pN.  Resolve it only against the selected page; this keeps
        // page-local scope intact and still lets users write `exact A` instead
        // of locating the corresponding proposition number.
        try {
            const expression = this.parseProposition(argument);
            const page = this.fs.inferencePages.page(this.pageId);
            const index = page?.propositions.findIndex(proposition => {
                try {
                    this.assertSameProposition(proposition.value, expression);
                    return true;
                } catch {
                    return false;
                }
            }) ?? -1;
            if (index >= 0) return { kind: "page", index, pageId: this.pageId };
        } catch {
            // Not a proposition expression; continue with shared-rule lookup.
        }
        const existing = this.resolveVisibleDeduction(argument);
        if (existing) return { kind: "rule", name: argument, replaceValues: [] };
        throw new Error(TR("未找到证明来源") + argument);
    }

    private getSourceProposition(source: SourceRef, node: DraftNode): AST {
        if (source.kind === "hypothesis") {
            const hypothesis = node.hypotheses.find(item => item.name === source.name)
                ?? this.findPendingHaveForNode(node, source.name);
            if (!hypothesis) throw new Error(TR("未找到证明来源") + source.name);
            if (hypothesis.kind === "have" && !this.isHypothesisAvailable(hypothesis)) {
                throw new Error(TR("该假设尚未完成"));
            }
            if (!hypothesis.proposition) throw new Error(TR("全称变量不能作为命题证明来源：") + source.name);
            return astmgr.clone(hypothesis.proposition);
        }
        if (source.kind === "page") {
            const proposition = this.fs.inferencePages.page(source.pageId)?.propositions[source.index];
            if (!proposition) throw new Error(TR("定理不存在"));
            return astmgr.clone(proposition.value);
        }
        return astmgr.clone(this.requireDeduction(source.name).conclusion);
    }

    private matchPropositionApplication(proposition: AST, target: AST): {
        premises: AST[];
        conclusion: AST;
        matchTable: ReplvarMatchTable;
    } {
        const premises: AST[] = [];
        let conclusion = proposition;
        let lastError: unknown = new Error(TR("证明来源结论与当前目标不匹配"));
        while (true) {
            try {
                return {
                    premises: premises.map(premise => astmgr.clone(premise)),
                    conclusion: astmgr.clone(conclusion),
                    matchTable: this.matchPropositionConclusion(proposition, conclusion, target)
                };
            } catch (error) {
                lastError = error;
            }
            if (conclusion.type !== "sym" || conclusion.name !== ">" || conclusion.nodes?.length !== 2) {
                throw lastError;
            }
            premises.push(astmgr.clone(conclusion.nodes[0]));
            conclusion = conclusion.nodes[1];
        }
    }

    private matchRuleApplication(deduction: Deduction, target: AST, explicit: RuleExplicitArguments,
        node?: DraftNode): RuleApplicationMatch {
        const context = this.createRuleMetavariableContext(deduction, target, explicit, node);
        const premises: AST[] = [];
        let conclusion = astmgr.clone(context.conclusion);
        let unresolvedMatch: RuleApplicationMatch | undefined;
        let lastError: unknown = new Error(TR("规则结论与当前目标不匹配"));
        while (true) {
            try {
                const match = this.matchConclusion(deduction, target, explicit, conclusion,
                    node, context, [...context.conditions, ...premises]);
                const application: RuleApplicationMatch = {
                    premises: premises.map(premise => astmgr.clone(premise)),
                    conclusion: astmgr.clone(conclusion),
                    context,
                    matchTable: match.matchTable,
                    unresolved: match.unresolved
                };
                if (!match.unresolved.length) return application;
                unresolvedMatch = application;
            } catch (error) {
                lastError = error;
            }
            if (conclusion.type !== "sym" || conclusion.name !== ">" || conclusion.nodes?.length !== 2) {
                if (unresolvedMatch) return unresolvedMatch;
                throw lastError;
            }
            premises.push(astmgr.clone(conclusion.nodes[0]));
            conclusion = conclusion.nodes[1];
        }
    }

    private matchPropositionConclusion(_proposition: AST, conclusion: AST, target: AST): ReplvarMatchTable {
        try {
            this.assertSameProposition(conclusion, target);
        } catch (error) {
            throw new Error(TR("证明来源结论与当前目标不匹配：") + error);
        }
        return {};
    }

    private fixedPropositionMayMatch(proposition: AST, target: AST): boolean {
        try {
            this.assertSameProposition(proposition, target);
            return true;
        } catch {
            return false;
        }
    }

    private findMatchingHypothesis(node: DraftNode): string | undefined {
        for (const hypothesis of node.hypotheses) {
            if (!hypothesis.proposition || !this.isHypothesisAvailable(hypothesis)) continue;
            if (this.fixedPropositionMayMatch(hypothesis.proposition, node.target)) return hypothesis.name;
        }
        return undefined;
    }

    private isConstructorTarget(target: AST): boolean {
        return target?.type === "sym" && (target.name === "&" || target.name === "<>")
            && target.nodes?.length === 2;
    }

    private isSymmetryTarget(target: AST): boolean {
        return target?.type === "sym" && (target.name === "=" || target.name === "<>")
            && target.nodes?.length === 2;
    }

    private isReflexiveEqualityTarget(target: AST): boolean {
        if (target?.type !== "sym" || target.name !== "=" || target.nodes?.length !== 2) return false;
        try {
            this.assertSameProposition(target.nodes[0], target.nodes[1]);
            return true;
        } catch {
            return false;
        }
    }

    private resolveStrategyRule(name: string, available = this.availableRuleNames): StrategyRuleResolution | undefined {
        const direct = this.fs.deductions[name];
        if ((!available || available.has(name)) && direct) {
            return {
                name,
                metavariables: new Map([
                    ["$0", "$0"],
                    ["$1", "$1"],
                    ["$2", "$2"],
                    ["$3", "$3"]
                ])
            };
        }
        const shape = this.strategyRuleShape(name);
        if (!shape) return undefined;
        for (const [candidateName, candidate] of Object.entries(this.fs.deductions)) {
            if (candidateName === name) continue;
            if (available && !available.has(candidateName)) continue;
            const metavariables = this.matchStrategyRuleSchema(candidate, shape);
            if (metavariables) return { name: candidateName, metavariables };
        }
        return undefined;
    }

    private strategyRuleShape(name: string): { conditions: AST[]; conclusion: AST } | undefined {
        switch (name) {
            case ".&":
                return { conditions: [parser.parse("$0"), parser.parse("$1")], conclusion: parser.parse("$0&$1") };
            case ".<>":
                return { conditions: [parser.parse("$0>$1"), parser.parse("$1>$0")], conclusion: parser.parse("$0<>$1") };
            case ".=s":
                return { conditions: [parser.parse("$0=$1")], conclusion: parser.parse("$1=$0") };
            case ".<>s":
                return { conditions: [parser.parse("$0<>$1")], conclusion: parser.parse("$1<>$0") };
            case ".m":
                return { conditions: [parser.parse("$0"), parser.parse("~$0")], conclusion: parser.parse("$1") };
            case ".|1":
                return { conditions: [parser.parse("$0")], conclusion: parser.parse("$0|$1") };
            case ".|2":
                return { conditions: [parser.parse("$1")], conclusion: parser.parse("$0|$1") };
            case ".&1":
                return { conditions: [parser.parse("$0&$1")], conclusion: parser.parse("$0") };
            case ".&2":
                return { conditions: [parser.parse("$0&$1")], conclusion: parser.parse("$1") };
            case ".<>1":
                return { conditions: [], conclusion: parser.parse("($0<>$1)>($0>$1)") };
            case ".<>2":
                return { conditions: [], conclusion: parser.parse("($0<>$1)>($1>$0)") };
            case ".|m":
                return {
                    conditions: [parser.parse("$0>$2"), parser.parse("$1>$2")],
                    conclusion: parser.parse("($0|$1)>$2")
                };
            case ".mn":
                return { conditions: [], conclusion: parser.parse("(~$0>$0)>$0") };
            case ".m2":
                return { conditions: [parser.parse("$0>$1"), parser.parse("~$0>$1")], conclusion: parser.parse("$1") };
            case "a3":
                return { conditions: [], conclusion: parser.parse("(~$1>~$0)>($0>$1)") };
            case "a7":
                return { conditions: [], conclusion: parser.parse("$0=$0") };
            case "a8":
                return { conditions: [], conclusion: parser.parse("($0=$1)>($2>#rp($2,$0,$1,$3))") };
            default:
                return undefined;
        }
    }

    private matchStrategyRuleSchema(deduction: Deduction,
        shape: { conditions: AST[]; conclusion: AST }): Map<string, string> | undefined {
        if (deduction.conditions.length !== shape.conditions.length) return undefined;
        const expectedToActual = new Map<string, string>();
        const actualToExpected = new Map<string, string>();
        const match = (actual: AST, expected: AST): boolean => {
            if (expected.type === "replvar" && expected.name.startsWith("$")) {
                if (actual.type !== "replvar" || !actual.name.startsWith("$")) return false;
                const existing = expectedToActual.get(expected.name);
                if (existing && existing !== actual.name) return false;
                const reverse = actualToExpected.get(actual.name);
                if (reverse && reverse !== expected.name) return false;
                expectedToActual.set(expected.name, actual.name);
                actualToExpected.set(actual.name, expected.name);
                return true;
            }
            if (actual.type !== expected.type || actual.name !== expected.name) return false;
            const actualNodes = actual.nodes ?? [];
            const expectedNodes = expected.nodes ?? [];
            if (actualNodes.length !== expectedNodes.length) return false;
            return expectedNodes.every((child, index) => match(actualNodes[index], child));
        };
        for (let index = 0; index < shape.conditions.length; index++) {
            if (!match(deduction.conditions[index], shape.conditions[index])) return undefined;
        }
        if (!match(deduction.conclusion, shape.conclusion)) return undefined;
        return expectedToActual;
    }

    private negatedProposition(ast: AST): AST | undefined {
        if (ast?.type === "sym" && ast.name === "~" && ast.nodes?.length === 1) {
            return ast.nodes[0];
        }
        return undefined;
    }

    private findContradictionPair(node: DraftNode): {
        proposition: AST;
        positiveName: string;
        negativeName: string;
    } | undefined {
        const hypotheses = node.hypotheses.filter(hypothesis =>
            !!hypothesis.proposition && this.isHypothesisAvailable(hypothesis)
        );
        for (const negative of hypotheses) {
            const proposition = this.negatedProposition(negative.proposition!);
            if (!proposition) continue;
            const positive = hypotheses.find(candidate => candidate.name !== negative.name
                && this.fixedPropositionMayMatch(candidate.proposition!, proposition));
            if (positive) {
                return {
                    proposition: astmgr.clone(proposition),
                    positiveName: positive.name,
                    negativeName: negative.name
                };
            }
        }
        return undefined;
    }

    private syntaxMayMatch(pattern: AST, target: AST): boolean {
        if (astmgr.equal(pattern, target)) return true;
        try {
            this.fs.assert.match(astmgr.clone(target), astmgr.clone(pattern), /^\$/, false, {}, {}, null, []);
            return true;
        } catch {
            return false;
        }
    }

    private isPurePropositionalSyntax(ast: AST): boolean {
        if (ast.type === "replvar") return true;
        if (ast.type !== "sym" || !["~", ">", "<>", "|", "&"].includes(ast.name)) return false;
        return !!ast.nodes?.length && ast.nodes.every(child => this.isPurePropositionalSyntax(child));
    }

    /**
     * Find a pending `have` only when the current goal is in that `have`'s
     * subgoal branch.  Searching the whole tree would make a fact from a
     * sibling rule-condition appear to be in scope and produce a misleading
     * "尚未完成" diagnostic.
     */
    private findPendingHaveForNode(target: DraftNode, name: string, node: DraftNode = this.root,
        pending: InferenceProofHypothesis[] = []): InferenceProofHypothesis | undefined {
        if (node === target) return pending.find(hypothesis => hypothesis.name === name);
        if (node.kind === "have" && node.children.length >= 2) {
            const subgoal = node.children[0];
            const continuation = node.children[1];
            const local = continuation.hypotheses.find(hypothesis =>
                hypothesis.kind === "have" && hypothesis.sourceNodeId === subgoal.id);
            const inSubgoal = this.findPendingHaveForNode(target, name, subgoal,
                local ? [...pending, local] : pending);
            if (inSubgoal) return inSubgoal;
            return this.findPendingHaveForNode(target, name, continuation, pending);
        }
        for (const child of node.children) {
            const found = this.findPendingHaveForNode(target, name, child, pending);
            if (found) return found;
        }
        return undefined;
    }

    private requireDeduction(name: string): Deduction {
        const deduction = this.fs.deductions[name] ?? this.fs.generateDeduction(name);
        if (!deduction) throw new Error(TR("推理规则不存在") + name);
        return deduction;
    }

    private matchConclusion(deduction: Deduction, target: AST, explicit: RuleExplicitArguments,
        conclusion: AST = deduction.conclusion, node?: DraftNode,
        context?: RuleMetavariableContext, inferencePatterns?: AST[],
        inferenceCandidates?: AST[]): RuleMatchResult {
        context ??= this.createRuleMetavariableContext(deduction, target, explicit, node);
        const matchTable: ReplvarMatchTable = {};
        const replacedTypes: { [name: string]: boolean } = {};
        const assign = (original: string, value: AST) => {
            const internal = context.internalByOriginal.get(original);
            if (!internal) throw new Error(TR("规则中不存在元变量") + original);
            if (matchTable[internal] && !astmgr.equal(matchTable[internal], value)) {
                throw new Error(TR("元变量映射重复：") + original);
            }
            this.fs.assert.getReplVarsType(value, replacedTypes, context.replaceTypes[internal]);
            matchTable[internal] = astmgr.clone(value);
        };
        for (let i = 0; i < explicit.positional.length; i++) {
            const original = deduction.replaceNames[i];
            if (!original) throw new Error(TR("apply参数过多"));
            assign(original, explicit.positional[i]);
        }
        for (const [original, value] of explicit.named.entries()) assign(original, value);
        try {
            const pattern = this.renameRuleMetavariables(conclusion, context.internalByOriginal);
            astmgr.replaceByMatchTable(pattern, matchTable);
            if (this.astContainsFunction(pattern, "#rp") && !this.astContainsPrivateRuleVariable(pattern)) {
                this.fs.assert.expand(pattern, false);
            }
            this.fs.assert.match(astmgr.clone(target), pattern, /^\$/, false,
                matchTable, replacedTypes, null, []);
        } catch (error) {
            throw new Error(TR("规则结论与当前目标不匹配：") + error);
        }
        this.inferRuleMetavariables(context, matchTable, inferencePatterns ?? context.conditions, node,
            inferenceCandidates);
        return {
            context,
            matchTable,
            unresolved: context.names.filter(name => !matchTable[context.internalByOriginal.get(name)!])
        };
    }

    private parseRuleArguments(parts: string[], deduction: Deduction): RuleExplicitArguments {
        const positional: AST[] = [];
        const named = new Map<string, AST>();
        const ruleNames = new Set<string>();
        const collect = (ast: AST) => {
            if (ast.type === "replvar" && ast.name.startsWith("$")) ruleNames.add(ast.name);
            ast.nodes?.forEach(collect);
        };
        deduction.conditions.forEach(collect);
        collect(deduction.conclusion);
        for (const part of parts) {
            const mapping = /^(\$[^=]+)=(.+)$/.exec(part);
            if (mapping) {
                const original = mapping[1];
                if (!ruleNames.has(original)) {
                    throw new Error(TR("规则中不存在元变量映射：") + original);
                }
                if (named.has(original)) throw new Error(TR("元变量映射重复：") + original);
                named.set(original, this.parsePropositionOrItem(mapping[2]));
            } else {
                positional.push(this.parsePropositionOrItem(part));
            }
        }
        if (positional.length > deduction.replaceNames.length) throw new Error(TR("apply参数过多"));
        return { positional, named };
    }

    private astContainsFunction(ast: AST, name: string): boolean {
        if (ast.type === "fn" && ast.name === name) return true;
        return !!ast.nodes?.some(child => this.astContainsFunction(child, name));
    }

    private astContainsPrivateRuleVariable(ast: AST): boolean {
        if (ast.type === "replvar" && ast.name.startsWith("$$assistant_rule_")) return true;
        return !!ast.nodes?.some(child => this.astContainsPrivateRuleVariable(child));
    }

    private createRuleMetavariableContext(deduction: Deduction, target: AST,
        explicit: RuleExplicitArguments, node?: DraftNode): RuleMetavariableContext {
        const names = new Set<string>();
        const collectNames = (ast: AST, set: Set<string>) => {
            if (ast.type === "replvar" && ast.name.startsWith("$")) set.add(ast.name);
            ast.nodes?.forEach(child => collectNames(child, set));
        };
        const collect = (ast: AST) => collectNames(ast, names);
        deduction.conditions.forEach(collect);
        collect(deduction.conclusion);
        const occupied = new Set<string>();
        collectNames(target, occupied);
        explicit.positional.forEach(value => collectNames(value, occupied));
        explicit.named.forEach(value => collectNames(value, occupied));
        node?.hypotheses.forEach(hypothesis => hypothesis.proposition && collectNames(hypothesis.proposition, occupied));
        this.fs.inferencePages.page(this.pageId)?.propositions.forEach(proposition => collectNames(proposition.value, occupied));
        const prefixBase = "$$assistant_rule_";
        let prefix = prefixBase;
        for (let index = 1; ; index++) {
            if (![...occupied].some(name => name.startsWith(prefix))) break;
            prefix = `${prefixBase}${index}_`;
        }
        const internalByOriginal = new Map<string, string>();
        const originalByInternal = new Map<string, string>();
        [...names].forEach((name, index) => {
            const internal = `${prefix}${index}`;
            internalByOriginal.set(name, internal);
            originalByInternal.set(internal, name);
        });
        const rename = (ast: AST): AST => {
            const result = astmgr.clone(ast);
            const visit = (value: AST) => {
                if (value.type === "replvar") {
                    const internal = internalByOriginal.get(value.name);
                    if (internal) value.name = internal;
                }
                value.nodes?.forEach(visit);
            };
            visit(result);
            return result;
        };
        const replaceNames = deduction.replaceNames
            .map(name => internalByOriginal.get(name)!)
            .filter(Boolean);
        const replaceTypes: { [name: string]: boolean } = {};
        for (const name of names) {
            const internal = internalByOriginal.get(name)!;
            replaceTypes[internal] = deduction.replaceTypes[name];
        }
        return {
            names: [...names],
            internalByOriginal,
            originalByInternal,
            conditions: deduction.conditions.map(rename),
            conclusion: rename(deduction.conclusion),
            replaceNames,
            replaceTypes
        };
    }

    private renameRuleMetavariables(ast: AST, internalByOriginal: Map<string, string>): AST {
        const visit = (value: AST) => {
            if (value.type === "replvar") {
                const internal = internalByOriginal.get(value.name);
                if (internal) value.name = internal;
            }
            value.nodes?.forEach(visit);
        };
        const result = astmgr.clone(ast);
        visit(result);
        return result;
    }

    private instantiateRuleAst(value: AST, context: RuleMetavariableContext,
        matchTable: ReplvarMatchTable): AST {
        const result = this.renameRuleMetavariables(value, context.internalByOriginal);
        astmgr.replaceByMatchTable(result, matchTable);
        return result;
    }

    private inferRuleMetavariables(context: RuleMetavariableContext, matchTable: ReplvarMatchTable,
        patterns: AST[], node?: DraftNode, inferenceCandidates?: AST[]): void {
        const candidates: AST[] = [];
        const addCandidate = (value?: AST) => {
            if (!value || candidates.some(candidate => astmgr.equal(candidate, value))) return;
            candidates.push(astmgr.clone(value));
        };
        if (node) {
            node.hypotheses.forEach(hypothesis => {
                if (hypothesis.proposition && this.isHypothesisAvailable(hypothesis)) addCandidate(hypothesis.proposition);
            });
            this.fs.inferencePages.page(this.pageId)?.propositions.forEach(proposition => {
                if (!proposition.from) addCandidate(proposition.value);
            });
        }
        inferenceCandidates?.forEach(addCandidate);
        for (const original of context.names) {
            const internal = context.internalByOriginal.get(original)!;
            if (matchTable[internal]) continue;
            const sets: AST[][] = [];
            for (const pattern of patterns) {
                const contains = this.astContainsName(pattern, internal);
                if (!contains) continue;
                const values: AST[] = [];
                for (const candidate of candidates) {
                    const trial = Object.fromEntries(Object.entries(matchTable).map(([key, value]) => [key, astmgr.clone(value)]));
                    try {
                        this.fs.assert.match(astmgr.clone(candidate), astmgr.clone(pattern), /^\$/, false,
                            trial, {}, null, []);
                        const value = trial[internal];
                        if (value && !values.some(item => astmgr.equal(item, value))) values.push(astmgr.clone(value));
                    } catch { }
                }
                sets.push(values);
            }
            if (!sets.length) continue;
            let intersection = sets[0].slice();
            for (const values of sets.slice(1)) {
                intersection = intersection.filter(item => values.some(value => astmgr.equal(item, value)));
            }
            if (intersection.length === 1) matchTable[internal] = intersection[0];
        }
    }

    private astContainsName(ast: AST, name: string): boolean {
        if (ast.type === "replvar" && ast.name === name) return true;
        return !!ast.nodes?.some(child => this.astContainsName(child, name));
    }

    private assertRuleMatchComplete(match: RuleMatchResult | RuleApplicationMatch, ruleName: string): void {
        if (!match.unresolved.length) return;
        const context = match.context;
        const names = match.unresolved.map(internal => context.originalByInternal.get(internal) ?? internal);
        throw new Error(TR("规则") + ruleName + TR("仍有未指定的元变量：") + names.join(", ")
            + TR("；请使用") + `apply ${ruleName} ${names.map(name => `${name}=...`).join(" ")}` + TR("指定"));
    }

    private parseProposition(target: AST | string): AST {
        const ast = typeof target === "string" ? parser.parse(target) : astmgr.clone(target);
        if (!ast) throw new Error(TR("空表达式"));
        this.fs.assert.checkGrammer(ast, "p");
        return ast;
    }

    private parsePropositionOrItem(value: string): AST {
        if (value === "_") throw new Error(TR("推理层证明助手暂不支持_模糊匹配"));
        try { return this.parseProposition(value); }
        catch { return astmgr.clone(parser.parse(value)); }
    }

    private assertSameProposition(a: AST, b: AST): void {
        const left = astmgr.clone(a);
        const right = astmgr.clone(b);
        try { this.fs.assert.expand(left, false); } catch { }
        try { this.fs.assert.expand(right, false); } catch { }
        if (astmgr.equal(left, right)) return;
        try {
            const noMetavariables = /(?!)/;
            this.fs.assert.match(left, right, noMetavariables, false, {}, {}, null, []);
            this.fs.assert.match(right, left, noMetavariables, false, {}, {}, null, []);
            return;
        } catch { }
        throw new Error(TR("证明来源与当前目标不匹配"));
    }

    private isHypothesisAvailable(hypothesis: InferenceProofHypothesis): boolean {
        // Direct `have h := ...` facts have no pending subgoal and therefore
        // intentionally omit sourceNodeId.  Legacy declaration-style `have`
        // keeps the source id and remains unavailable until its subgoal closes.
        return hypothesis.kind !== "have"
            || hypothesis.sourceNodeId === undefined
            || this.nodeSolved(hypothesis.sourceNodeId);
    }

    private nodeSolved(id: number): boolean {
        const node = this.findNode(this.root, id);
        return !!node && this.isSolved(node);
    }

    private isSolved(node: DraftNode): boolean {
        if (node.kind === "pending") return false;
        return node.children.every(child => this.isSolved(child));
    }

    private openNodes(node: DraftNode = this.root, result: DraftNode[] = []): DraftNode[] {
        if (node.kind === "pending") {
            result.push(node);
            return result;
        }
        for (const child of node.children) this.openNodes(child, result);
        return result;
    }

    private findNode(node: DraftNode, id: number): DraftNode | undefined {
        if (node.id === id) return node;
        for (const child of node.children) {
            const result = this.findNode(child, id);
            if (result) return result;
        }
    }

    private makeNode(target: AST, hypotheses: InferenceProofHypothesis[]): DraftNode {
        return {
            id: this.nextNodeId++,
            target: astmgr.clone(target),
            hypotheses,
            kind: "pending",
            children: [],
            introBindings: []
        };
    }

    private nextHypothesisName(node: DraftNode): string {
        for (let i = 1; ; i++) {
            const name = `h${i}`;
            if (!node.hypotheses.some(h => h.name === name)) return name;
        }
    }

    private nextHypothesisNames(node: DraftNode, count: number): string[] {
        const used = new Set(node.hypotheses.map(hypothesis => hypothesis.name));
        const names: string[] = [];
        for (let index = 1; names.length < count; index++) {
            const name = `h${index}`;
            if (used.has(name)) continue;
            used.add(name);
            names.push(name);
        }
        return names;
    }

    private assertUniqueHypothesis(node: DraftNode, name: string): void {
        if (node.hypotheses.some(h => h.name === name)) throw new Error(TR("假设名称已存在：") + name);
    }

    private cloneHypotheses(hypotheses: InferenceProofHypothesis[]): InferenceProofHypothesis[] {
        return hypotheses.map(h => ({
            name: h.name,
            proposition: h.proposition ? astmgr.clone(h.proposition) : undefined,
            binder: h.binder ? astmgr.clone(h.binder) : undefined,
            kind: h.kind,
            sourceNodeId: h.sourceNodeId
        }));
    }

    private substituteBound(ast: AST, source: string, destination: string): AST {
        if (ast.type === "replvar") {
            return ast.name === source ? { type: "replvar", name: destination } : astmgr.clone(ast);
        }
        if (!ast.nodes?.length) return astmgr.clone(ast);
        if (ast.type === "sym" && ["V", "E", "E!"].includes(ast.name)) {
            const binderName = this.fs.assert.getVarName(ast.nodes[0]) as string;
            // A nested binder with the source name shadows the outer binder.
            if (binderName === source) return astmgr.clone(ast);
            const binder = astmgr.clone(ast.nodes[0]);
            let body = astmgr.clone(ast.nodes[1]);
            // Avoid capturing the replacement variable under a nested binder.
            // For example, substituting x -> y in V y: x = y must first rename
            // the inner y binder.
            if (binderName === destination && this.containsFreeName(body, source)) {
                const fresh = this.freshBinderName(body, binderName, source, destination);
                this.renameBoundOccurrences(body, binderName, fresh);
                this.renameBinder(binder, binderName, fresh);
            }
            return {
                type: ast.type,
                name: ast.name,
                nodes: [binder, this.substituteBound(body, source, destination)]
            };
        }
        return {
            type: ast.type,
            name: ast.name,
            nodes: ast.nodes.map(child => this.substituteBound(child, source, destination))
        };
    }

    /** Capture-avoiding substitution used by direct universal `have` calls. */
    private substituteBoundValue(ast: AST, source: string, replacement: AST): AST {
        if (ast.type === "replvar") {
            return ast.name === source ? astmgr.clone(replacement) : astmgr.clone(ast);
        }
        if (!ast.nodes?.length) return astmgr.clone(ast);
        if (ast.type === "sym" && ["V", "E", "E!"].includes(ast.name)) {
            const binderName = this.fs.assert.getVarName(ast.nodes[0]) as string;
            // A nested binder with the source name shadows the outer binder.
            if (binderName === source) return astmgr.clone(ast);
            const binder = astmgr.clone(ast.nodes[0]);
            let body = astmgr.clone(ast.nodes[1]);
            // Rename a nested binder before inserting an argument that uses
            // that name, preventing accidental capture.
            const replacementNames = new Set<string>();
            this.collectReplvarNames(replacement, replacementNames);
            if (binderName && replacementNames.has(binderName) && this.containsFreeName(body, source)) {
                const fresh = this.freshBinderNameForReplacement(body, binderName, source, replacementNames);
                this.renameBoundOccurrences(body, binderName, fresh);
                this.renameBinder(binder, binderName, fresh);
            }
            return {
                type: ast.type,
                name: ast.name,
                nodes: [binder, this.substituteBoundValue(body, source, replacement)]
            };
        }
        return {
            type: ast.type,
            name: ast.name,
            nodes: ast.nodes.map(child => this.substituteBoundValue(child, source, replacement))
        };
    }

    private collectReplvarNames(ast: AST, result: Set<string>): void {
        if (ast.type === "replvar") result.add(ast.name);
        ast.nodes?.forEach(child => this.collectReplvarNames(child, result));
    }

    private freshBinderNameForReplacement(body: AST, binderName: string, source: string,
        replacementNames: Set<string>): string {
        const used = new Set<string>([binderName, source, ...replacementNames]);
        this.collectReplvarNames(body, used);
        let fresh = `${binderName}'`;
        while (used.has(fresh)) fresh += "'";
        return fresh;
    }

    private containsFreeName(ast: AST, name: string): boolean {
        if (ast.type === "replvar") return ast.name === name;
        if (!ast.nodes?.length) return false;
        if (ast.type === "sym" && ["V", "E", "E!"].includes(ast.name)) {
            const binderName = this.fs.assert.getVarName(ast.nodes[0]) as string;
            if (binderName === name) return false;
            return this.containsFreeName(ast.nodes[1], name);
        }
        return ast.nodes.some(child => this.containsFreeName(child, name));
    }

    private freshBinderName(body: AST, binderName: string, source: string, destination: string): string {
        const used = new Set<string>([binderName, source, destination]);
        const collect = (ast: AST) => {
            if (ast.type === "replvar") used.add(ast.name);
            ast.nodes?.forEach(collect);
        };
        collect(body);
        let fresh = `${binderName}'`;
        while (used.has(fresh)) fresh += "'";
        return fresh;
    }

    private renameBinder(ast: AST, source: string, destination: string): void {
        if (ast.type === "replvar") {
            if (ast.name === source) ast.name = destination;
            return;
        }
        ast.nodes?.forEach(child => this.renameBinder(child, source, destination));
    }

    private renameBoundOccurrences(ast: AST, source: string, destination: string): void {
        if (ast.type === "replvar") {
            if (ast.name === source) ast.name = destination;
            return;
        }
        if (!ast.nodes?.length) return;
        if (ast.type === "sym" && ["V", "E", "E!"].includes(ast.name)) {
            const binderName = this.fs.assert.getVarName(ast.nodes[0]) as string;
            if (binderName === source) return;
            this.renameBoundOccurrences(ast.nodes[0], source, destination);
            this.renameBoundOccurrences(ast.nodes[1], source, destination);
            return;
        }
        ast.nodes.forEach(child => this.renameBoundOccurrences(child, source, destination));
    }

    private replayHistory(history: readonly string[]): void {
        // Replaying must produce the same node identities as the original
        // command sequence.  Reset allocation before creating the root;
        // otherwise a failed command followed by replay shifts every goal id.
        this.nextNodeId = 1;
        this.root = this.makeNode(this.theorem, []);
        this.history = [];
        for (const command of history) {
            this.execute(command);
            this.history.push(command);
        }
    }

    private materialize(includeExternalPremises = false, allowIntroRules = false): {
        propositions: InferenceProofMaterializedProposition[];
        steps: DeductionStep[];
        basePropositionCount: number;
        pageFingerprint: string;
    } {
        const propositions: InferenceProofMaterializedProposition[] = [];
        const steps: DeductionStep[] = [];
        const page = this.fs.inferencePages.page(this.pageId);
        const basePropositionCount = page?.propositions.length ?? 0;
        const absolute = (index: number) => index + basePropositionCount;
        const materializationSystemSnapshot = this.captureFormalSystemState();
        let materializationSucceeded = false;
        try {

        // A closed pure-propositional theorem is already within MCPT's exact
        // domain. Keep it as one lazy node instead of rebuilding a Hilbert
        // proof from a1/a2/a3/mp during assistant expansion.
        if (this.allowMcpt && this.isPurePropositionalSyntax(this.theorem)) {
            const name = this.nextTautoName(this.theorem);
            try {
                if (!this.fs.deductions[name]) {
                    this.fs.metaCompleteTheorem(astmgr.clone(this.theorem), name, "证明助手自动MCPT*");
                }
                const step: DeductionStep = {
                    deductionIdx: name,
                    conditionIdxs: [],
                    replaceValues: []
                };
                propositions.push({
                    value: astmgr.clone(this.theorem),
                    from: step,
                    deferredKind: "cpt"
                });
                steps.push(step);
                materializationSucceeded = true;
                return {
                    propositions,
                    steps,
                    basePropositionCount,
                    pageFingerprint: this.pageFingerprint(page ?? { propositions: [] })
                };
            } catch {
                // Not every syntactically propositional target is a tautology.
                // Fall back to the user's explicit proof tree in that case.
            }
        }

        const collectExternalPremises = (node: DraftNode, result = new Map<string, Proposition>()): Map<string, Proposition> => {
            const source = node.kind === "haveApply" ? node.haveSource : node.source;
            if ((node.kind === "exact" || node.kind === "apply" || node.kind === "haveApply")
                && source?.kind === "page") {
                const sourcePage = this.fs.inferencePages.page(source.pageId);
                const proposition = sourcePage?.propositions[source.index];
                if (proposition) result.set(`${source.pageId}:${source.index}`, proposition);
            }
            for (const child of node.children) collectExternalPremises(child, result);
            return result;
        };
        const externalPremiseRows = new Map<string, number>();

        // Named qed compiles a self-contained chain.  Bring page propositions
        // used by exact into its initial condition rows before any derived row.
        if (includeExternalPremises) {
            for (const [key, proposition] of collectExternalPremises(this.root)) {
                externalPremiseRows.set(key, propositions.length);
                propositions.push({ value: astmgr.clone(proposition.value), from: null });
            }
        }

        const sourceAbsoluteRow = (source: Exclude<SourceRef, { kind: "rule" }>, hypothesisRows: Map<string, number>): number => {
            if (source.kind === "hypothesis") {
                const index = hypothesisRows.get(source.name);
                if (index === undefined) throw new Error(TR("无法物化证明来源：") + source.name);
                return absolute(index);
            }
            if (!includeExternalPremises) return source.index;
            const index = externalPremiseRows.get(`${source.pageId}:${source.index}`);
            if (index === undefined) throw new Error(TR("无法物化推理表定理来源"));
            return absolute(index);
        };

        const propositionAt = (absoluteIndex: number): Proposition => {
            if (absoluteIndex < basePropositionCount) {
                const proposition = page?.propositions[absoluteIndex];
                if (!proposition) throw new Error(TR("证明步骤引用了不存在的推理表定理"));
                return proposition;
            }
            const proposition = propositions[absoluteIndex - basePropositionCount];
            if (!proposition) throw new Error(TR("证明步骤引用了不存在的中间定理"));
            return proposition;
        };

        const appendDerived = (value: AST, step: DeductionStep,
            deferredKind?: "cpt"): EmitResult => {
            const index = propositions.length;
            propositions.push({
                value: astmgr.clone(value),
                from: {
                    deductionIdx: step.deductionIdx,
                    conditionIdxs: [...step.conditionIdxs],
                    replaceValues: step.replaceValues.map(item => astmgr.clone(item))
                },
                ...(deferredKind ? { deferredKind } : {})
            });
            steps.push(step);
            return { index, proposition: astmgr.clone(value) };
        };

        const implication = (premise: AST, conclusion: AST): AST => ({
            type: "sym",
            name: ">",
            nodes: [astmgr.clone(premise), astmgr.clone(conclusion)]
        });

        /** Discharge one implication-intro hypothesis through the generated row graph. */
        const dischargeHypothesis = (result: EmitResult, hypothesis: AST,
            hypothesisIndex: number): EmitResult => {
            const hypothesisAbsolute = absolute(hypothesisIndex);
            const transformed = new Map<number, EmitResult>();
            const dependency = new Map<number, boolean>();

            const dependsOnHypothesis = (absoluteIndex: number): boolean => {
                if (absoluteIndex === hypothesisAbsolute) return true;
                const cached = dependency.get(absoluteIndex);
                if (cached !== undefined) return cached;
                const row = propositionAt(absoluteIndex);
                const depends = !!row.from?.conditionIdxs.some(dependsOnHypothesis);
                dependency.set(absoluteIndex, depends);
                return depends;
            };

            const liftIndependent = (absoluteIndex: number): EmitResult => {
                const proposition = propositionAt(absoluteIndex).value;
                const axiom = implication(proposition, implication(hypothesis, proposition));
                const axiomResult = appendDerived(axiom, {
                    deductionIdx: "a1",
                    conditionIdxs: [],
                    replaceValues: [astmgr.clone(proposition), astmgr.clone(hypothesis)]
                });
                return appendDerived(implication(hypothesis, proposition), {
                    deductionIdx: "mp",
                    conditionIdxs: [absolute(axiomResult.index), absoluteIndex],
                    replaceValues: []
                });
            };

            const transform = (absoluteIndex: number): EmitResult => {
                const cached = transformed.get(absoluteIndex);
                if (cached) return cached;
                const row = propositionAt(absoluteIndex);
                if (absoluteIndex === hypothesisAbsolute
                    || (dependsOnHypothesis(absoluteIndex)
                        && this.fixedPropositionMayMatch(row.value, hypothesis))) {
                    const identity = appendDerived(implication(hypothesis, hypothesis), {
                        deductionIdx: ".i",
                        conditionIdxs: [],
                        replaceValues: [astmgr.clone(hypothesis)]
                    });
                    transformed.set(absoluteIndex, identity);
                    return identity;
                }
                if (!dependsOnHypothesis(absoluteIndex)) {
                    const lifted = liftIndependent(absoluteIndex);
                    transformed.set(absoluteIndex, lifted);
                    return lifted;
                }
                if (!row.from?.deductionIdx) throw new Error(TR("无法对临时假设应用演绎定理"));

                const conditions = row.from.conditionIdxs.map(transform);
                const desired = implication(hypothesis, row.value);
                const oldActivePage = this.fs.inferencePages.activeId;
                this.fs.inferencePages.activate(this.pageId);
                const oldFastMetarules = this.fs.fastmetarules;
                try {
                    this.fs.fastmetarules = this.availableFastMetaRules ?? "cvuqe><:#zZQR";
                    const expectedConditions = conditions.map(condition => condition.proposition);
                    const selection = this.selectGeneratedRule(
                        row.from.deductionIdx,
                        desired,
                        expectedConditions,
                        ["c", "<", ">"]
                    );
                    if (!selection) throw new Error(TR("无法生成匹配intro目标的最短条件演绎规则"));
                    const transformedResult = appendDerived(desired, {
                        deductionIdx: selection.name,
                        conditionIdxs: conditions.map(condition => absolute(condition.index)),
                        replaceValues: selection.replaceValues
                    });
                    this.assertSameProposition(transformedResult.proposition, desired);
                    transformed.set(absoluteIndex, transformedResult);
                    return transformedResult;
                } finally {
                    this.fs.fastmetarules = oldFastMetarules;
                    if (oldActivePage !== this.pageId) this.fs.inferencePages.activate(oldActivePage);
                }
            };

            return transform(absolute(result.index));
        };

        /** Generalize a completed proof graph over one introduced universal variable. */
        const quantifyResult = (result: EmitResult, binding: InferenceProofHypothesis): EmitResult => {
            if (!binding.binder) throw new Error(TR("全称变量缺少原始约束变量"));
            const binder = astmgr.clone(binding.binder);
            const binderName = this.fs.assert.getVarName(binder);
            if (!binderName) throw new Error(TR("全称量词约束变量无效"));
            const transformed = new Map<number, EmitResult>();
            const quantify = (body: AST): AST => ({
                type: "sym",
                name: "V",
                nodes: [astmgr.clone(binder), this.substituteBound(body, binding.name, binderName)]
            });

            const transform = (absoluteIndex: number): EmitResult => {
                const cached = transformed.get(absoluteIndex);
                if (cached) return cached;
                const row = propositionAt(absoluteIndex);
                const desired = quantify(row.value);

                if (!row.from) {
                    if (this.containsFreeName(row.value, binding.name)) {
                        throw new Error(TR("全称变量出现在未解除的外部前提中：") + binding.name);
                    }
                    const body = astmgr.clone(row.value);
                    const implicationTarget = implication(body, desired);
                    const axiom = this.requireDeduction("a6");
                    const match = this.matchConclusion(axiom, implicationTarget, {
                        positional: [],
                        named: new Map()
                    }, axiom.conclusion);
                    this.assertRuleMatchComplete(match, "a6");
                    const replaceValues = axiom.replaceNames.map(name => {
                        const value = match.matchTable[match.context.internalByOriginal.get(name)!];
                        if (!value) throw new Error(TR("无法从全称化目标推断a6参数：") + name);
                        return astmgr.clone(value);
                    });
                    const axiomResult = appendDerived(implicationTarget, {
                        deductionIdx: "a6",
                        conditionIdxs: [],
                        replaceValues
                    });
                    const quantified = appendDerived(desired, {
                        deductionIdx: "mp",
                        conditionIdxs: [absolute(axiomResult.index), absoluteIndex],
                        replaceValues: []
                    });
                    transformed.set(absoluteIndex, quantified);
                    return quantified;
                }

                const conditions = row.from.conditionIdxs.map(transform);
                const oldActivePage = this.fs.inferencePages.activeId;
                const oldFastMetarules = this.fs.fastmetarules;
                try {
                    this.fs.fastmetarules = this.availableFastMetaRules ?? "cvuqe><:#zZQR";
                    const originalRule = this.requireDeduction(row.from.deductionIdx);
                    const explicitValues = originalRule.conditions.length ? [] : [
                        astmgr.clone(binder),
                        ...row.from.replaceValues.map(value =>
                            this.substituteBound(value, binding.name, binderName))
                    ];
                    const selection = this.selectGeneratedRule(
                        row.from.deductionIdx,
                        desired,
                        conditions.map(condition => condition.proposition),
                        ["v", "u", "c", "<", ">"],
                        explicitValues
                    );
                    if (!selection) throw new Error(TR("无法生成匹配全称intro目标的最短概括规则"));
                    const quantified = appendDerived(desired, {
                        deductionIdx: selection.name,
                        conditionIdxs: conditions.map(condition => absolute(condition.index)),
                        replaceValues: selection.replaceValues
                    });
                    transformed.set(absoluteIndex, quantified);
                    return quantified;
                } finally {
                    this.fs.fastmetarules = oldFastMetarules;
                    if (oldActivePage !== this.pageId) this.fs.inferencePages.activate(oldActivePage);
                }
            };

            return transform(absolute(result.index));
        };

        /** Emit a direct `have h := source arg...` specialization. */
        const emitHaveApplication = (node: DraftNode,
            hypothesisRows: Map<string, number>): EmitResult => {
            if (!node.haveSource || node.haveSource.kind === "rule" || !node.haveProposition) {
                throw new Error(TR("have应用节点缺少局部或页面命题来源"));
            }
            const sourceAbsoluteIndex = sourceAbsoluteRow(node.haveSource, hypothesisRows);
            let currentRow = sourceAbsoluteIndex;
            let currentProposition = astmgr.clone(propositionAt(currentRow).value);
            const args = node.haveArguments ?? [];

            // Even a direct alias gets a local derived row.  This keeps the
            // continuation hypothesis independent of an external page row.
            if (!args.length) {
                const identity = appendDerived(implication(currentProposition, currentProposition), {
                    deductionIdx: ".i",
                    conditionIdxs: [],
                    replaceValues: [astmgr.clone(currentProposition)]
                });
                const result = appendDerived(currentProposition, {
                    deductionIdx: "mp",
                    conditionIdxs: [absolute(identity.index), currentRow],
                    replaceValues: []
                });
                this.assertSameProposition(result.proposition, node.haveProposition);
                return { index: result.index, proposition: astmgr.clone(node.haveProposition) };
            }

            for (const argument of args) {
                if (currentProposition.type !== "sym" || currentProposition.name !== "V"
                    || currentProposition.nodes?.length !== 2) {
                    throw new Error(TR("have应用参数过多，来源命题不是足够的全称命题"));
                }
                const binder = astmgr.clone(currentProposition.nodes[0]);
                const binderName = this.fs.assert.getVarName(binder);
                if (!binderName) throw new Error(TR("have来源命题的全称量词变量无效"));
                const body = astmgr.clone(currentProposition.nodes[1]);
                const specialized = this.substituteBoundValue(body, binderName, argument);
                const elimination = appendDerived(implication(currentProposition, specialized), {
                    deductionIdx: "a4",
                    conditionIdxs: [],
                    replaceValues: [binder, body, astmgr.clone(argument)]
                });
                const result = appendDerived(specialized, {
                    deductionIdx: "mp",
                    conditionIdxs: [absolute(elimination.index), currentRow],
                    replaceValues: []
                });
                currentRow = absolute(result.index);
                currentProposition = specialized;
            }
            this.assertSameProposition(currentProposition, node.haveProposition);
            return { index: currentRow - basePropositionCount, proposition: astmgr.clone(node.haveProposition) };
        };

        let emit: (node: DraftNode, incomingRows: Map<string, number>) => EmitResult;
        const emitBody = (node: DraftNode, incomingRows: Map<string, number>): EmitResult => {
            const hypothesisRows = new Map(incomingRows);
            const introEntries: { binding: InferenceProofHypothesis; index?: number }[] = [];
            // Implication intros create temporary proposition rows. Universal
            // intros carry their original binder so finish() can generalize the
            // completed proof graph in the exact reverse introduction order.
            for (const hypothesis of node.introBindings) {
                if (hypothesis.proposition) {
                    const index = propositions.length;
                    propositions.push({ value: astmgr.clone(hypothesis.proposition), from: null });
                    hypothesisRows.set(hypothesis.name, index);
                    introEntries.push({ binding: hypothesis, index });
                } else {
                    introEntries.push({ binding: hypothesis });
                }
            }
            const finish = (result: EmitResult): EmitResult => {
                for (let index = introEntries.length - 1; index >= 0; index--) {
                    const intro = introEntries[index];
                    if (intro.binding.proposition) {
                        if (intro.index === undefined) throw new Error(TR("intro临时假设行缺失"));
                        result = dischargeHypothesis(result, intro.binding.proposition, intro.index);
                    } else if (intro.binding.kind === "variable") {
                        result = quantifyResult(result, intro.binding);
                    }
                }
                return result;
            };
            if (node.kind === "revert") {
                if (node.children.length !== 1 || !node.revertSource) {
                    throw new Error(TR("revert证明节点结构无效"));
                }
                const implicationResult = emit(node.children[0], hypothesisRows);
                const implication = implicationResult.proposition;
                if (implication.type !== "sym" || implication.name !== ">" || implication.nodes?.length !== 2) {
                    throw new Error(TR("revert子目标没有生成蕴含证明"));
                }
                if (node.revertSource.kind === "rule") throw new Error(TR("revert证明来源不能是推理规则"));
                const sourceIndex = sourceAbsoluteRow(node.revertSource, hypothesisRows);
                this.assertSameProposition(implication.nodes[0], propositionAt(sourceIndex).value);
                this.assertSameProposition(implication.nodes[1], node.target);
                const result = appendDerived(node.target, {
                    deductionIdx: "mp",
                    conditionIdxs: [absolute(implicationResult.index), sourceIndex],
                    replaceValues: []
                });
                return finish(result);
            }
            if (node.kind === "have") {
                const first = emit(node.children[0], hypothesisRows);
                const local = node.children[1].hypotheses.find(h => h.kind === "have" && h.sourceNodeId === node.children[0].id);
                const continuationRows = new Map(hypothesisRows);
                if (local) continuationRows.set(local.name, first.index);
                return finish(emit(node.children[1], continuationRows));
            }
            if (node.kind === "haveApply") {
                if (node.children.length !== 1 || !node.haveName) {
                    throw new Error(TR("have应用节点结构无效"));
                }
                const first = emitHaveApplication(node, hypothesisRows);
                const continuationRows = new Map(hypothesisRows);
                continuationRows.set(node.haveName, first.index);
                return finish(emit(node.children[0], continuationRows));
            }
            if (node.kind === "apply") {
                const children = node.children.map(child => emit(child, hypothesisRows));
                if (node.source && node.source.kind !== "rule") {
                    if (!node.appliedProposition) throw new Error(TR("apply证明节点缺少蕴含来源"));
                    let implication = astmgr.clone(node.appliedProposition);
                    let implicationRow = sourceAbsoluteRow(node.source, hypothesisRows);
                    for (let index = 0; index < children.length; index++) {
                        if (implication.type !== "sym" || implication.name !== ">" || implication.nodes?.length !== 2) {
                            throw new Error(TR("apply证明节点的蕴含层数无效"));
                        }
                        this.assertSameProposition(implication.nodes[0], children[index].proposition);
                        const conclusion = astmgr.clone(implication.nodes[1]);
                        const step: DeductionStep = {
                            deductionIdx: "mp",
                            conditionIdxs: [implicationRow, absolute(children[index].index)],
                            replaceValues: []
                        };
                        const resultIndex = propositions.length;
                        propositions.push({ value: conclusion, from: step });
                        steps.push(step);
                        implicationRow = absolute(resultIndex);
                        implication = conclusion;
                    }
                    this.assertSameProposition(implication, node.target);
                    return finish({ index: implicationRow - basePropositionCount, proposition: astmgr.clone(node.target) });
                }
                if (!node.ruleName) throw new Error(TR("apply证明节点缺少推理规则"));
                const ruleConditionCount = node.ruleConditionCount ?? children.length;
                if (ruleConditionCount > children.length) throw new Error(TR("apply证明节点的规则条件数量无效"));
                const ruleStep: DeductionStep = {
                    deductionIdx: node.ruleName,
                    conditionIdxs: children.slice(0, ruleConditionCount).map(child => absolute(child.index)),
                    replaceValues: (node.replaceValues ?? []).map(value => astmgr.clone(value))
                };
                let implication = astmgr.clone(node.appliedProposition ?? node.target);
                let resultIndex = propositions.length;
                propositions.push({ value: astmgr.clone(implication), from: ruleStep });
                steps.push(ruleStep);
                let implicationRow = absolute(resultIndex);
                for (const child of children.slice(ruleConditionCount)) {
                    if (implication.type !== "sym" || implication.name !== ">" || implication.nodes?.length !== 2) {
                        throw new Error(TR("apply证明节点的蕴含层数无效"));
                    }
                    this.assertSameProposition(implication.nodes[0], child.proposition);
                    const conclusion = astmgr.clone(implication.nodes[1]);
                    const mpStep: DeductionStep = {
                        deductionIdx: "mp",
                        conditionIdxs: [implicationRow, absolute(child.index)],
                        replaceValues: []
                    };
                    resultIndex = propositions.length;
                    propositions.push({ value: conclusion, from: mpStep });
                    steps.push(mpStep);
                    implicationRow = absolute(resultIndex);
                    implication = conclusion;
                }
                this.assertSameProposition(implication, node.target);
                return finish({ index: resultIndex, proposition: astmgr.clone(node.target) });
            }
            if (node.kind === "tauto") {
                if (!node.tautoName) throw new Error(TR("tauto证明节点缺少内部规则"));
                const step: DeductionStep = { deductionIdx: node.tautoName, conditionIdxs: [], replaceValues: [] };
                const index = propositions.length;
                propositions.push({ value: astmgr.clone(node.target), from: step, deferredKind: "cpt" });
                steps.push(step);
                return finish({ index, proposition: astmgr.clone(node.target) });
            }
            if (node.kind === "exact" && node.source) {
                if (node.source.kind === "rule") {
                    const step: DeductionStep = {
                        deductionIdx: node.source.name,
                        conditionIdxs: [],
                        replaceValues: node.source.replaceValues.map(value => astmgr.clone(value))
                    };
                    const index = propositions.length;
                    propositions.push({ value: astmgr.clone(node.target), from: step });
                    steps.push(step);
                    return finish({ index, proposition: astmgr.clone(node.target) });
                }
                const sourceAbsoluteIndex = sourceAbsoluteRow(node.source, hypothesisRows);
                const idStep: DeductionStep = { deductionIdx: ".i", conditionIdxs: [], replaceValues: [astmgr.clone(node.target)] };
                const idIndex = propositions.length;
                propositions.push({ value: { type: "sym", name: ">", nodes: [astmgr.clone(node.target), astmgr.clone(node.target)] }, from: idStep });
                const mpStep: DeductionStep = { deductionIdx: "mp", conditionIdxs: [absolute(idIndex), sourceAbsoluteIndex], replaceValues: [] };
                const index = propositions.length;
                propositions.push({ value: astmgr.clone(node.target), from: mpStep });
                steps.push(idStep, mpStep);
                return finish({ index, proposition: astmgr.clone(node.target) });
            }
            throw new Error(TR("证明树中仍有未完成目标"));
        };

        emit = emitBody;
        const result = emit(this.root, new Map());
        this.assertSameProposition(result.proposition, this.theorem);

        // Temporary intro hypotheses and the proof rows that depended on them
        // are implementation details. Retain only the final discharged proof
        // graph so bare qed does not leave hypotheses in the inference page and
        // named qed records the theorem rather than a conditional macro.
        const reachable = new Set<number>();
        const visit = (absoluteIndex: number) => {
            if (absoluteIndex < basePropositionCount) return;
            const localIndex = absoluteIndex - basePropositionCount;
            if (reachable.has(localIndex)) return;
            const proposition = propositions[localIndex];
            if (!proposition) throw new Error(TR("最终证明引用了不存在的中间定理"));
            reachable.add(localIndex);
            proposition.from?.conditionIdxs.forEach(visit);
        };
        visit(absolute(result.index));
        const kept = [...reachable].sort((left, right) => left - right);
        const remap = new Map(kept.map((oldIndex, newIndex) => [oldIndex, newIndex]));
        const compacted = kept.map(oldIndex => {
            const proposition = propositions[oldIndex];
            if (!proposition.from) return { value: astmgr.clone(proposition.value), from: null };
            return {
                value: astmgr.clone(proposition.value),
                from: {
                    deductionIdx: proposition.from.deductionIdx,
                    conditionIdxs: proposition.from.conditionIdxs.map(conditionIndex => {
                        if (conditionIndex < basePropositionCount) return conditionIndex;
                        const mapped = remap.get(conditionIndex - basePropositionCount);
                        if (mapped === undefined) throw new Error(TR("最终证明缺少依赖的中间定理"));
                        return basePropositionCount + mapped;
                    }),
                    replaceValues: proposition.from.replaceValues.map(value => astmgr.clone(value)),
                    ...(proposition.from.assistant ? {
                        assistant: this.cloneDeferredAssistantPayload(proposition.from.assistant)
                    } : {})
                },
                ...(proposition.deferredKind ? { deferredKind: proposition.deferredKind } : {})
            } as InferenceProofMaterializedProposition;
        });
        propositions.splice(0, propositions.length, ...compacted);
        steps.splice(0, steps.length, ...compacted.flatMap(proposition => proposition.from ? [proposition.from] : []));
        const existingDeductionNames = new Set(Object.keys(materializationSystemSnapshot.deductions));
        for (const step of steps) {
            this.assertGeneratedDeductionMetaRules(step.deductionIdx, existingDeductionNames);
        }
        materializationSucceeded = true;
        return {
            propositions,
            steps,
            basePropositionCount,
            pageFingerprint: this.pageFingerprint(page ?? { propositions: [] })
        };
        } finally {
            // Conditionalizing an atomic user rule can create generated
            // helper deductions such as `cmyRule`/`ccmyRule`.  The compacted
            // proof graph references those names, so retain only the helpers
            // actually used by this successful materialization after rolling
            // back unrelated temporary state.
            const generated = new Map<string, Deduction>();
            if (materializationSucceeded) {
                const retainGenerated = (name: string) => {
                    if (materializationSystemSnapshot.deductions[name]) return;
                    if (generated.has(name)) return;
                    const deduction = this.fs.deductions[name];
                    if (!deduction) return;
                    generated.set(name, this.cloneDeduction(deduction));
                    deduction.steps?.forEach(step => retainGenerated(step.deductionIdx));
                };
                steps.forEach(step => retainGenerated(step.deductionIdx));
            }
            this.restoreFormalSystemState(materializationSystemSnapshot);
            for (const [name, deduction] of generated) {
                if (!this.fs.deductions[name]) this.fs.deductions[name] = deduction;
            }
        }
    }
}

/**
 * FormalSystem calls this hook when an assistant-generated atomic rule is
 * explicitly expanded.  The replay page is isolated from the user's live
 * page, so pN references remain bound to the snapshot captured by qed.
 */
const assistantReplayStack = new Set<string>();

registerDeferredAssistantMaterializer((fs, deduction) => {
    const payload = deduction.deferredPayload;
    if (!payload || payload.kind !== "assistant" || payload.version !== 1) {
        throw new Error(TR("证明助手延迟步骤数据无效"));
    }
    if (!astmgr.equal(deduction.conclusion, payload.theorem)
        || deduction.conditions.length !== payload.premises.length
        || deduction.conditions.some((condition, index) => !astmgr.equal(condition, payload.premises[index].value))) {
        throw new Error(TR("证明助手延迟步骤与推理规则结论不匹配"));
    }
    const deductionName = Object.entries(fs.deductions).find(([, value]) => value === deduction)?.[0];
    const replayKey = deductionName ?? `payload:${parser.stringifyTight(payload.theorem)}:${payload.history.join("\u0000")}`;
    if (assistantReplayStack.has(replayKey)) {
        throw new Error(TR("证明助手延迟步骤存在循环依赖"));
    }
    assistantReplayStack.add(replayKey);
    const existingNames = new Set(Object.keys(fs.deductions));
    const previousPages = fs.inferencePages;
    const premiseIndices = new Set<number>();
    const indexMap = new Map<number, number>();
    for (const [position, premise] of payload.premises.entries()) {
        if (!Number.isInteger(premise.index) || premise.index < 0 || premiseIndices.has(premise.index)) {
            assistantReplayStack.delete(replayKey);
            throw new Error(TR("证明助手延迟步骤的前提编号无效"));
        }
        if (premise.pageId !== undefined && premise.pageId !== payload.pageId) {
            assistantReplayStack.delete(replayKey);
            throw new Error(TR("证明助手延迟步骤的来源推理表不匹配"));
        }
        premiseIndices.add(premise.index);
        indexMap.set(premise.index, position);
    }
    let replayHistory: string[];
    try {
        replayHistory = payload.history.map(command => {
            const match = /^(apply|exact)\s+p([0-9]+)(?=\s|$)/.exec(command.trim())
                ?? /^(have\s+[^\s,:=]+\s*:=\s*)p([0-9]+)(?=\s|$)/.exec(command.trim());
            if (!match) return command;
            const originalIndex = Number(match[2]);
            const replayIndex = indexMap.get(originalIndex);
            if (replayIndex === undefined) {
                throw new Error(TR("证明助手延迟步骤缺少所引用的前提定理 p") + originalIndex);
            }
            if (/^(apply|exact)\b/.test(match[1])) {
                return command.replace(/^(apply|exact)\s+p[0-9]+/, `${match[1]} p${replayIndex}`);
            }
            return command.replace(/^(have\s+[^\s,:=]+\s*:=\s*)p[0-9]+/, `${match[1]}p${replayIndex}`);
        });
    } catch (error) {
        // This mapping runs before the replay try/finally below.  Release the
        // recursion marker here as well, otherwise a later retry would be
        // misreported as a circular dependency.
        assistantReplayStack.delete(replayKey);
        throw error;
    }
    const replayRows: Proposition[] = payload.premises.map(premise => ({
        value: astmgr.clone(premise.value),
        from: null
    }));
    /*
     * The temporary page contains only snapshotted premises. Explicit pN
     * references were remapped above, so there is no filler proposition that
     * a corrupted history could accidentally use. Do not mutate the persisted
     * payload while constructing the replay page; saves may share this object
     * with an active draft or another deduction clone.
     */
    const replayPageId = "__assistant_replay";
    fs.inferencePages = new InferencePageStore<Proposition>([
        {
            id: replayPageId,
            name: replayPageId,
            propositions: replayRows,
            command: { input: "", buffer: [] }
        }
    ], replayPageId);
    try {
        const assistant = new InferenceProofAssistant(fs, astmgr.clone(payload.theorem), {
            pageId: replayPageId,
            history: replayHistory,
            ...(payload.ruleNames ? { ruleNames: payload.ruleNames } : {}),
            ...(payload.fastMetaRules !== undefined ? { fastMetaRules: payload.fastMetaRules } : {}),
            allowMcpt: payload.allowMcpt !== false
        });
        const replayed = assistant.materializeForDeferred();
        // `materialize()` restores the formal-system snapshot by replacing the
        // deductions map, so reacquire the live entry before attaching steps.
        const liveDeduction = (deductionName ? fs.deductions[deductionName] : undefined) ?? deduction;
        liveDeduction.steps = replayed.steps;
        liveDeduction.tempvars = replayed.tempvars;
        liveDeduction.deferredKind = "assistant";
        // Older bare-qed saves used a private `__assist_N` deduction and let
        // ast2deduction infer replacement parameters from free `$` names in
        // the theorem.  Their page step carries no corresponding values, so
        // retaining those names would make the next `entr` call dereference
        // an undefined AST.  The assistant recipe already contains the exact
        // theorem and premise snapshot; legacy bare entries therefore have no
        // replacement parameters.
        if (deductionName && /^__assist_[0-9]+$/.test(deductionName)) {
            liveDeduction.replaceNames = [];
            deduction.replaceNames = [];
        }
        // Command adapters snapshot the deductions object before expansion and
        // restore that shallow map afterwards.  Mirror the result onto the
        // original object as well so the cached steps survive that rollback.
        if (liveDeduction !== deduction) {
            deduction.steps = replayed.steps;
            deduction.tempvars = replayed.tempvars;
            deduction.deferredKind = "assistant";
        }
    } catch (error) {
        // Replay may create generated helper rules (for example a nested
        // tauto).  Do not leave a partial rule table behind on failure.
        for (const name of Object.keys(fs.deductions)) {
            if (!existingNames.has(name)) delete fs.deductions[name];
        }
        throw error;
    } finally {
        fs.inferencePages = previousPages;
        assistantReplayStack.delete(replayKey);
    }
});

/** Short alias retained for adapters that use the FS prefix. */
export const FSProofAssistant = InferenceProofAssistant;
