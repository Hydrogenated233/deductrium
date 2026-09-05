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
import { migrateInferenceProofHistory } from "./proof-syntax.js";

const astmgr = new ASTMgr();
const parser = new ASTParser();
const PRIVATE_RULE_METAVARIABLE_PATTERN = /^\$\$assistant_rule_/;

export type InferenceProofHypothesisKind = "intro" | "variable" | "have" | "page";

export interface InferenceProofHypothesis {
    name: string;
    proposition?: AST;
    /**
     * Unnormalized proposition retained for replay/materialization.  The
     * assistant may simplify assertion syntax in `proposition` for tactics
     * and rendering, but rules such as .Vcn/.Ecn need the original #nf/#rp
     * dependency when qed later lifts the proof through binders.
     */
    formalProposition?: AST;
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
    /** Whether iff lifting (the `mifft` capability) may be used by `rw`. */
    allowIfft?: boolean;
    /** Whether iff lifting through `E!` may be used by `rw`. */
    allowIfftEu?: boolean;
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

type RuleHaveInstantiation = {
    conditions: AST[];
    conclusion: AST;
    replaceValues: AST[];
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
    /** Normalized target used by tactics and the proof-assistant UI. */
    target: AST;
    /** Exact target used only while materializing the completed proof tree. */
    formalTarget: AST;
    hypotheses: InferenceProofHypothesis[];
    kind: "pending" | "apply" | "applyAt" | "have" | "haveApply" | "obtainExists" | "revert" | "exact" | "tauto" | "rwIff";
    children: DraftNode[];
    ruleName?: string;
    replaceValues?: AST[];
    /** Rule arguments with presentation-only assertion simplifications restored. */
    formalReplaceValues?: AST[];
    source?: SourceRef;
    /** Local hypothesis rewritten by Lean-style `apply rule at h`. */
    applyAtHypothesis?: string;
    /** Instantiated conclusion/source proposition used by implication apply. */
    appliedProposition?: AST;
    /** Unnormalized instantiated conclusion used by materialization. */
    formalAppliedProposition?: AST;
    /** Number of leading children required by a shared rule's `⊢` conditions. */
    ruleConditionCount?: number;
    /** Theorem-list premises used by a conditional tauto proof. */
    tautoSources?: SourceRef[];
    /** The exact tautology checked by MCPT (target or premise > target). */
    tautoTheorem?: AST;
    haveName?: string;
    /** Direct `have name := source arg...` application metadata. */
    haveSource?: SourceRef;
    haveArguments?: AST[];
    /** Sources used for implication arguments; `null` entries are term arguments. */
    haveArgumentSources?: (SourceRef | null)[];
    haveProposition?: AST;
    formalHaveProposition?: AST;
    /** Existential source and local names introduced by `obtain <x,hx> := h`. */
    obtainSource?: SourceRef;
    obtainVariableName?: string;
    obtainHypothesisName?: string;
    obtainBinder?: AST;
    obtainBody?: AST;
    formalObtainBinder?: AST;
    formalObtainBody?: AST;
    obtainEmpRule?: string;
    obtainEeRule?: string;
    revertSource?: SourceRef;
    /** Iff rewrite keeps an atomic recipe until qed materialization. */
    rwBefore?: AST;
    rwAfter?: AST;
    rwSourceTerm?: AST;
    rwDestinationTerm?: AST;
    rwReverse?: boolean;
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
    private allowIfft = true;
    private allowIfftEu = true;
    /**
     * Only proofs whose stated goal contains user-visible assertion syntax need
     * a second, unsimplified materialization track.  Keeping ordinary proofs on
     * the historic normalized path avoids exposing internal a4/#rp wrappers to
     * conditionalization and universal generalization.
     */
    private preserveFormalAssertions = false;
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
        this.allowIfft = options.allowIfft !== false;
        this.allowIfftEu = options.allowIfftEu !== false;
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
        this.preserveFormalAssertions = this.containsSchematicAssertion(ast);
        this.targetSource = parser.stringifyTight(ast);
        this.nextNodeId = 1;
        this.root = this.makeNode(ast, []);
        this.history = [];
        this.committed = false;
        this.revision = 0;
        const history = migrateInferenceProofHistory(options.history);
        if (history.length) {
            const systemSnapshot = this.captureFormalSystemState();
            const root = this.cloneDraftNode(this.root);
            try {
                this.replayHistory(history);
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
        const deferredCommands: string[] = [];
        const addDeferred = (command: string) => {
            if (!deferredCommands.includes(command)) deferredCommands.push(command);
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
                if (this.canRewriteIffTarget(node.target, hypothesis.proposition, false, availableRuleNames)) {
                    add(`rw ${hypothesis.name}`);
                }
                const simplifyDirection = this.simplifyDirection(hypothesis.proposition);
                if (simplifyDirection !== null
                    && this.canRewriteTarget(node.target, hypothesis.proposition, simplifyDirection, availableRuleNames)) {
                    add("simp");
                }
                addDeferred(`revert ${hypothesis.name}`);
                if (hypothesis.proposition.type === "sym" && ["&", "<>"].includes(hypothesis.proposition.name)
                    && hypothesis.proposition.nodes?.length === 2) {
                    const rules = hypothesis.proposition.name === "&" ? [".&1", ".&2"] : [".<>1", ".<>2"];
                    if (rules.every(rule => this.resolveStrategyRule(rule, availableRuleNames))) {
                        const names = this.nextHypothesisNames(node, 2);
                        add(`cases ${hypothesis.name}`);
                        add(`obtain <${names[0]},${names[1]}> := ${hypothesis.name}`);
                    }
                }
                if (hypothesis.proposition.type === "sym" && hypothesis.proposition.name === "|"
                    && hypothesis.proposition.nodes?.length === 2
                    && this.canUseFastMetaRule("c")
                    && this.resolveStrategyRule(".|m", availableRuleNames)) {
                    const names = this.nextHypothesisNames(node, 2);
                    add(`cases ${hypothesis.name}`);
                    add(`obtain ${names[0]} | ${names[1]} := ${hypothesis.name}`);
                }
                if (hypothesis.proposition.type === "sym" && hypothesis.proposition.name === "E"
                    && hypothesis.proposition.nodes?.length === 2
                    && this.resolveStrategyRule(".Ee", availableRuleNames)
                    && this.resolveStrategyRule(".Emp", availableRuleNames)) {
                    const names = this.nextHypothesisNames(node, 2);
                    add(`cases ${hypothesis.name}`);
                    add(`obtain <${names[0]},${names[1]}> := ${hypothesis.name}`);
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
        if (node.target.type === "sym" && node.target.name === "E" && node.target.nodes?.length === 2
            && this.resolveStrategyRule(".Erp", availableRuleNames)) {
            add("use ??");
        }
        const page = this.fs.inferencePages.page(this.pageId);
        page?.propositions.forEach((proposition, index) => {
            addPropositionSource(`p${index}`, proposition.value, false);
            if (this.canRewriteTarget(node.target, proposition.value, false, availableRuleNames)) add(`rw p${index}`);
            if (this.canRewriteIffTarget(node.target, proposition.value, false, availableRuleNames)) add(`rw p${index}`);
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
        // `revert` is a context-management escape hatch, not a first-line
        // proof step.  Keep it as a fallback only when no goal-shaping
        // recommendation was found, and cap the fallback list so a large
        // context does not turn the recommendation panel into a wall of
        // rarely useful commands.
        if (commands.length === 0) return [...commands, ...deferredCommands.slice(0, 3)];
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
            // A deferred assistant row is visible to proposition gates before
            // `entr`/`inln` expands it.  Validate the exact replay path now so
            // an invalid generalization cannot enter the page as a trusted
            // atomic step.  The expanded graph is discarded and remains lazy.
            this.validateDeferredMaterialization();
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
                        ...(data.step.info !== undefined ? { info: data.step.info } : {}),
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

    /** Check deferred replay transactionally without retaining expanded steps. */
    private validateDeferredMaterialization(): void {
        const systemSnapshot = this.captureFormalSystemState();
        const previousActive = this.fs.inferencePages.activeId;
        try {
            this.materializeForDeferred();
        } finally {
            this.restoreFormalSystemState(systemSnapshot);
            if (this.fs.inferencePages.activeId !== previousActive
                && this.fs.inferencePages.page(previousActive)) {
                this.fs.inferencePages.activate(previousActive);
            }
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
                ...(step.info !== undefined ? { info: step.info } : {}),
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
                ...(deduction.deferredPayload.allowIfft !== undefined
                    ? { allowIfft: deduction.deferredPayload.allowIfft } : {}),
                ...(deduction.deferredPayload.allowIfftEu !== undefined
                    ? { allowIfftEu: deduction.deferredPayload.allowIfftEu } : {}),
                ...(deduction.deferredPayload.tauto ? {
                    tauto: { checkedTheorem: astmgr.clone(deduction.deferredPayload.tauto.checkedTheorem) }
                } : {}),
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
            ...(payload.allowIfft !== undefined ? { allowIfft: payload.allowIfft } : {}),
            ...(payload.allowIfftEu !== undefined ? { allowIfftEu: payload.allowIfftEu } : {}),
            ...(payload.tauto ? { tauto: { checkedTheorem: astmgr.clone(payload.tauto.checkedTheorem) } } : {}),
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
            formalTarget: astmgr.clone(node.formalTarget),
            hypotheses: this.cloneHypotheses(node.hypotheses),
            kind: node.kind,
            children: node.children.map(child => this.cloneDraftNode(child)),
            ruleName: node.ruleName,
            replaceValues: node.replaceValues?.map(value => astmgr.clone(value)),
            formalReplaceValues: node.formalReplaceValues?.map(value => astmgr.clone(value)),
            source: this.cloneSource(node.source),
            applyAtHypothesis: node.applyAtHypothesis,
            appliedProposition: node.appliedProposition ? astmgr.clone(node.appliedProposition) : undefined,
            formalAppliedProposition: node.formalAppliedProposition
                ? astmgr.clone(node.formalAppliedProposition) : undefined,
            ruleConditionCount: node.ruleConditionCount,
            tautoSources: node.tautoSources?.map(source => this.cloneSource(source)!),
            tautoTheorem: node.tautoTheorem ? astmgr.clone(node.tautoTheorem) : undefined,
            haveName: node.haveName,
            haveSource: this.cloneSource(node.haveSource),
            haveArguments: node.haveArguments?.map(value => astmgr.clone(value)),
            haveArgumentSources: node.haveArgumentSources?.map(source => this.cloneSource(source) ?? null),
            haveProposition: node.haveProposition ? astmgr.clone(node.haveProposition) : undefined,
            formalHaveProposition: node.formalHaveProposition
                ? astmgr.clone(node.formalHaveProposition) : undefined,
            obtainSource: this.cloneSource(node.obtainSource),
            obtainVariableName: node.obtainVariableName,
            obtainHypothesisName: node.obtainHypothesisName,
            obtainBinder: node.obtainBinder ? astmgr.clone(node.obtainBinder) : undefined,
            obtainBody: node.obtainBody ? astmgr.clone(node.obtainBody) : undefined,
            formalObtainBinder: node.formalObtainBinder
                ? astmgr.clone(node.formalObtainBinder) : undefined,
            formalObtainBody: node.formalObtainBody
                ? astmgr.clone(node.formalObtainBody) : undefined,
            obtainEmpRule: node.obtainEmpRule,
            obtainEeRule: node.obtainEeRule,
            revertSource: this.cloneSource(node.revertSource),
            rwBefore: node.rwBefore ? astmgr.clone(node.rwBefore) : undefined,
            rwAfter: node.rwAfter ? astmgr.clone(node.rwAfter) : undefined,
            rwSourceTerm: node.rwSourceTerm ? astmgr.clone(node.rwSourceTerm) : undefined,
            rwDestinationTerm: node.rwDestinationTerm ? astmgr.clone(node.rwDestinationTerm) : undefined,
            rwReverse: node.rwReverse,
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

    /**
     * Collect theorem-list premises once for both named-qed recording and
     * deferred replay.  For named qed, the selected page's leading hypotheses
     * define the theorem scope, matching the legacy `hyp ...; m name` flow, so
     * retain them even when the proof tree does not reference every hypothesis
     * directly. Bare qed keeps its existing minimal-dependency behavior.
     * Proof-tree traversal order is not the user's premise order: an `apply`
     * can expose p1 before a later branch consumes p0.  Keep the first-seen
     * order of distinct pages for cross-page compatibility, but restore the
     * explicit row order within each page.
     */
    private collectExternalPremiseRefs(includePageScope = false): {
        pageId: string;
        index: number;
        proposition: Proposition;
    }[] {
        const selectedPage = this.fs.inferencePages.page(this.pageId);
        const result = new Map<string, {
            pageId: string;
            index: number;
            proposition: Proposition;
            pageOrder: number;
        }>();
        const pageOrder = new Map<string, number>();
        if (!selectedPage) throw new Error(TR("推理表不存在"));
        if (includePageScope) {
            pageOrder.set(selectedPage.id, 0);
            const firstDerived = selectedPage.propositions.findIndex(proposition => !!proposition.from);
            const hypothesisCount = firstDerived === -1
                ? selectedPage.propositions.length
                : firstDerived;
            for (let index = 0; index < hypothesisCount; index++) {
                result.set(`${selectedPage.id}:${index}`, {
                    pageId: selectedPage.id,
                    index,
                    proposition: selectedPage.propositions[index],
                    pageOrder: 0
                });
            }
        }
        const visit = (node: DraftNode | null) => {
            if (!node) return;
            const sources = node.kind === "tauto"
                ? (node.tautoSources ?? [])
                : [
                    node.kind === "haveApply"
                        ? node.haveSource
                        : node.kind === "obtainExists"
                            ? node.obtainSource
                            : node.source,
                    ...(node.kind === "haveApply"
                        ? (node.haveArgumentSources ?? []).filter((source): source is SourceRef => !!source)
                        : [])
                ];
            for (const source of sources) {
                if (!source || source.kind !== "page") continue;
                const key = `${source.pageId}:${source.index}`;
                if (result.has(key)) continue;
                const proposition = this.fs.inferencePages.page(source.pageId)?.propositions[source.index];
                if (!proposition) throw new Error(TR("证明助手引用了不存在的推理表定理"));
                if (!pageOrder.has(source.pageId)) pageOrder.set(source.pageId, pageOrder.size);
                result.set(key, {
                    pageId: source.pageId,
                    index: source.index,
                    proposition,
                    pageOrder: pageOrder.get(source.pageId)!
                });
            }
            node.children.forEach(visit);
        };
        visit(this.root);
        return [...result.values()]
            .sort((left, right) => left.pageOrder - right.pageOrder || left.index - right.index)
            .map(({ pageId, index, proposition }) => ({ pageId, index, proposition }));
    }

    private collectExternalPremises(includePageScope = false): DeferredAssistantPayload["premises"] {
        return this.collectExternalPremiseRefs(includePageScope).map(({ pageId, index, proposition }) => ({
            pageId,
            index,
            value: astmgr.clone(proposition.value)
        }));
    }

    private buildDeferredQed(name?: string, preferredName?: string): {
        deductionName?: string;
        value: AST;
        row: InferenceProofMaterializedProposition;
        step: DeductionStep;
        payload: DeferredAssistantPayload;
    } {
        const premises = this.collectExternalPremises(name !== undefined);
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
            allowIfft: this.allowIfft,
            allowIfftEu: this.allowIfftEu,
            premises: premises.map(premise => ({
                pageId: premise.pageId,
                index: premise.index,
                value: astmgr.clone(premise.value)
            }))
        };
        const generatedByTauto = this.history.some(command => /^tauto(?:\s|$)/.test(command.trim()));
        const step: DeductionStep = {
            deductionIdx: deductionName ?? DEFERRED_ASSISTANT_STEP,
            conditionIdxs: premises.map(premise => premise.index),
            replaceValues: [],
            ...(generatedByTauto ? { info: "tauto" } : {}),
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
                    ...(step.info !== undefined ? { info: step.info } : {}),
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
                    ...(row.from.info !== undefined ? { info: row.from.info } : {}),
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
            case "rintro": return this.rintro(args);
            case "exact": return this.exact(args);
            case "apply": return this.applyRule(args);
            case "specialize": return this.specialize(args);
            case "use": return this.use(args);
            case "have": return this.have(args);
            case "obtain": return this.obtain(args);
            case "cases": return this.cases(args);
            case "rcases": return this.cases(args);
            case "revert": return this.revert(args);
            case "change": return this.change(args);
            case "show": return this.show(args);
            case "assumption": return this.assumption(args);
            case "constructor": return this.constructorStrategy(args);
            case "left": return this.disjunctionStrategy("left", args);
            case "right": return this.disjunctionStrategy("right", args);
            case "symm": return this.symm(args);
            case "rfl": return this.rfl(args);
            case "rw": return this.rewrite(args);
            case "nth_rw": return this.nthRewrite(args);
            case "simp": return this.simplify(args);
            case "simpa": return this.simpa(args);
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
            // Implication intro can discharge its temporary hypothesis through
            // the conditional-deduction path.  The inverse-deduction prefix is
            // only an optional shorter route selected during materialization.
            ? this.canUseFastMetaRule("c")
            : this.canUseFastMetaRule("v");
    }

    private assertIntroMetaRule(target: AST): void {
        if (target.name === ">" && !this.canUseFastMetaRule("c")) {
            throw new Error(TR("intro需要解锁条件演绎元定理；请先解锁元定理 c，使 (...Γ⊢Q) 变为 (S>...Γ)⊢(S>Q)"));
        }
        if (target.name === "V" && !this.canUseFastMetaRule("v")) {
            throw new Error(TR("intro需要解锁条件概括元定理；请先解锁元定理 v，使 (...Γ⊢Q) 变为 (Vx:...Γ)⊢(Vx:Q)"));
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

    /** Lean's `rintro`: introduce binders and destruct one simple pattern. */
    private rintro(argument: string): void {
        const patterns = this.splitRintroPatterns(argument.trim());
        if (!patterns.length) throw new Error(TR("rintro需要至少一个模式"));
        for (const pattern of patterns) {
            if (/^[^\s,<>⟨⟩|()]+$/.test(pattern)) {
                this.intro(pattern === "_" ? "" : pattern);
                continue;
            }
            const pair = /^[<⟨]\s*([^,\s<>⟨⟩]+)\s*,\s*([^,\s<>⟨⟩]+)\s*[>⟩]$/.exec(pattern);
            const branch = /^\(\s*([^|\s()]+)\s*\|\s*([^|\s()]+)\s*\)$/.exec(pattern);
            if (!pair && !branch) throw new Error(TR("rintro暂不支持该模式：") + pattern);
            const node = this.requireCurrentNode();
            const temporary = this.nextHypothesisName(node);
            this.intro(temporary);
            if (pair) this.cases(`${temporary} with ${pair[1]} ${pair[2]}`);
            else this.cases(`${temporary} with ${branch[1]} | ${branch[2]}`);
        }
    }

    private splitRintroPatterns(value: string): string[] {
        const patterns: string[] = [];
        let current = "";
        let depth = 0;
        const push = () => {
            const pattern = current.trim();
            if (pattern) patterns.push(pattern);
            current = "";
        };
        for (const character of value) {
            if (/\s/.test(character) && depth === 0) {
                push();
                continue;
            }
            current += character;
            if ("(<⟨".includes(character)) depth++;
            else if (")>⟩".includes(character)) depth = Math.max(0, depth - 1);
        }
        push();
        return patterns;
    }

    /** Change the current proposition to an assertion-equivalent surface form. */
    private change(argument: string): void {
        const value = argument.trim();
        if (!value) throw new Error(TR("change需要一个目标命题"));
        const node = this.requireCurrentNode();
        const target = this.parseProposition(value);
        this.assertSameProposition(node.target, target);
        node.target = astmgr.clone(target);
    }

    /** Lean's `show` spelling for `change`. */
    private show(argument: string): void {
        this.change(argument);
    }

    private introNode(node: DraftNode, name: string): void {
        if (name && !/^[^\s,]+$/.test(name)) throw new Error(TR("intro名称无效"));
        const target = node.target;
        // Rule instantiation can leave an outer #rp that only substituted an
        // already-eliminated quantifier variable.  It prevents the tactic
        // layer from seeing the leading V, but it carries no remaining formal
        // dependency.  Strip that one inert shell without simplifying nested
        // #nf/#rp terms required by explicit .Vcn/.Ecn materialization.
        const formalTarget = this.stripInertFormalReplacement(node.formalTarget);
        node.formalTarget = astmgr.clone(formalTarget);
        if (target.type !== "sym" || ![">", "V"].includes(target.name)) {
            throw new Error(TR("intro只能处理蕴含或全称量词"));
        }
        if (formalTarget.type !== "sym" || formalTarget.name !== target.name
            || formalTarget.nodes?.length !== 2) {
            throw new Error(TR("intro目标的形式化结构无效"));
        }
        this.assertIntroMetaRule(target);
        if (target.name === ">") {
            const proposition = astmgr.clone(target.nodes[0]);
            const formalProposition = astmgr.clone(formalTarget.nodes[0]);
            const hypothesis: InferenceProofHypothesis = {
                name: name || this.nextHypothesisName(node),
                proposition,
                formalProposition,
                kind: "intro"
            };
            this.assertUniqueHypothesis(node, hypothesis.name);
            node.hypotheses = [...node.hypotheses, hypothesis];
            node.introBindings.push(hypothesis);
            node.target = astmgr.clone(target.nodes[1]);
            node.formalTarget = astmgr.clone(formalTarget.nodes[1]);
            return;
        }

        const binder = target.nodes[0];
        if (binder.type !== "replvar") throw new Error(TR("全称量词约束变量无效"));
        const replacement = name || this.nextHypothesisName(node);
        if (!/^[^\s,]+$/.test(replacement)) throw new Error(TR("intro名称无效"));
        this.assertUniqueHypothesis(node, replacement);
        node.target = this.substituteBound(target.nodes[1], binder.name, replacement);
        const formalBinder = formalTarget.nodes[0];
        if (formalBinder.type !== "replvar") throw new Error(TR("全称量词形式化约束变量无效"));
        node.formalTarget = this.substituteBound(formalTarget.nodes[1], formalBinder.name, replacement);
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
        const normalizedTarget = this.normalizeAssertionSyntax(node.target, true);
        if (source.kind !== "rule") {
            const normalizedSource = this.normalizeAssertionSyntax(this.getSourceProposition(source, node), true);
            this.assertSameProposition(normalizedSource, normalizedTarget);
        } else {
            const deduction = this.requireDeduction(source.name);
            if (deduction.conditions.length) throw new Error(TR("该规则包含条件，请使用apply"));
            const match = this.matchConclusion(deduction, normalizedTarget, {
                positional: [],
                named: new Map()
            }, deduction.conclusion, node);
            this.assertRuleMatchComplete(match, source.name);
            source.replaceValues = deduction.replaceNames.map(name => {
                const value = match.matchTable[match.context.internalByOriginal.get(name)!];
                if (!value) throw new Error(TR("无法从目标推断规则参数") + name);
                return astmgr.clone(value);
            });
            node.formalReplaceValues = this.preserveFormalAssertions
                ? this.deriveFormalReplaceValues(source.replaceValues, node.target, node.formalTarget)
                : source.replaceValues.map(value => astmgr.clone(value));
            const formalMatchTable = this.withFormalRuleMatchValues(
                deduction, match.context, match.matchTable, node.formalReplaceValues
            );
            node.formalAppliedProposition = this.preserveFormalAssertions
                ? this.stripInertFormalRuleAssertion(
                    this.instantiateRuleAst(deduction.conclusion, match.context, formalMatchTable)
                )
                : astmgr.clone(normalizedTarget);
            this.fs.assert.checkGrammer(node.formalAppliedProposition, "p");
        }
        node.target = normalizedTarget;
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
            if (!rule) this.missingStrategyRule(".&", "constructor需要解锁合取构造规则或提供等价推理规则");
            this.applyRule(rule.name);
            return;
        }
        if (node.target.name === "<>") {
            const rule = this.resolveStrategyRule(".<>");
            if (!rule) this.missingStrategyRule(".<>", "constructor需要解锁等价构造规则或提供等价推理规则");
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
        if (!rule) this.missingStrategyRule(ruleName, side + "需要解锁析取构造规则或提供等价推理规则");
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
        if (!rule) this.missingStrategyRule(node.target.name === "=" ? ".=s" : ".<>s", "symm需要解锁对称规则或提供等价推理规则");
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
        if (!rule) this.missingStrategyRule("a7", "rfl需要解锁等式自反规则或提供等价推理规则");
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

    /** Lean-style `simpa`, optionally closing the goal with `using source`. */
    private simpa(argument: string): void {
        const value = argument.trim();
        const usingMatch = /^(?:(.*?)\s+)?using\s+([^\s]+)$/.exec(value);
        if (!usingMatch) {
            this.simplify(value);
            return;
        }
        this.simplify(usingMatch[1]?.trim() ?? "");
        this.exact(usingMatch[2]);
    }

    /**
     * Lean-style case splitting for a local conjunction, equivalence,
     * existential, or disjunction.  The compact `with a b` form names the
     * generated facts; without names the usual h1/h2 names are selected.
     */
    private cases(argument: string): void {
        const value = argument.trim();
        const match = /^([^\s]+)(?:\s+with\s+([\s\S]+))?$/i.exec(value);
        if (!match) throw new Error(TR("cases语法应为 cases h [with h1 h2]"));
        const sourceName = match[1];
        const node = this.requireCurrentNode();
        const source = this.resolveSource(sourceName, node);
        if (source.kind === "rule") throw new Error(TR("cases来源必须是假设或页面命题"));
        const proposition = this.getSourceProposition(source, node);
        if (proposition.type !== "sym" || !["&", "<>", "|", "E"].includes(proposition.name)
            || proposition.nodes?.length !== 2) {
            throw new Error(TR("cases来源必须是合取、等价、析取或存在命题"));
        }
        const names = this.parseCasesNames(match[2] ?? "", node);
        if (proposition.name === "|" && names.length === 2) {
            this.obtain(`${names[0]} | ${names[1]} := ${sourceName}`);
            return;
        }
        if (names.length !== 2) throw new Error(TR("cases需要两个分支名称"));
        this.obtain(`⟨${names[0]},${names[1]}⟩ := ${sourceName}`);
    }

    /** Lean's `rcases` is the pattern-oriented spelling of `cases`. */
    private rcases(argument: string): void {
        this.cases(argument);
    }

    private parseCasesNames(value: string, node: DraftNode): string[] {
        if (!value.trim()) return this.nextHypothesisNames(node, 2);
        const pair = /[⟨<]\s*([^,\s<>⟩]+)\s*,\s*([^,\s<>⟩]+)\s*[⟩>]/.exec(value);
        if (pair) return [pair[1], pair[2]];
        const branchNames: string[] = [];
        for (const branch of value.split("|")) {
            const tokens = branch.trim().split(/\s+/).filter(Boolean);
            const candidate = tokens.at(-1)?.replace(/=>$/, "");
            if (candidate && /^[^\s,|<>⟩]+$/.test(candidate)
                && !["inl", "inr", "left", "right", "zero", "succ"].includes(candidate)) {
                branchNames.push(candidate);
            }
        }
        if (branchNames.length === 2) return branchNames;
        return value.split(/[\s,]+/).filter(name => /^[^\s,|<>⟩]+$/.test(name));
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
        if (equality.type === "sym" && equality.name === "<>" && equality.nodes?.length === 2) {
            this.rewriteWithIffSource(sourceText, reverse, nth, source, equality);
            return;
        }
        if (equality.type !== "sym" || equality.name !== "=" || equality.nodes?.length !== 2) {
            throw new Error(TR("rw来源必须是等式或等价命题"));
        }
        const sourceTerm = reverse ? equality.nodes[1] : equality.nodes[0];
        const destinationTerm = reverse ? equality.nodes[0] : equality.nodes[1];
        const substitution = this.resolveStrategyRule("a8");
        if (!substitution) this.missingStrategyRule("a8", "rw需要解锁等式替换规则或提供等价推理规则");
        const symmetry = reverse ? undefined : this.resolveStrategyRule(".=s");
        if (!reverse && !symmetry) this.missingStrategyRule(".=s", "rw正向改写需要解锁等式对称规则或提供等价推理规则");
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

    private canRewriteIffTarget(target: AST, proposition: AST, reverse: boolean,
        available = this.availableRuleNames): boolean {
        if (!this.allowIfft || !this.resolveStrategyRule(reverse ? ".<>1" : ".<>2", available)) {
            return false;
        }
        if (proposition.type !== "sym" || proposition.name !== "<>" || proposition.nodes?.length !== 2) {
            return false;
        }
        const source = reverse ? proposition.nodes[1] : proposition.nodes[0];
        const destination = reverse ? proposition.nodes[0] : proposition.nodes[1];
        try {
            const steps = this.planRewrite(target, source, destination, null);
            return steps.length > 0 && steps.every(step => {
                try {
                    const pair = this.findRewritePair(step.before, step.after, source, destination);
                    this.assertIffContextSupported(step.before, step.after,
                        pair.source, pair.destination, available);
                    return true;
                } catch {
                    return false;
                }
            });
        } catch {
            return false;
        }
    }

    /**
     * Rewrite through a local/page iff proposition.  The draft keeps this as
     * one atomic node; materialization derives the contextual iff lazily from
     * the existing `.<>r*` rules and then selects the required direction.
     */
    private rewriteWithIffSource(sourceText: string, reverse: boolean, nth: number | null,
        source: Exclude<SourceRef, { kind: "rule" }>, iff: AST): void {
        if (!this.allowIfft) {
            throw new Error(TR("rw等价改写需要解锁互推替换元定理(ifft)"));
        }
        const left = iff.nodes?.[0];
        const right = iff.nodes?.[1];
        if (!left || !right) throw new Error(TR("rw来源等价命题结构无效"));
        const sourceTerm = reverse ? right : left;
        const destinationTerm = reverse ? left : right;
        const directionRule = reverse ? ".<>1" : ".<>2";
        if (!this.resolveStrategyRule(directionRule)) {
            this.missingStrategyRule(directionRule,
                "rw等价改写需要解锁互推方向规则或提供等价推理规则");
        }
        const steps = this.planRewrite(this.requireCurrentNode().target,
            sourceTerm, destinationTerm, nth);
        const pairs = steps.map(step => {
            const pair = this.findRewritePair(step.before, step.after, sourceTerm, destinationTerm);
            this.assertIffContextSupported(step.before, step.after,
                pair.source, pair.destination);
            return pair;
        });
        for (let index = 0; index < steps.length; index++) {
            const step = steps[index];
            const pair = pairs[index];
            const node = this.requireCurrentNode();
            this.assertSameProposition(node.target, step.before);
            const child = this.makeNode(step.after, this.cloneHypotheses(node.hypotheses), step.after);
            node.kind = "rwIff";
            node.source = this.cloneSource(source);
            node.rwBefore = astmgr.clone(step.before);
            node.rwAfter = astmgr.clone(step.after);
            node.rwSourceTerm = astmgr.clone(pair.source);
            node.rwDestinationTerm = astmgr.clone(pair.destination);
            node.rwReverse = reverse;
            node.children = [child];
            node.target = astmgr.clone(step.after);
            node.formalTarget = astmgr.clone(step.after);
        }
    }

    /** Find the concrete subtree changed by one planned replacement. */
    private findRewritePair(before: AST, after: AST, source: AST, destination: AST): {
        source: AST; destination: AST;
    } {
        const paths: number[][] = [];
        const collect = (ast: AST, path: number[]) => {
            paths.push(path);
            ast.nodes?.forEach((_, index) => collect(ast.nodes![index], [...path, index]));
        };
        const getAt = (ast: AST, path: number[]): AST => {
            let current = ast;
            for (const index of path) current = current.nodes?.[index] as AST;
            return current;
        };
        const replaceAt = (ast: AST, path: number[], value: AST): void => {
            if (!path.length) {
                astmgr.assign(ast, value);
                return;
            }
            const parent = getAt(ast, path.slice(0, -1));
            if (!parent.nodes) throw new Error(TR("rw替换位置无效"));
            parent.nodes[path[path.length - 1]] = astmgr.clone(value);
        };
        collect(before, []);
        for (const path of paths) {
            const candidate = getAt(before, path);
            const matched: ReplvarMatchTable = {};
            try {
                this.fs.assert.match(candidate, source, /^\$/, false, matched, {}, null, []);
            } catch {
                continue;
            }
            const concreteDestination = astmgr.clone(destination);
            astmgr.replaceByMatchTable(concreteDestination, matched);
            const trial = astmgr.clone(before);
            replaceAt(trial, path, concreteDestination);
            if (astmgr.equal(trial, after)) {
                return { source: astmgr.clone(candidate), destination: concreteDestination };
            }
        }
        throw new Error(TR("rw无法定位等价改写位置"));
    }

    /** Validate the structural fragment supported by iff contextual lifting. */
    private assertIffContextSupported(before: AST, after: AST,
        baseSource: AST, baseDestination: AST,
        available = this.availableRuleNames): void {
        if (astmgr.equal(before, baseSource) && astmgr.equal(after, baseDestination)) return;
        if (astmgr.equal(before, after)) {
            const identity = this.resolveStrategyRule(".<>i", available);
            if (!identity) {
                const direct = this.resolveStrategyRule(".<>", available);
                if (!direct || !this.resolveStrategyRule(".i", available)) {
                    throw new Error(TR("rw等价改写需要解锁等价自反规则：.<>i"));
                }
            }
            return;
        }
        if (before.type !== after.type || before.name !== after.name
            || before.nodes?.length !== after.nodes?.length) {
            throw new Error(TR("rw等价改写暂不支持该函数或关系上下文"));
        }
        if (before.type !== "sym"
            || ![">", "<>", "&", "|", "~", "V", "E", "E!"].includes(before.name)) {
            throw new Error(TR("rw等价改写暂不支持该函数或关系上下文"));
        }
        if (before.name === "V" || before.name === "E" || before.name === "E!") {
            if (before.name === "E!" && !this.allowIfftEu) {
                throw new Error(TR("rw等价改写跨E!需要解锁ifft-EU"));
            }
            if (!astmgr.equal(before.nodes?.[0], after.nodes?.[0])) {
                throw new Error(TR("rw等价改写暂不支持绑定变量名不同的量词上下文"));
            }
        }
        const contextRule = ".<>r" + before.name;
        if (!this.resolveStrategyRule(contextRule, available)) {
            throw new Error(TR("rw等价改写需要解锁上下文等价规则：") + contextRule);
        }
        for (let index = 0; index < (before.nodes?.length ?? 0); index++) {
            if ((before.name === "V" || before.name === "E" || before.name === "E!")
                && index === 0) continue;
            this.assertIffContextSupported(before.nodes![index], after.nodes![index],
                baseSource, baseDestination, available);
        }
        if (before.name === "V" || before.name === "E" || before.name === "E!") {
            if (!this.resolveStrategyRule("a6", available)) {
                throw new Error(TR("rw等价改写量词上下文需要解锁全称概括规则a6"));
            }
        }
    }

    private planRewrite(target: AST, source: AST, destination: AST, nth: number | null): RewriteStep[] {
        if (astmgr.equal(source, destination)) throw new Error(TR("rw等式两端相同，没有可执行的改写"));
        // Concrete sources can be found independently of unrelated user
        // metavariables in the target.  Schematic sources still require the
        // assertion matcher’s strict unknown/capture analysis.
        const allowUnknownOutsideMatch = Object.keys(
            this.fs.assert.getVarNamesAndIsNots(source, {}, null)
        ).length === 0;
        const probe = astmgr.clone(target);
        const allMatches = this.fs.assert.getSubAstMatchTimesAndReplace(
            probe, astmgr.clone(source), astmgr.clone(destination), -1, [], [], false,
            allowUnknownOutsideMatch
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
                after, astmgr.clone(source), astmgr.clone(destination), index, [], [], false,
                allowUnknownOutsideMatch
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
            probe, astmgr.clone(source), astmgr.clone(destination), -1, [], [], false,
            Object.keys(this.fs.assert.getVarNamesAndIsNots(source, {}, null)).length === 0
        );
        if (matches === false) throw new Error(TR("rw无法构造反向替换证明"));
        for (let index = 0; index < matches.length; index++) {
            const candidate = astmgr.clone(after);
            const result = this.fs.assert.getSubAstMatchTimesAndReplace(
                candidate, astmgr.clone(source), astmgr.clone(destination), index, [], [], false,
                Object.keys(this.fs.assert.getVarNamesAndIsNots(source, {}, null)).length === 0
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
        if (!pair) throw new Error(TR("未找到相反命题假设或定理"));
        const rule = this.resolveStrategyRule(".m");
        if (!rule) this.missingStrategyRule(".m", "contradiction需要解锁矛盾规则或提供等价推理规则");
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
        if (!rule) this.missingStrategyRule(".mn", "by_contra需要解锁反证规则或提供等价推理规则");
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
        if (!rule) this.missingStrategyRule(".m2", "by_cases需要解锁分类讨论规则或提供等价推理规则");
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
        if (!rule) this.missingStrategyRule("a3", "contrapose需要解锁逆否规则或提供等价推理规则");
        this.applyRule(rule.name);
    }

    private applyRule(argument: string): void {
        const atMatch = /^(.*)\s+at\s+([^\s]+)$/.exec(argument.trim());
        if (atMatch && atMatch[1].trim()) {
            this.applyAt(atMatch[1].trim(), atMatch[2]);
            return;
        }
        const node = this.requireCurrentNode();
        const parts = argument.trim() ? argument.trim().split(/\s+/) : [];
        if (!parts.length) throw new Error(TR("apply需要一个证明来源或推理规则"));
        const sourceName = parts.shift();
        if (sourceName === "_") throw new Error(TR("推理层证明助手暂不支持_模糊匹配"));
        const source = this.resolveSource(sourceName, node);
        if (source.kind === "rule") {
            const deduction = this.requireDeduction(source.name);
            const explicit = this.parseRuleArguments(parts, deduction);
            const preserveSchematicAssertions = this.explicitArgumentsContainSchematicAssertions(
                explicit, deduction
            );
            const application = this.matchRuleApplication(deduction, node.target, explicit, node);
            this.assertRuleMatchComplete(application, source.name);
            const matchTable = application.matchTable;
            const implicationPremises = application.premises;
            const replaceValues = deduction.replaceNames.map(name => {
                const value = matchTable[application.context.internalByOriginal.get(name)!];
                if (!value) throw new Error(TR("无法从目标推断规则参数") + name);
                return astmgr.clone(value);
            });
            const formalReplaceValues = this.preserveFormalAssertions
                ? this.deriveFormalReplaceValues(replaceValues, node.target, node.formalTarget)
                : replaceValues.map(value => astmgr.clone(value));
            const formalMatchTable = this.withFormalRuleMatchValues(
                deduction, application.context, matchTable, formalReplaceValues
            );
            const instantiate = (value: AST, preserveSurfaceAssertions = false) => {
                const result = this.instantiateRuleAst(value, application.context, matchTable);
                if (this.astContainsPrivateRuleVariable(result)) {
                    if (this.astContainsFunction(result, "#rp")) this.fs.assert.expand(result, false);
                } else {
                    astmgr.assign(result, this.normalizeAssertionSyntax(
                        result, !(preserveSchematicAssertions || preserveSurfaceAssertions)
                    ));
                }
                this.fs.assert.checkGrammer(result, "p");
                return result;
            };
            const instantiateFormal = (value: AST) => {
                const result = this.instantiateRuleAst(value, application.context, formalMatchTable);
                if (this.astContainsPrivateRuleVariable(result)) {
                    throw new Error(TR("推理规则仍包含未解析的元变量"));
                }
                this.fs.assert.checkGrammer(result, "p");
                return this.stripInertFormalRuleAssertion(result);
            };
            const conditions = [
                ...application.context.conditions,
                ...implicationPremises.map(condition => this.renameRuleMetavariables(
                    astmgr.clone(condition), application.context.internalByOriginal
                ))
            ].map(condition => {
                return instantiate(condition);
            });
            const formalConditions = this.preserveFormalAssertions
                ? [
                    ...application.context.conditions,
                    ...implicationPremises.map(condition => this.renameRuleMetavariables(
                        astmgr.clone(condition), application.context.internalByOriginal
                    ))
                ].map(instantiateFormal)
                : conditions.map(condition => astmgr.clone(condition));
            node.kind = "apply";
            node.source = source;
            node.ruleName = source.name;
            node.replaceValues = replaceValues;
            node.formalReplaceValues = formalReplaceValues;
            // Tactics operate on normalized child goals, but the emitted rule
            // must retain an explicit #rp/#nf conclusion.  In particular,
            // `use` followed by an explicit .Vcn/.Ecn needs that formal
            // bridge when qed conditionally lifts the proof graph.
            node.appliedProposition = instantiate(
                deduction.conclusion, this.containsSchematicAssertion(node.target)
            );
            node.formalAppliedProposition = this.preserveFormalAssertions
                ? instantiateFormal(deduction.conclusion)
                : astmgr.clone(node.appliedProposition);
            node.ruleConditionCount = deduction.conditions.length;
            node.children = conditions.map((condition, index) => this.makeNode(
                condition, this.cloneHypotheses(node.hypotheses), formalConditions[index]
            ));
            return;
        }

        if (parts.length) throw new Error(TR("对假设或定理使用apply时不能附加参数"));
        const proposition = this.getSourceProposition(source, node);
        const formalProposition = this.getSourceFormalProposition(source, node);
        const application = this.matchPropositionApplication(proposition, node.target);
        const matchTable = application.matchTable;
        const appliedProposition = astmgr.clone(proposition);
        astmgr.replaceByMatchTable(appliedProposition, matchTable);
        const formalAppliedProposition = astmgr.clone(formalProposition);
        astmgr.replaceByMatchTable(formalAppliedProposition, matchTable);
        const instantiatedPremises = application.premises.map(premise => {
            const result = astmgr.clone(premise);
            astmgr.replaceByMatchTable(result, matchTable);
            return result;
        });
        const formalPremises: AST[] = [];
        let formalConclusion = astmgr.clone(formalAppliedProposition);
        for (let index = 0; index < instantiatedPremises.length; index++) {
            if (formalConclusion.type !== "sym" || formalConclusion.name !== ">"
                || formalConclusion.nodes?.length !== 2) {
                throw new Error(TR("证明来源的形式化蕴含层数无效"));
            }
            formalPremises.push(astmgr.clone(formalConclusion.nodes[0]));
            formalConclusion = astmgr.clone(formalConclusion.nodes[1]);
        }
        if (!instantiatedPremises.length) {
            this.assertSameProposition(appliedProposition, node.target);
            node.kind = "exact";
            node.source = source;
            node.ruleName = undefined;
            node.replaceValues = undefined;
            node.formalReplaceValues = undefined;
            node.appliedProposition = undefined;
            node.formalAppliedProposition = formalAppliedProposition;
            node.ruleConditionCount = undefined;
            node.children = [];
            return;
        }
        node.kind = "apply";
        node.source = source;
        node.ruleName = undefined;
        node.replaceValues = undefined;
        node.formalReplaceValues = undefined;
        node.appliedProposition = appliedProposition;
        node.formalAppliedProposition = formalAppliedProposition;
        node.ruleConditionCount = 0;
        node.children = instantiatedPremises.map((condition, index) => this.makeNode(
            condition, this.cloneHypotheses(node.hypotheses), formalPremises[index]
        ));
    }

    /** Lean-style `apply source at h`, transforming a local proposition. */
    private applyAt(sourceText: string, hypothesisName: string): void {
        const node = this.requireCurrentNode();
        const hypothesis = node.hypotheses.find(item => item.name === hypothesisName && !!item.proposition);
        if (!hypothesis?.proposition) throw new Error(TR("未找到要应用的假设：") + hypothesisName);
        const parts = this.splitApplicationTerms(sourceText);
        if (!parts.length) throw new Error(TR("apply at需要一个证明来源"));
        const sourceName = parts.shift()!;
        if (sourceName === "_") throw new Error(TR("推理层证明助手暂不支持_模糊匹配"));
        const source = this.resolveSource(sourceName, node);

        if (source.kind !== "rule") {
            const sourceProposition = this.getSourceProposition(source, node);
            const application = this.instantiateHaveApplication(
                sourceProposition,
                [...parts, hypothesisName],
                node
            );
            const continuationHypotheses = this.cloneHypotheses(node.hypotheses)
                .filter(item => item.name !== hypothesisName);
            continuationHypotheses.push({
                name: hypothesisName,
                proposition: astmgr.clone(application.proposition),
                kind: "have"
            });
            const continuation = this.makeNode(node.target, continuationHypotheses);
            node.kind = "haveApply";
            node.haveName = hypothesisName;
            node.haveSource = this.cloneSource(source);
            node.haveArguments = application.arguments.map(value => astmgr.clone(value));
            node.haveArgumentSources = application.sources.map(value => this.cloneSource(value) ?? null);
            node.haveProposition = astmgr.clone(application.proposition);
            node.children = [continuation];
            return;
        }

        const deduction = this.requireDeduction(source.name);
        if (!deduction.conditions.length) {
            throw new Error(TR("apply at来源规则必须至少有一个前件"));
        }
        const explicit = this.parseRuleArguments(parts, deduction);
        const preserveSchematicAssertions = this.explicitArgumentsContainSchematicAssertions(
            explicit, deduction
        );
        const context = this.createRuleMetavariableContext(deduction, hypothesis.proposition, explicit, node);
        const match = this.matchConclusion(
            deduction,
            hypothesis.proposition,
            explicit,
            deduction.conditions[0],
            node,
            context,
            [deduction.conditions[0]]
        );
        this.assertRuleMatchComplete(match, source.name);
        const instantiate = (value: AST) => {
            const result = this.instantiateRuleAst(value, context, match.matchTable);
            if (this.astContainsPrivateRuleVariable(result)) {
                if (this.astContainsFunction(result, "#rp")) this.fs.assert.expand(result, false);
            } else {
                astmgr.assign(result, this.normalizeAssertionSyntax(result, !preserveSchematicAssertions));
            }
            this.fs.assert.checkGrammer(result, "p");
            return result;
        };
        const conditions = deduction.conditions.map(instantiate);
        this.assertSameProposition(conditions[0], hypothesis.proposition);
        const conclusion = instantiate(deduction.conclusion);
        const replaceValues = deduction.replaceNames.map(name => {
            const value = match.matchTable[context.internalByOriginal.get(name)!];
            if (!value) throw new Error(TR("无法从目标推断规则参数") + name);
            return astmgr.clone(value);
        });
        const continuationHypotheses = this.cloneHypotheses(node.hypotheses)
            .filter(item => item.name !== hypothesisName);
        continuationHypotheses.push({
            name: hypothesisName,
            proposition: astmgr.clone(conclusion),
            kind: "have"
        });
        const continuation = this.makeNode(node.target, continuationHypotheses);
        node.kind = "applyAt";
        node.applyAtHypothesis = hypothesisName;
        node.source = {
            kind: "rule",
            name: source.name,
            replaceValues
        };
        node.ruleName = source.name;
        node.replaceValues = replaceValues.map(value => astmgr.clone(value));
        node.appliedProposition = astmgr.clone(conclusion);
        node.ruleConditionCount = deduction.conditions.length;
        node.children = conditions.slice(1)
            .map(condition => this.makeNode(condition, this.cloneHypotheses(node.hypotheses)));
        node.children.push(continuation);
    }

    /** Lean-style `specialize h a ...`, replacing a local function fact. */
    private specialize(argument: string): void {
        const node = this.requireCurrentNode();
        const parts = this.splitApplicationTerms(argument.trim());
        if (parts.length < 2) throw new Error(TR("specialize语法应为 specialize h 参数..."));
        const sourceName = parts.shift()!;
        const hypothesis = node.hypotheses.find(item => item.name === sourceName && !!item.proposition);
        if (!hypothesis?.proposition) throw new Error(TR("specialize只能作用于局部假设：") + sourceName);
        if (hypothesis.kind === "variable") throw new Error(TR("specialize只能作用于命题假设：") + sourceName);
        const application = this.instantiateHaveApplication(hypothesis.proposition, parts, node);
        const continuationHypotheses = this.cloneHypotheses(node.hypotheses)
            .filter(item => item.name !== sourceName);
        continuationHypotheses.push({
            name: sourceName,
            proposition: astmgr.clone(application.proposition),
            kind: "have"
        });
        const continuation = this.makeNode(node.target, continuationHypotheses);
        node.kind = "haveApply";
        node.haveName = sourceName;
        node.haveSource = { kind: "hypothesis", name: sourceName, nodeId: hypothesis.sourceNodeId };
        node.haveArguments = application.arguments.map(value => astmgr.clone(value));
        node.haveArgumentSources = application.sources.map(value => this.cloneSource(value) ?? null);
        node.haveProposition = astmgr.clone(application.proposition);
        node.children = [continuation];
    }

    /** Introduce a concrete witness for an existential target through `.Erp`. */
    private use(argument: string): void {
        const value = argument.trim();
        if (!value) throw new Error(TR("use需要一个具体见证项"));
        const node = this.requireCurrentNode();
        if (node.target.type !== "sym" || node.target.name !== "E" || node.target.nodes?.length !== 2) {
            throw new Error(TR("use只能作用于存在量词目标"));
        }
        const rule = this.resolveStrategyRule(".Erp");
        if (!rule) this.missingStrategyRule(".Erp", "use需要解锁存在量词构造规则或提供等价推理规则");
        const witness = this.parsePropositionOrItem(value);
        const witnessMeta = rule.metavariables.get("$2") ?? "$2";
        this.applyRule(`${rule.name} ${witnessMeta}=${parser.stringifyTight(witness)}`);
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
                const deduction = this.requireDeduction(source.name);
                const explicit = this.parseRuleArguments(terms, deduction);
                const instantiated = this.instantiateRuleForHave(source.name, deduction, explicit, node);
                const ruleSource: SourceRef = {
                    kind: "rule",
                    name: source.name,
                    replaceValues: instantiated.replaceValues.map(value => astmgr.clone(value))
                };
                const subgoal = this.makeNode(instantiated.conclusion, this.cloneHypotheses(node.hypotheses));
                subgoal.kind = "apply";
                subgoal.source = ruleSource;
                subgoal.ruleName = source.name;
                subgoal.replaceValues = instantiated.replaceValues.map(value => astmgr.clone(value));
                subgoal.appliedProposition = astmgr.clone(instantiated.conclusion);
                subgoal.formalAppliedProposition = astmgr.clone(instantiated.conclusion);
                subgoal.ruleConditionCount = deduction.conditions.length;
                subgoal.children = instantiated.conditions.map(condition =>
                    this.makeNode(condition, this.cloneHypotheses(node.hypotheses)));
                const continuationHypotheses = this.cloneHypotheses(node.hypotheses);
                continuationHypotheses.push({
                    name,
                    proposition: astmgr.clone(instantiated.conclusion),
                    formalProposition: astmgr.clone(instantiated.conclusion),
                    kind: "have",
                    sourceNodeId: subgoal.id
                });
                const continuation = this.makeNode(node.target, continuationHypotheses, node.formalTarget);
                node.kind = "have";
                node.haveName = name;
                node.children = [subgoal, continuation];
                return;
            }
            const sourceProposition = this.getSourceProposition(source, node);
            const formalSourceProposition = this.getSourceFormalProposition(source, node);
            const application = this.instantiateHaveApplication(sourceProposition, terms, node);
            const args = application.arguments;
            const proposition = application.proposition;
            const formalProposition = this.instantiateFormalHaveApplication(formalSourceProposition, args);
            this.fs.assert.checkGrammer(proposition, "p");
            const continuationHypotheses = this.cloneHypotheses(node.hypotheses);
            continuationHypotheses.push({
                name,
                proposition: astmgr.clone(proposition),
                formalProposition: astmgr.clone(formalProposition),
                kind: "have"
            });
            const continuation = this.makeNode(node.target, continuationHypotheses, node.formalTarget);
            node.kind = "haveApply";
            node.haveName = name;
            node.haveSource = this.cloneSource(source);
            node.haveArguments = args.map(arg => astmgr.clone(arg));
            node.haveArgumentSources = application.sources.map(source => this.cloneSource(source) ?? null);
            node.haveProposition = astmgr.clone(proposition);
            node.formalHaveProposition = astmgr.clone(formalProposition);
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

    private createHaveGoal(node: DraftNode, name: string, proposition: AST,
        consumedHypothesis?: string, formalProposition: AST = proposition): void {
        const subgoal = this.makeNode(proposition, this.cloneHypotheses(node.hypotheses), formalProposition);
        const continuationHypotheses = this.cloneHypotheses(node.hypotheses)
            .filter(hypothesis => hypothesis.name !== consumedHypothesis);
        continuationHypotheses.push({
            name,
            proposition: astmgr.clone(proposition),
            formalProposition: astmgr.clone(formalProposition),
            kind: "have",
            sourceNodeId: subgoal.id
        });
        const continuation = this.makeNode(node.target, continuationHypotheses, node.formalTarget);
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
        const formalProposition = this.getSourceFormalProposition(source, node);
        if (proposition.type !== "sym" || proposition.nodes?.length !== 2) {
            throw new Error(TR("obtain来源必须是合取、等价或析取命题"));
        }

        if (proposition.name === "E") {
            this.obtainExistential(node, firstName, secondName, source, proposition, formalProposition);
            return;
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
            if (!rule) this.missingStrategyRule(canonicalRule, "obtain需要解锁消去规则或提供等价推理规则");
            const current = this.requireCurrentNode();
            this.createHaveGoal(current, index === 0 ? firstName : secondName, astmgr.clone(fact),
                source.kind === "hypothesis" && index === facts.length - 1 ? source.name : undefined);
            this.applyRule(rule.name);
            this.exact(sourceText);
        }
    }

    /** Introduce a witness variable and its proposition from an existential source. */
    private obtainExistential(node: DraftNode, variableName: string, hypothesisName: string,
        source: SourceRef, proposition: AST, formalProposition: AST = proposition): void {
        if (source.kind === "rule") throw new Error(TR("obtain只支持假设或页面命题来源"));
        const empRule = this.resolveStrategyRule(".Emp");
        if (!empRule) this.missingStrategyRule(".Emp", "obtain存在量词需要解锁存在量词消去规则或提供等价推理规则");
        const eeRule = this.resolveStrategyRule(".Ee");
        if (!eeRule) this.missingStrategyRule(".Ee", "obtain存在量词需要解锁存在命题消去规则或提供等价推理规则");
        const binder = astmgr.clone(proposition.nodes[0]);
        const binderName = this.fs.assert.getVarName(binder);
        if (!binderName) throw new Error(TR("obtain来源的存在量词变量无效"));
        if (!/^[^\s,]+$/.test(variableName) || !/^[^\s,]+$/.test(hypothesisName)) {
            throw new Error(TR("obtain生成的假设名称无效"));
        }
        const body = astmgr.clone(proposition.nodes[1]);
        const witnessProposition = this.substituteBound(body, binderName, variableName);
        this.fs.assert.checkGrammer(witnessProposition, "p");
        if (formalProposition.type !== "sym" || formalProposition.name !== "E"
            || formalProposition.nodes?.length !== 2) {
            throw new Error(TR("obtain来源的形式化存在量词无效"));
        }
        const formalBinder = astmgr.clone(formalProposition.nodes[0]);
        const formalBinderName = this.fs.assert.getVarName(formalBinder);
        if (!formalBinderName) throw new Error(TR("obtain来源的形式化存在变量无效"));
        const formalBody = astmgr.clone(formalProposition.nodes[1]);
        const formalWitnessProposition = this.substituteBound(formalBody, formalBinderName, variableName);

        const variable: InferenceProofHypothesis = {
            name: variableName,
            binder,
            kind: "variable"
        };
        const witnessHypothesis: InferenceProofHypothesis = {
            name: hypothesisName,
            proposition: astmgr.clone(witnessProposition),
            formalProposition: astmgr.clone(formalWitnessProposition),
            kind: "intro"
        };
        const continuationHypotheses = this.cloneHypotheses(node.hypotheses)
            .filter(hypothesis => source.kind !== "hypothesis" || hypothesis.name !== source.name);
        continuationHypotheses.push(variable, witnessHypothesis);
        const continuation = this.makeNode(node.target, continuationHypotheses, node.formalTarget);
        // The child proof is generalized back to
        // `Vx:(P x > target)` during materialization, then `.Emp`/`.Ee`
        // consume the original existential source.
        continuation.introBindings.push(variable, witnessHypothesis);

        node.kind = "obtainExists";
        node.obtainSource = this.cloneSource(source);
        node.obtainVariableName = variableName;
        node.obtainHypothesisName = hypothesisName;
        node.obtainBinder = binder;
        node.obtainBody = body;
        node.formalObtainBinder = formalBinder;
        node.formalObtainBody = formalBody;
        node.obtainEmpRule = empRule.name;
        node.obtainEeRule = eeRule.name;
        node.children = [continuation];
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
        if (!rule) this.missingStrategyRule(".|m", "obtain需要解锁析取消去规则或提供等价推理规则");
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
        if (source.kind === "hypothesis") {
            for (const child of node.children.slice(0, 2)) {
                child.hypotheses = child.hypotheses.filter(hypothesis => hypothesis.name !== source.name);
            }
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

    /**
     * Instantiate a Lean-style `have h := source ...` application.  Universal
     * binders consume ordinary terms, while implication binders consume proof
     * sources (hypotheses or page propositions) and are materialized as `mp`.
     * Keeping the two kinds tagged avoids treating a proof name as a literal
     * term when the application crosses both forms.
     */
    private instantiateHaveApplication(proposition: AST, terms: string[], node: DraftNode): {
        proposition: AST;
        arguments: AST[];
        sources: (SourceRef | null)[];
    } {
        let result = astmgr.clone(proposition);
        const argumentValues: AST[] = [];
        const sources: (SourceRef | null)[] = [];
        for (const term of terms) {
            if (result.type === "sym" && result.name === "V" && result.nodes?.length === 2) {
                const argument = this.parsePropositionOrItem(term);
                const binderName = this.fs.assert.getVarName(result.nodes[0]);
                if (!binderName) throw new Error(TR("have来源命题的全称量词变量无效"));
                result = this.substituteBoundValue(result.nodes[1], binderName, argument);
                argumentValues.push(argument);
                sources.push(null);
                continue;
            }
            if (result.type === "sym" && result.name === ">" && result.nodes?.length === 2) {
                const source = this.resolveSource(term, node);
                if (source.kind === "rule") {
                    throw new Error(TR("have蕴涵参数必须是假设或定理来源：") + term);
                }
                const sourceProposition = this.getSourceProposition(source, node);
                try {
                    this.assertSameProposition(sourceProposition, result.nodes[0]);
                } catch {
                    throw new Error(TR("have蕴涵参数与前件不匹配：") + term);
                }
                result = astmgr.clone(result.nodes[1]);
                // Retain a parsed placeholder for stable cloning/history; the
                // tagged source is authoritative when materializing the `mp`.
                argumentValues.push(this.parsePropositionOrItem(term));
                sources.push(this.cloneSource(source)!);
                continue;
            }
            throw new Error(TR("have应用参数过多，来源命题不是足够的全称或蕴涵命题"));
        }
        return { proposition: result, arguments: argumentValues, sources };
    }

    private tauto(argument: string): void {
        if (argument.trim()) throw new Error(TR("tauto不接受参数"));
        if (!this.allowMcpt) throw new Error(TR("尚未解锁MCPT，不能使用tauto"));
        const node = this.requireCurrentNode();
        // Prefer a closed tautology.  If the target is only tautological under
        // theorem-list propositions, check p0 > (p1 > target) and remember the
        // selected pN rows so materialization can apply inverse deduction later.
        let checkedTheorem = astmgr.clone(node.target);
        let tautoSources: SourceRef[] = [];
        if (this.isPurePropositionalSyntax(node.target)) {
            let targetError: unknown;
            try {
                new Proof(this.fs).assertTautology(node.target);
            } catch (error) {
                targetError = error;
                const candidate = this.findTautoPagePremises(node);
                if (!candidate) throw targetError;
                if (!this.canUseFastMetaRule("<")) {
                    throw new Error(TR("tauto使用定理表前提需要解锁逆演绎元定理"));
                }
                checkedTheorem = candidate.theorem;
                tautoSources = candidate.sources;
                new Proof(this.fs).assertTautology(checkedTheorem);
            }
        } else {
            new Proof(this.fs).assertTautology(node.target);
        }
        // Keep MCPT's exhaustive check as the authority.  Do not add a
        // generated rule here: applying a tactic is a draft-only operation and
        // must not mutate the shared FormalSystem.  The deferred rule is
        // created transactionally by commit() when the result is accepted.
        node.kind = "tauto";
        node.tautoSources = tautoSources.map(source => this.cloneSource(source)!);
        node.tautoTheorem = checkedTheorem;
        node.children = [];
    }

    private findTautoPagePremises(node: DraftNode): {
        sources: SourceRef[];
        theorem: AST;
    } | undefined {
        if (!this.isPurePropositionalSyntax(node.target)) return undefined;
        const page = this.fs.inferencePages.page(this.pageId);
        if (!page) return undefined;
        const candidates: { source: SourceRef; proposition: AST }[] = [];
        const seen = new Set<string>();
        for (let index = 0; index < page.propositions.length && candidates.length < 32; index++) {
            const proposition = page.propositions[index]?.value;
            if (!proposition || !this.isPurePropositionalSyntax(proposition)) continue;
            if (this.fixedPropositionMayMatch(proposition, node.target)) continue;
            const key = parser.stringifyTight(proposition);
            if (seen.has(key)) continue;
            seen.add(key);
            candidates.push({
                source: { kind: "page", pageId: page.id, index },
                proposition: astmgr.clone(proposition)
            });
        }
        const checked = new Set<string>();
        let attempts = 0;
        const maxAttempts = 2048;
        const tryCombination = (indices: number[]): { sources: SourceRef[]; theorem: AST } | undefined => {
            if (attempts++ >= maxAttempts) return undefined;
            const theorem = this.buildTautoImplication(
                indices.map(index => candidates[index].proposition), node.target
            );
            const key = parser.stringifyTight(theorem);
            if (checked.has(key)) return undefined;
            checked.add(key);
            try {
                new Proof(this.fs).assertTautology(theorem);
                return {
                    sources: indices.map(index => this.cloneSource(candidates[index].source)!),
                    theorem
                };
            } catch {
                return undefined;
            }
        };
        const search = (size: number, start: number, indices: number[]): { sources: SourceRef[]; theorem: AST } | undefined => {
            if (indices.length === size) return tryCombination(indices);
            for (let index = start; index <= candidates.length - (size - indices.length); index++) {
                const found = search(size, index + 1, [...indices, index]);
                if (found) return found;
                if (attempts >= maxAttempts) return undefined;
            }
            return undefined;
        };
        for (let size = 1; size <= Math.min(4, candidates.length); size++) {
            const found = search(size, 0, []);
            if (found) return found;
            if (attempts >= maxAttempts) break;
        }
        return undefined;
    }

    private buildTautoImplication(premises: AST[], target: AST): AST {
        let theorem = astmgr.clone(target);
        for (let index = premises.length - 1; index >= 0; index--) {
            theorem = {
                type: "sym",
                name: ">",
                nodes: [astmgr.clone(premises[index]), theorem]
            };
        }
        return theorem;
    }

    private createAtomicTautoPayload(target: AST, checkedTheorem: AST,
        sources: SourceRef[]): DeferredAssistantPayload {
        const premises = sources.map(source => {
            if (source.kind !== "page") throw new Error(TR("tauto前提必须来自定理表"));
            const proposition = this.fs.inferencePages.page(source.pageId)?.propositions[source.index];
            if (!proposition) throw new Error(TR("证明助手引用了不存在的推理表定理"));
            return {
                pageId: source.pageId,
                index: source.index,
                value: astmgr.clone(proposition.value)
            };
        });
        return {
            kind: "assistant",
            version: 1,
            pageId: this.pageId,
            theorem: astmgr.clone(target),
            history: ["tauto"],
            ...(this.availableRuleNames ? { ruleNames: [...this.availableRuleNames] } : {}),
            ...(this.availableFastMetaRules !== undefined ? { fastMetaRules: this.availableFastMetaRules } : {}),
            allowMcpt: this.allowMcpt,
            allowIfft: this.allowIfft,
            allowIfftEu: this.allowIfftEu,
            tauto: { checkedTheorem: astmgr.clone(checkedTheorem) },
            premises
        };
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

    /**
     * Expand a fully instantiated generated assertion without asking the
     * low-level matcher to decide a capture-prone #rp pattern.  The ordinary
     * matcher must remain strict for user-authored rules; this helper is only
     * used after every generated-rule replacement value has been fixed.
     */
    private expandGeneratedAssertionsCaptureAvoiding(ast: AST): AST {
        if (ast.type === "fn" && ast.name === "#rp") {
            if (!ast.nodes || ast.nodes.length !== 3) {
                // A fourth node selects one occurrence.  Replaying that form
                // by replacing every occurrence would change its meaning, so
                // let the normal matcher handle it instead.
                throw new Error(TR("生成规则包含无法安全展开的定点替换"));
            }
            const source = this.fs.assert.getVarName(ast.nodes[1]);
            if (!source) throw new Error(TR("生成规则替换源不是变量"));
            const replaced = this.substituteBoundValue(ast.nodes[0], source, ast.nodes[2]);
            return this.expandGeneratedAssertionsCaptureAvoiding(replaced);
        }
        if (!ast.nodes?.length) return astmgr.clone(ast);
        return {
            type: ast.type,
            name: ast.name,
            nodes: ast.nodes.map(child => this.expandGeneratedAssertionsCaptureAvoiding(child))
        };
    }

    /**
     * Match a generated rule whose replacement values are already complete.
     * `AssertionSystem.match` intentionally rejects a #rp that could capture
     * a binder.  Generated universal lifting knows the concrete replacement,
     * so evaluate that #rp with the same capture-avoiding substitution used by
     * `have` and then compare the resulting propositions semantically.
     */
    private selectExplicitGeneratedRule(candidateName: string, deduction: Deduction,
        target: AST, expectedConditions: AST[], explicitValues: AST[]
    ): GeneratedRuleSelection | undefined {
        if (deduction.replaceNames.length !== explicitValues.length) return undefined;
        if (!this.astContainsFunction(deduction.conclusion, "#rp")
            && !deduction.conditions.some(condition => this.astContainsFunction(condition, "#rp"))) {
            return undefined;
        }
        const matchTable: ReplvarMatchTable = {};
        deduction.replaceNames.forEach((name, index) => {
            matchTable[name] = astmgr.clone(explicitValues[index]);
        });
        const instantiate = (value: AST): AST => {
            const result = astmgr.clone(value);
            astmgr.replaceByMatchTable(result, matchTable);
            if (this.astContainsPrivateRuleVariable(result)) {
                throw new Error(TR("生成规则仍包含未解析的元变量"));
            }
            return this.expandGeneratedAssertionsCaptureAvoiding(result);
        };
        const conclusion = instantiate(deduction.conclusion);
        this.assertSameProposition(conclusion, target);
        const conditions = deduction.conditions.map(instantiate);
        if (conditions.length !== expectedConditions.length) return undefined;
        for (let index = 0; index < conditions.length; index++) {
            this.assertSameProposition(conditions[index], expectedConditions[index]);
        }
        return {
            name: candidateName,
            deduction,
            replaceValues: explicitValues.map(value => astmgr.clone(value))
        };
    }

    private selectGeneratedRule(baseName: string, target: AST, expectedConditions: AST[],
        prefixes: string[], explicitValues: AST[] = []): GeneratedRuleSelection | undefined {
        const oldFastMetaRules = this.fs.fastmetarules;
        const existingNames = new Set(Object.keys(this.fs.deductions));
        const candidates: GeneratedRuleSelection[] = [];
        // A generated conditional/quantified rule must retain the assertion
        // wrappers carried by the proof graph.  Rigid normalization can erase
        // the binder-renaming dependency in an explicit .Vcn/.Ecn step, making
        // an otherwise valid c-prefix rule appear to have different conditions.
        const preserveSchematicAssertions = [target, ...expectedConditions, ...explicitValues]
            .some(value => this.containsSchematicAssertion(value));
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
                        if (this.astContainsPrivateRuleVariable(result)) {
                            if (this.astContainsFunction(result, "#rp")) this.fs.assert.expand(result, false);
                        } else {
                            astmgr.assign(result, this.normalizeAssertionSyntax(result, !preserveSchematicAssertions));
                        }
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

            // A fully explicit generated `a4`/`v...a4` application can carry
            // a capture-prone #rp in its conclusion.  The strict matcher must
            // reject that shape for user input, but universal qed lifting can
            // safely evaluate it now that every replacement is concrete.
            // Universal lifting prefixes an unconditional `a4` with one or
            // more `v`/`u`/`c` markers (for example `va4` and `vva4`).  The
            // capture-safe fallback applies to that whole generated family,
            // while the suffix check keeps unrelated rules such as `a1` out.
            if (explicitValues.length && /^[vuc<>]*a4$/.test(baseName)) {
                for (const candidateName of this.generatedRuleCandidates(baseName, prefixes)) {
                    if (candidates.some(candidate => candidate.name === candidateName)) continue;
                    let deduction: Deduction | undefined;
                    try {
                        deduction = this.fs.deductions[candidateName] ?? this.fs.generateDeduction(candidateName);
                        if (!deduction) continue;
                        this.assertGeneratedDeductionMetaRules(candidateName, existingNames);
                        const selection = this.selectExplicitGeneratedRule(
                            candidateName, deduction, target, expectedConditions, explicitValues
                        );
                        if (selection) candidates.push(selection);
                    } catch {
                        // A candidate with incompatible binders is expected;
                        // continue searching for the next generated prefix.
                    }
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

    /**
     * Return the source spelling that the materializer must replay.  Local
     * hypotheses can have a simplified presentation proposition while their
     * formal proposition still contains an assertion substitution.
     */
    private getSourceFormalProposition(source: SourceRef, node: DraftNode): AST {
        if (source.kind !== "hypothesis") return this.getSourceProposition(source, node);
        const hypothesis = node.hypotheses.find(item => item.name === source.name)
            ?? this.findPendingHaveForNode(node, source.name);
        if (!hypothesis) throw new Error(TR("未找到证明来源") + source.name);
        if (hypothesis.kind === "have" && !this.isHypothesisAvailable(hypothesis)) {
            throw new Error(TR("该假设尚未完成"));
        }
        if (!hypothesis.proposition) throw new Error(TR("全称变量不能作为命题证明来源：") + source.name);
        return astmgr.clone(hypothesis.formalProposition ?? hypothesis.proposition);
    }

    /** Apply already-validated `have` arguments without presentation normalization. */
    private instantiateFormalHaveApplication(proposition: AST, terms: readonly AST[]): AST {
        let current = astmgr.clone(proposition);
        for (const term of terms) {
            if (current.type === "sym" && current.name === "V" && current.nodes?.length === 2) {
                const binderName = this.fs.assert.getVarName(current.nodes[0]);
                if (!binderName) throw new Error(TR("have来源命题的全称量词变量无效"));
                current = this.substituteBoundValue(current.nodes[1], binderName, term);
                continue;
            }
            if (current.type === "sym" && current.name === ">" && current.nodes?.length === 2) {
                current = astmgr.clone(current.nodes[1]);
                continue;
            }
            throw new Error(TR("have应用参数过多，来源命题不是足够的全称或蕴涵命题"));
        }
        return current;
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

    /**
     * Order explicit values according to the resolved rule's actual
     * replacement names.  User-provided equivalent rules are allowed to use
     * different names or declaration order from the built-in schema.
     */
    private strategyReplaceValues(rule: StrategyRuleResolution,
        canonicalValues: Readonly<Record<string, AST>>): AST[] {
        const deduction = this.fs.deductions[rule.name];
        if (!deduction) throw new Error(TR("推理规则不存在：") + rule.name);
        const actualToCanonical = new Map<string, string>();
        for (const [canonical, actual] of rule.metavariables) {
            actualToCanonical.set(actual, canonical);
        }
        return deduction.replaceNames.map(actualName => {
            const canonicalName = actualToCanonical.get(actualName) ?? actualName;
            const value = canonicalValues[canonicalName];
            if (!value) {
                throw new Error(TR("无法从策略参数推断规则变量：") + canonicalName);
            }
            return astmgr.clone(value);
        });
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
            case ".<>i":
                return { conditions: [], conclusion: parser.parse("$0<>$0") };
            case ".<>r>":
                return {
                    conditions: [parser.parse("$0<>$1"), parser.parse("$2<>$3")],
                    conclusion: parser.parse("($0>$2)<>($1>$3)")
                };
            case ".<>r<>":
                return {
                    conditions: [parser.parse("$0<>$1"), parser.parse("$2<>$3")],
                    conclusion: parser.parse("($0<>$2)<>($1<>$3)")
                };
            case ".<>r&":
                return {
                    conditions: [parser.parse("$0<>$1"), parser.parse("$2<>$3")],
                    conclusion: parser.parse("($0&$2)<>($1&$3)")
                };
            case ".<>r|":
                return {
                    conditions: [parser.parse("$0<>$1"), parser.parse("$2<>$3")],
                    conclusion: parser.parse("($0|$2)<>($1|$3)")
                };
            case ".<>rn":
                return {
                    conditions: [parser.parse("$0<>$1")],
                    conclusion: parser.parse("~$0<>~$1")
                };
            case ".<>rV":
                return {
                    conditions: [parser.parse("(V$x:($0<>$1))")],
                    conclusion: parser.parse("(V$x:$0)<>(V$x:$1)")
                };
            case ".<>rE":
                return {
                    conditions: [parser.parse("(V$x:($0<>$1))")],
                    conclusion: parser.parse("(E$x:$0)<>(E$x:$1)")
                };
            case ".<>rE!":
                return {
                    conditions: [parser.parse("(V$x:($0<>$1))")],
                    conclusion: parser.parse("(E!$x:$0)<>(E!$x:$1)")
                };
            case ".|m":
                return {
                    conditions: [parser.parse("$0>$2"), parser.parse("$1>$2")],
                    conclusion: parser.parse("($0|$1)>$2")
                };
            case ".Erp":
                return {
                    conditions: [],
                    conclusion: parser.parse("#rp($1,$0,$2)>(E$0:$1)")
                };
            case ".Emp":
                return {
                    conditions: [parser.parse("(V$x:($1>$2))"), parser.parse("(E$x:$1)")],
                    conclusion: parser.parse("(E$x:$2)")
                };
            case ".Ee":
                return {
                    conditions: [parser.parse("(E$0:#nf($1,$0))")],
                    conclusion: parser.parse("#nf($1,$0)")
                };
            case ".mn":
                return { conditions: [], conclusion: parser.parse("(~$0>$0)>$0") };
            case ".m2":
                return { conditions: [parser.parse("$0>$1"), parser.parse("~$0>$1")], conclusion: parser.parse("$1") };
            case "a3":
                return { conditions: [], conclusion: parser.parse("(~$1>~$0)>($0>$1)") };
            case "a7":
                return { conditions: [], conclusion: parser.parse("$0=$0") };
            case "a6":
                return {
                    conditions: [],
                    conclusion: parser.parse("#nf($1,$0)>(V$0:#nf($1,$0))")
                };
            case "a8":
                return { conditions: [], conclusion: parser.parse("($0=$1)>($2>#rp($2,$0,$1,$3))") };
            default:
                return undefined;
        }
    }

    /** Render the canonical prerequisite rule a strategy needs. */
    private strategyRuleHint(name: string): string {
        const shape = this.strategyRuleShape(name);
        if (!shape) return name;
        const conditions = shape.conditions.map(condition => parser.stringifyTight(condition)).join(",");
        const conclusion = parser.stringifyTight(shape.conclusion);
        return `${name}：${conditions ? conditions + "⊢" : "⊢"}${conclusion}`;
    }

    private missingStrategyRule(name: string, message: string): never {
        throw new Error(`${TR(message)}；需要先证明或提供等价推理规则：${this.strategyRuleHint(name)}`);
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
        const hypotheses = node.hypotheses
            .filter(hypothesis => !!hypothesis.proposition && this.isHypothesisAvailable(hypothesis))
            .map(hypothesis => ({
                name: hypothesis.name,
                proposition: hypothesis.proposition!
            }));
        // Page propositions are valid proof sources but are not copied into the
        // local hypothesis list. Include them for contradiction search while
        // preserving local-name precedence if a user chose a colliding name.
        const localNames = new Set(hypotheses.map(hypothesis => hypothesis.name));
        this.fs.inferencePages.page(this.pageId)?.propositions.forEach((proposition, index) => {
            const name = `p${index}`;
            if (localNames.has(name)) return;
            hypotheses.push({ name, proposition: proposition.value });
        });
        for (const negative of hypotheses) {
            const proposition = this.negatedProposition(negative.proposition);
            if (!proposition) continue;
            const positive = hypotheses.find(candidate => candidate.name !== negative.name
                && this.fixedPropositionMayMatch(candidate.proposition, proposition));
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
            if (!this.astContainsPrivateRuleVariable(pattern)) {
                const preserveSchematicAssertions = this.explicitArgumentsContainSchematicAssertions(explicit);
                astmgr.assign(pattern, this.normalizeAssertionSyntax(pattern, !preserveSchematicAssertions));
            }
            if (!astmgr.equal(target, pattern)) {
                this.fs.assert.match(astmgr.clone(target), pattern, PRIVATE_RULE_METAVARIABLE_PATTERN, false,
                    matchTable, replacedTypes, null, []);
            }
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

    /**
     * User-supplied assertion terms can still contain theorem-schema `$` names.
     * Rules such as `.Vcn` also carry assertion wrappers in their own
     * declaration. When their explicit arguments are schematic `$` names,
     * preserve those wrappers too; otherwise rigid simplification erases the
     * `#rp/#nf` dependency before qed can lift the step through a binder.
     */
    private explicitArgumentsContainSchematicAssertions(explicit: RuleExplicitArguments,
        deduction?: Deduction): boolean {
        const values = [...explicit.positional, ...explicit.named.values()];
        if (values.some(value => this.containsSchematicAssertion(value))) return true;
        if (!deduction) return false;
        const ruleCarriesAssertion = this.astContainsFunction(deduction.conclusion, "#rp")
            || this.astContainsFunction(deduction.conclusion, "#nf")
            || deduction.conditions.some(condition =>
                this.astContainsFunction(condition, "#rp")
                || this.astContainsFunction(condition, "#nf"));
        // The surrounding target is deliberately ignored here.  A target may
        // contain an assertion wrapper merely because an existential witness
        // is being introduced (for example `.Erp`); preserving that wrapper
        // would leave `use` with a non-quantifier goal.  Only explicit `$`
        // arguments (such as `.Vcn $x=...`) opt into schematic preservation.
        return ruleCarriesAssertion && values.some(value => this.containsSurfacePattern(value));
    }

    private containsSurfacePattern(ast: AST): boolean {
        if (ast.type === "replvar" && ast.name.startsWith("$")
            && !ast.name.startsWith("$$assistant_rule_")) return true;
        return !!ast.nodes?.some(child => this.containsSurfacePattern(child));
    }

    private containsSchematicAssertion(ast: AST): boolean {
        if (ast.type === "fn" && (ast.name === "#rp" || /^#v*nf$/.test(ast.name))
            && this.containsSurfacePattern(ast)) return true;
        return !!ast.nodes?.some(child => this.containsSchematicAssertion(child));
    }

    /** Instantiate a rule for Lean-style `have h := rule args...`. */
    private instantiateRuleForHave(sourceName: string, deduction: Deduction,
        explicit: RuleExplicitArguments, node: DraftNode): RuleHaveInstantiation {
        const preserveSchematicAssertions = this.explicitArgumentsContainSchematicAssertions(explicit, deduction);
        const context = this.createRuleMetavariableContext(deduction, deduction.conclusion, explicit, node);
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
        for (let index = 0; index < explicit.positional.length; index++) {
            const original = deduction.replaceNames[index];
            if (!original) throw new Error(TR("have参数过多"));
            assign(original, explicit.positional[index]);
        }
        for (const [original, value] of explicit.named.entries()) assign(original, value);

        // Conditions are the only source of inference when the rule is not
        // being matched against the current goal.  Reuse the normal candidate
        // search so `have h := mp` can still infer its variables from local
        // hypotheses/pages when there is a unique match.
        this.inferRuleMetavariables(context, matchTable, context.conditions, node);
        const unresolved = context.names.filter(name => !matchTable[context.internalByOriginal.get(name)!]);
        if (unresolved.length) {
            this.assertRuleMatchComplete({ context, matchTable, unresolved }, sourceName);
        }

        const instantiate = (value: AST): AST => {
            const result = this.instantiateRuleAst(value, context, matchTable);
            if (this.astContainsPrivateRuleVariable(result)) {
                throw new Error(TR("have来源规则仍包含未解析的元变量"));
            }
            astmgr.assign(result, this.normalizeAssertionSyntax(result, !preserveSchematicAssertions));
            this.fs.assert.checkGrammer(result, "p");
            return result;
        };
        return {
            conditions: deduction.conditions.map(instantiate),
            conclusion: instantiate(deduction.conclusion),
            replaceValues: deduction.replaceNames.map(name => {
                const value = matchTable[context.internalByOriginal.get(name)!];
                if (!value) throw new Error(TR("无法从have来源规则推断参数") + name);
                return astmgr.clone(value);
            })
        };
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

    /**
     * Recover rule arguments before presentation normalization.  Tactics match
     * a normalized target, whereas materialization must replay the exact
     * assertion bridge the user constructed (for example `.Vcn` after `use`).
     * The normalized and formal targets still share their outer syntax, so map
     * every rule argument occurring in the normalized target to its formal
     * counterpart without changing tactic-side matching semantics.
     */
    private deriveFormalReplaceValues(values: readonly AST[], normalized: AST, formal: AST): AST[] {
        const result = values.map(value => astmgr.clone(value));
        const visit = (normalNode: AST, formalNode: AST): void => {
            for (const [index, value] of values.entries()) {
                if (astmgr.equal(normalNode, value)) result[index] = astmgr.clone(formalNode);
            }
            if (normalNode.type !== formalNode.type || normalNode.name !== formalNode.name
                || normalNode.nodes?.length !== formalNode.nodes?.length) return;
            normalNode.nodes?.forEach((child, index) => visit(child, formalNode.nodes![index]));
        };
        visit(normalized, formal);
        return result;
    }

    /** Replace the private matcher entries for a rule with formal replay values. */
    private withFormalRuleMatchValues(deduction: Deduction, context: RuleMetavariableContext,
        matchTable: ReplvarMatchTable, formalValues: readonly AST[]): ReplvarMatchTable {
        const result: ReplvarMatchTable = {};
        for (const [name, value] of Object.entries(matchTable)) result[name] = astmgr.clone(value);
        deduction.replaceNames.forEach((name, index) => {
            const internal = context.internalByOriginal.get(name);
            const value = formalValues[index];
            if (internal && value) result[internal] = astmgr.clone(value);
        });
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
                        this.fs.assert.match(astmgr.clone(candidate), astmgr.clone(pattern),
                            PRIVATE_RULE_METAVARIABLE_PATTERN, false,
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

    private normalizeAssertionSyntax(ast: AST, rigid = false): AST {
        const normalized = astmgr.clone(ast);
        for (let round = 0; round < 16; round++) {
            const before = astmgr.clone(normalized);
            try { this.fs.assert.expand(normalized, false); } catch { break; }
            if (rigid) this.simplifyRigidAssertions(normalized);
            if (astmgr.equal(before, normalized)) break;
        }
        return normalized;
    }

    /**
     * Remove only top-level #rp wrappers whose source no longer occurs freely
     * in their body.  Unlike normalizeAssertionSyntax(..., true), this never
     * descends into the body, so a meaningful nested binder-conversion remains
     * available when qed materializes the proof tree.
     */
    private stripInertFormalReplacement(ast: AST): AST {
        let result = astmgr.clone(ast);
        for (;;) {
            let params: ReturnType<NonNullable<typeof this.fs.assert.getRpParams>> | false = false;
            try { params = this.fs.assert.getRpParams(result); } catch { break; }
            if (!params) break;
            const [body, source] = params;
            if (source.type !== "replvar" || this.containsRigidFreeName(body, source.name)) break;
            result = astmgr.clone(body);
        }
        return result;
    }

    /**
     * Rule instantiation may add a top-level `#rp` around an implication
     * premise even though the substituted name is already absent.  Remove only
     * that wrapper before storing the materialization graph.  Deliberately do
     * not recurse through binders: an explicit `.Vcn`/`.Ecn` conversion uses
     * nested `#nf/#rp` syntax that is part of the player's proof.
     */
    private stripInertFormalRuleAssertion(ast: AST): AST {
        const result = astmgr.clone(ast);
        if (result.type === "sym" && result.name === ">" && result.nodes?.length === 2) {
            result.nodes[0] = this.stripInertFormalReplacement(result.nodes[0]);
            return result;
        }
        return this.stripInertFormalReplacement(result);
    }

    /** Simplify assertion wrappers once their `$` names are fixed syntax. */
    private simplifyRigidAssertions(ast: AST, bound = new Set<string>()): void {
        const quant = this.fs.assert.getQuantParams(ast);
        if (quant) {
            const binderName = this.fs.assert.getVarName(quant[0]);
            const nextBound = binderName ? new Set([...bound, binderName]) : bound;
            this.simplifyRigidAssertions(quant[1], nextBound);
            return;
        }

        let nf: ReturnType<NonNullable<typeof this.fs.assert.getNfParams>> | false = false;
        try { nf = this.fs.assert.getNfParams(ast); } catch { nf = false; }
        if (nf) {
            const [sub, quants, vars] = nf;
            const nextBound = new Set(bound);
            for (const quantifier of quants) {
                const name = this.fs.assert.getVarName(quantifier);
                if (name) nextBound.add(name);
            }
            this.simplifyRigidAssertions(sub, nextBound);
            if ([...vars].every(name => !this.containsRigidFreeName(sub, name, nextBound))) {
                astmgr.assign(ast, sub);
                this.simplifyRigidAssertions(ast, bound);
            }
            return;
        }

        let rp: ReturnType<NonNullable<typeof this.fs.assert.getRpParams>> | false = false;
        try { rp = this.fs.assert.getRpParams(ast); } catch { rp = false; }
        if (rp) {
            const [sub, source, destination] = rp;
            this.simplifyRigidAssertions(sub, bound);
            if (source.type === "replvar" && !this.containsRigidFreeName(sub, source.name, bound)) {
                astmgr.assign(ast, sub);
                this.simplifyRigidAssertions(ast, bound);
            } else if (astmgr.equal(sub, source)) {
                astmgr.assign(ast, destination);
                this.simplifyRigidAssertions(ast, bound);
            }
            return;
        }

        ast.nodes?.forEach(child => this.simplifyRigidAssertions(child, bound));
    }

    private containsRigidFreeName(ast: AST, name: string, bound = new Set<string>): boolean {
        if (ast.type === "replvar") return ast.name === name && !bound.has(name);
        const quant = this.fs.assert.getQuantParams(ast);
        if (quant) {
            const binderName = this.fs.assert.getVarName(quant[0]);
            const nextBound = binderName ? new Set([...bound, binderName]) : bound;
            return this.containsRigidFreeName(quant[1], name, nextBound);
        }
        let nf: ReturnType<NonNullable<typeof this.fs.assert.getNfParams>> | false = false;
        try { nf = this.fs.assert.getNfParams(ast); } catch { nf = false; }
        if (nf) return this.containsRigidFreeName(nf[0], name, bound);
        let rp: ReturnType<NonNullable<typeof this.fs.assert.getRpParams>> | false = false;
        try { rp = this.fs.assert.getRpParams(ast); } catch { rp = false; }
        if (rp) return this.containsRigidFreeName(rp[0], name, bound);
        return !!ast.nodes?.some(child => this.containsRigidFreeName(child, name, bound));
    }

    private assertSameProposition(a: AST, b: AST): void {
        const left = this.normalizeAssertionSyntax(a);
        const right = this.normalizeAssertionSyntax(b);
        if (astmgr.equal(left, right)) return;
        // A formal child goal may retain an inert top-level #rp wrapper while
        // the tactic-facing node has already normalized it away.  Compare
        // those wrappers after proving that their source is absent from the
        // body; meaningful binder conversions (where the source occurs) stay
        // rigid and continue through the assertion-aware matcher below.
        const strippedLeft = this.stripInertFormalReplacement(left);
        const strippedRight = this.stripInertFormalReplacement(right);
        if (astmgr.equal(strippedLeft, strippedRight)) return;
        // Assertion wrappers such as `#nf` are semantically transparent once
        // both sides are being compared as propositions.  `AssertionSystem.match`
        // is intentionally directional for inference, so use its symmetric
        // equality helper before falling back to matching.
        if (this.fs.assert.equalWithAssertion(left, right, {})
            && this.fs.assert.equalWithAssertion(right, left, {})) return;
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

    private makeNode(target: AST, hypotheses: InferenceProofHypothesis[], formalTarget: AST = target): DraftNode {
        return {
            id: this.nextNodeId++,
            target: astmgr.clone(target),
            formalTarget: astmgr.clone(formalTarget),
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
            formalProposition: h.formalProposition ? astmgr.clone(h.formalProposition) : undefined,
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
        // domain. Keep it as one shared atomic assistant step instead of
        // allocating a fresh __tauto_N deduction for every theorem.
        if (this.allowMcpt && this.isPurePropositionalSyntax(this.theorem)) {
            try {
                new Proof(this.fs).assertTautology(this.theorem);
                const step: DeductionStep = {
                    deductionIdx: DEFERRED_ASSISTANT_STEP,
                    conditionIdxs: [],
                    replaceValues: [],
                    info: "tauto",
                    assistant: this.createAtomicTautoPayload(this.theorem, this.theorem, [])
                };
                propositions.push({ value: astmgr.clone(this.theorem), from: step, deferredKind: "assistant" });
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

        const externalPremiseRows = new Map<string, number>();

        // Named qed compiles a self-contained chain.  Bring page propositions
        // used by exact into its initial condition rows before any derived row.
        if (includeExternalPremises) {
            for (const { pageId, index, proposition } of this.collectExternalPremiseRefs(includeExternalPremises)) {
                const key = `${pageId}:${index}`;
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
                    replaceValues: step.replaceValues.map(item => astmgr.clone(item)),
                    ...(step.info !== undefined ? { info: step.info } : {})
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

        /** Emit an iff between two supported logical contexts. */
        const emitIffContext = (left: AST, right: AST, baseLeft: AST,
            baseRight: AST, sourceAbsoluteIndex: number): EmitResult => {
            if (astmgr.equal(left, baseLeft) && astmgr.equal(right, baseRight)) {
                const sourceValue = propositionAt(sourceAbsoluteIndex).value;
                const sourceShape = sourceValue.type === "sym"
                    && sourceValue.name === "<>" && sourceValue.nodes?.length === 2;
                if (!sourceShape || !astmgr.equal(sourceValue.nodes![0], baseLeft)
                    || !astmgr.equal(sourceValue.nodes![1], baseRight)) {
                    throw new Error(TR("rw等价来源与改写项不匹配"));
                }
                const identity = appendDerived(implication(sourceValue, sourceValue), {
                    deductionIdx: ".i",
                    conditionIdxs: [],
                    replaceValues: [astmgr.clone(sourceValue)]
                });
                return appendDerived(sourceValue, {
                    deductionIdx: "mp",
                    conditionIdxs: [absolute(identity.index), sourceAbsoluteIndex],
                    replaceValues: []
                });
            }
            if (astmgr.equal(left, right)) {
                const identityRule = this.resolveStrategyRule(".<>i");
                if (identityRule) {
                    return appendDerived({
                        type: "sym", name: "<>", nodes: [astmgr.clone(left), astmgr.clone(right)]
                    }, {
                        deductionIdx: identityRule.name,
                        conditionIdxs: [],
                        replaceValues: this.strategyReplaceValues(identityRule, {
                            "$0": left
                        })
                    });
                }
                const direct = this.resolveStrategyRule(".<>");
                const introRule = this.resolveStrategyRule(".i");
                if (!direct) this.missingStrategyRule(".<>", "rw等价改写需要等价构造规则");
                if (!introRule) this.missingStrategyRule(".i", "rw等价改写需要蕴含自反规则");
                const forward = appendDerived(implication(left, right), {
                    deductionIdx: introRule.name,
                    conditionIdxs: [],
                    replaceValues: this.strategyReplaceValues(introRule, { "$0": left })
                });
                const backward = appendDerived(implication(right, left), {
                    deductionIdx: introRule.name,
                    conditionIdxs: [],
                    replaceValues: this.strategyReplaceValues(introRule, { "$0": right })
                });
                return appendDerived({
                    type: "sym", name: "<>", nodes: [astmgr.clone(left), astmgr.clone(right)]
                }, {
                    deductionIdx: direct.name,
                    conditionIdxs: [absolute(forward.index), absolute(backward.index)],
                    replaceValues: []
                });
            }
            if (left.type !== right.type || left.name !== right.name
                || left.nodes?.length !== right.nodes?.length || left.type !== "sym") {
                throw new Error(TR("rw等价改写暂不支持该函数或关系上下文"));
            }
            if (![">", "<>", "&", "|", "~", "V", "E", "E!"].includes(left.name)) {
                throw new Error(TR("rw等价改写暂不支持该函数或关系上下文"));
            }
            if (["V", "E", "E!"].includes(left.name)
                && !astmgr.equal(left.nodes?.[0], right.nodes?.[0])) {
                throw new Error(TR("rw等价改写暂不支持绑定变量名不同的量词上下文"));
            }
            if (left.name === "E!" && !this.allowIfftEu) {
                throw new Error(TR("rw等价改写跨E!需要解锁ifft-EU"));
            }
            const children: EmitResult[] = [];
            if (["V", "E", "E!"].includes(left.name)) {
                const body = emitIffContext(
                    left.nodes![1], right.nodes![1], baseLeft, baseRight,
                    sourceAbsoluteIndex
                );
                const binder = left.nodes![0];
                const quantifiedCondition: AST = {
                    type: "sym", name: "V",
                    nodes: [astmgr.clone(binder), astmgr.clone(body.proposition)]
                };
                const quantifyRule = this.resolveStrategyRule("a6");
                if (!quantifyRule) {
                    throw new Error(TR("rw等价改写量词上下文需要解锁全称概括规则a6"));
                }
                const quantifyImplication = appendDerived(
                    implication(body.proposition, quantifiedCondition), {
                        deductionIdx: quantifyRule.name,
                        conditionIdxs: [],
                        replaceValues: this.strategyReplaceValues(quantifyRule, {
                            "$0": binder,
                            "$1": body.proposition
                        })
                    }
                );
                children.push(appendDerived(quantifiedCondition, {
                    deductionIdx: "mp",
                    conditionIdxs: [absolute(quantifyImplication.index), absolute(body.index)],
                    replaceValues: []
                }));
            } else {
                for (let index = 0; index < (left.nodes?.length ?? 0); index++) {
                    children.push(emitIffContext(
                        left.nodes![index], right.nodes![index], baseLeft, baseRight,
                        sourceAbsoluteIndex
                    ));
                }
            }
            const rule = this.resolveStrategyRule(".<>r" + left.name);
            if (!rule) {
                throw new Error(TR("rw等价改写需要解锁上下文等价规则：.<>r" + left.name));
            }
            return appendDerived({
                type: "sym", name: "<>", nodes: [astmgr.clone(left), astmgr.clone(right)]
            }, {
                deductionIdx: rule.name,
                conditionIdxs: children.map(child => absolute(child.index)),
                replaceValues: []
            });
        };

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
                    // Conditionalization must select a generated rule against
                    // the propositions actually emitted by its dependencies.
                    // In particular, an explicit .Vcn/.Ecn bridge carries a
                    // meaningful #nf/#rp assertion that c.Vcn/c.Ecn must see.
                    // selectGeneratedRule already normalizes ordinary rows,
                    // while retaining schematic assertions when present.
                    const selection = this.selectGeneratedRule(
                        row.from.deductionIdx,
                        desired,
                        conditions.map(condition => condition.proposition),
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
                // Once this binder is fixed, normalize the newly quantified
                // proposition before matching generated `v*` rules.  This
                // removes capture-safe #rp wrappers introduced by a4 and
                // keeps equivalent conditions in the same surface shape.
                // Preserve a user-visible #nf/#rp bridge such as `.Vcn` while
                // lifting it through a binder.  Ordinary a4-generated wrappers
                // remain implementation detail and need rigid normalization for
                // the usual v/c rule search to succeed.
                const quantifiedValue = quantify(row.value);
                const desired = this.normalizeAssertionSyntax(
                    quantifiedValue, !this.containsSchematicAssertion(quantifiedValue)
                );

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
                        replaceValues: selection.replaceValues,
                        info: "rigid"
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
            const formalHaveProposition = node.formalHaveProposition ?? node.haveProposition;
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
                this.assertSameProposition(result.proposition, formalHaveProposition);
                return { index: result.index, proposition: astmgr.clone(formalHaveProposition) };
            }

            const argumentSources = node.haveArgumentSources ?? [];
            for (let index = 0; index < args.length; index++) {
                const argument = args[index];
                if (currentProposition.type === "sym" && currentProposition.name === "V"
                    && currentProposition.nodes?.length === 2) {
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
                    continue;
                }
                if (currentProposition.type === "sym" && currentProposition.name === ">"
                    && currentProposition.nodes?.length === 2) {
                    const source = argumentSources[index];
                    if (!source || source.kind === "rule") {
                        throw new Error(TR("have蕴涵参数缺少假设或定理来源"));
                    }
                    const argumentRow = sourceAbsoluteRow(source, hypothesisRows);
                    this.assertSameProposition(
                        propositionAt(argumentRow).value,
                        currentProposition.nodes[0]
                    );
                    const result = appendDerived(astmgr.clone(currentProposition.nodes[1]), {
                        deductionIdx: "mp",
                        conditionIdxs: [currentRow, argumentRow],
                        replaceValues: []
                    });
                    currentRow = absolute(result.index);
                    currentProposition = astmgr.clone(currentProposition.nodes[1]);
                    continue;
                }
                throw new Error(TR("have应用参数过多，来源命题不是足够的全称或蕴涵命题"));
            }
            this.assertSameProposition(currentProposition, formalHaveProposition);
            return { index: currentRow - basePropositionCount, proposition: astmgr.clone(formalHaveProposition) };
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
                    propositions.push({
                        value: astmgr.clone(hypothesis.formalProposition ?? hypothesis.proposition),
                        from: null
                    });
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
                        result = dischargeHypothesis(
                            result, intro.binding.formalProposition ?? intro.binding.proposition, intro.index
                        );
                    } else if (intro.binding.kind === "variable") {
                        result = quantifyResult(result, intro.binding);
                    }
                }
                return result;
            };
            if (node.kind === "obtainExists") {
                if (node.children.length !== 1 || !node.obtainSource
                    || !node.obtainVariableName || !node.obtainHypothesisName
                    || !node.obtainBinder || !node.obtainBody) {
                    throw new Error(TR("obtain存在量词证明节点结构无效"));
                }
                if (node.obtainSource.kind === "rule") {
                    throw new Error(TR("obtain证明来源不能是推理规则"));
                }
                const sourceIndex = sourceAbsoluteRow(node.obtainSource, hypothesisRows);
                const sourceValue = propositionAt(sourceIndex).value;
                if (sourceValue.type !== "sym" || sourceValue.name !== "E"
                    || sourceValue.nodes?.length !== 2) {
                    throw new Error(TR("obtain存在量词来源已改变"));
                }
                const formalBinder = node.formalObtainBinder ?? node.obtainBinder;
                const formalBody = node.formalObtainBody ?? node.obtainBody;
                const formalTarget = node.formalTarget;
                const binderName = this.fs.assert.getVarName(formalBinder);
                const sourceBinderName = this.fs.assert.getVarName(sourceValue.nodes[0]);
                if (!binderName || !sourceBinderName
                    || !astmgr.equal(formalBody, sourceValue.nodes[1])
                    || binderName !== sourceBinderName) {
                    throw new Error(TR("obtain存在量词来源与证明节点不匹配"));
                }
                if (this.containsFreeName(formalTarget, node.obtainVariableName)) {
                    throw new Error(TR("obtain生成的见证变量不能出现在最终目标中"));
                }

                // The child proof introduces x and hx.  Its own finish pass
                // turns those local assumptions back into Vx:(P x > target).
                const continuation = emit(node.children[0], hypothesisRows);
                const expectedUniversal = {
                    type: "sym",
                    name: "V",
                    nodes: [astmgr.clone(formalBinder), {
                        type: "sym",
                        name: ">",
                        nodes: [astmgr.clone(formalBody), astmgr.clone(formalTarget)]
                    }]
                } as AST;
                this.assertSameProposition(continuation.proposition, expectedUniversal);

                const existentialTarget = {
                    type: "sym",
                    name: "E",
                    nodes: [astmgr.clone(formalBinder), astmgr.clone(formalTarget)]
                } as AST;
                const empResult = appendDerived(existentialTarget, {
                    deductionIdx: node.obtainEmpRule ?? ".Emp",
                    conditionIdxs: [absolute(continuation.index), sourceIndex],
                    replaceValues: []
                });
                const result = appendDerived(formalTarget, {
                    deductionIdx: node.obtainEeRule ?? ".Ee",
                    conditionIdxs: [absolute(empResult.index)],
                    replaceValues: []
                });
                return finish({ index: result.index, proposition: astmgr.clone(formalTarget) });
            }
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
                this.assertSameProposition(implication.nodes[1], node.formalTarget);
                const result = appendDerived(node.formalTarget, {
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
            if (node.kind === "applyAt") {
                if (node.children.length < 1 || !node.applyAtHypothesis
                    || !node.ruleName || !node.appliedProposition) {
                    throw new Error(TR("apply at证明节点结构无效"));
                }
                const continuation = node.children.at(-1)!;
                const premiseResults = node.children.slice(0, -1)
                    .map(child => emit(child, hypothesisRows));
                const hypothesisIndex = hypothesisRows.get(node.applyAtHypothesis);
                if (hypothesisIndex === undefined) {
                    throw new Error(TR("apply at找不到要转换的假设：") + node.applyAtHypothesis);
                }
                const step: DeductionStep = {
                    deductionIdx: node.ruleName,
                    conditionIdxs: [
                        absolute(hypothesisIndex),
                        ...premiseResults.map(result => absolute(result.index))
                    ],
                    replaceValues: (node.formalReplaceValues ?? node.replaceValues ?? [])
                        .map(value => astmgr.clone(value))
                };
                const transformed = appendDerived(node.formalAppliedProposition ?? node.appliedProposition, step);
                const continuationRows = new Map(hypothesisRows);
                continuationRows.set(node.applyAtHypothesis, transformed.index);
                return finish(emit(continuation, continuationRows));
            }
            if (node.kind === "rwIff") {
                if (node.children.length !== 1 || node.source?.kind === "rule"
                    || !node.rwBefore || !node.rwAfter || !node.rwSourceTerm
                    || !node.rwDestinationTerm || node.rwReverse === undefined) {
                    throw new Error(TR("rw等价改写证明节点结构无效"));
                }
                const child = emit(node.children[0], hypothesisRows);
                const sourceAbsoluteIndex = sourceAbsoluteRow(node.source, hypothesisRows);
                const fullContextLeft = node.rwReverse ? node.rwAfter : node.rwBefore;
                const fullContextRight = node.rwReverse ? node.rwBefore : node.rwAfter;
                const context = emitIffContext(
                    node.rwReverse ? node.rwAfter : node.rwBefore,
                    node.rwReverse ? node.rwBefore : node.rwAfter,
                    node.rwReverse ? node.rwDestinationTerm : node.rwSourceTerm,
                    node.rwReverse ? node.rwSourceTerm : node.rwDestinationTerm,
                    sourceAbsoluteIndex
                );
                const direction = node.rwReverse ? ".<>1" : ".<>2";
                const directionRule = this.resolveStrategyRule(direction);
                if (!directionRule) {
                    this.missingStrategyRule(direction,
                        "rw等价改写需要解锁互推方向规则或提供等价推理规则");
                }
                const directionImplication = appendDerived(implication(
                    context.proposition, implication(node.rwAfter, node.rwBefore)
                ), {
                    deductionIdx: directionRule.name,
                    conditionIdxs: [],
                    replaceValues: this.strategyReplaceValues(directionRule, {
                        "$0": fullContextLeft,
                        "$1": fullContextRight
                    })
                });
                const directed = appendDerived(implication(node.rwAfter, node.rwBefore), {
                    deductionIdx: "mp",
                    conditionIdxs: [absolute(directionImplication.index), absolute(context.index)],
                    replaceValues: []
                });
                const result = appendDerived(node.rwBefore, {
                    deductionIdx: "mp",
                    conditionIdxs: [absolute(directed.index), absolute(child.index)],
                    replaceValues: []
                });
                this.assertSameProposition(result.proposition, node.rwBefore);
                return finish(result);
            }
            if (node.kind === "apply") {
                const children = node.children.map(child => emit(child, hypothesisRows));
                if (node.source && node.source.kind !== "rule") {
                    if (!node.appliedProposition) throw new Error(TR("apply证明节点缺少蕴含来源"));
                    let implication = astmgr.clone(node.formalAppliedProposition ?? node.appliedProposition);
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
                    this.assertSameProposition(implication, node.formalTarget);
                    return finish({ index: implicationRow - basePropositionCount, proposition: astmgr.clone(implication) });
                }
                if (!node.ruleName) throw new Error(TR("apply证明节点缺少推理规则"));
                const ruleConditionCount = node.ruleConditionCount ?? children.length;
                if (ruleConditionCount > children.length) throw new Error(TR("apply证明节点的规则条件数量无效"));
                const ruleStep: DeductionStep = {
                    deductionIdx: node.ruleName,
                    conditionIdxs: children.slice(0, ruleConditionCount).map(child => absolute(child.index)),
                    replaceValues: (node.formalReplaceValues ?? node.replaceValues ?? [])
                        .map(value => astmgr.clone(value))
                };
                let implication = astmgr.clone(node.formalAppliedProposition ?? node.appliedProposition ?? node.formalTarget);
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
                this.assertSameProposition(implication, node.formalTarget);
                return finish({ index: resultIndex, proposition: astmgr.clone(implication) });
            }
            if (node.kind === "tauto") {
                const sources = node.tautoSources ?? [];
                const checkedTheorem = node.tautoTheorem ?? node.target;
                const formalTarget = node.formalTarget;
                const sourceIndices = sources.map(source => {
                    if (source.kind === "rule") throw new Error(TR("tauto前提不能来自推理规则"));
                    return sourceAbsoluteRow(source, hypothesisRows);
                });
                const step: DeductionStep = {
                    deductionIdx: DEFERRED_ASSISTANT_STEP,
                    conditionIdxs: sourceIndices,
                    replaceValues: [],
                    info: "tauto",
                    assistant: this.createAtomicTautoPayload(formalTarget, checkedTheorem, sources)
                };
                const index = propositions.length;
                propositions.push({ value: astmgr.clone(formalTarget), from: step, deferredKind: "assistant" });
                steps.push(step);
                return finish({ index, proposition: astmgr.clone(formalTarget) });
            }
            if (node.kind === "exact" && node.source) {
                if (node.source.kind === "rule") {
                    const step: DeductionStep = {
                        deductionIdx: node.source.name,
                        conditionIdxs: [],
                        replaceValues: (node.formalReplaceValues ?? node.source.replaceValues)
                            .map(value => astmgr.clone(value))
                    };
                    const index = propositions.length;
                    const proposition = astmgr.clone(node.formalAppliedProposition ?? node.formalTarget);
                    propositions.push({ value: proposition, from: step });
                    steps.push(step);
                    return finish({ index, proposition });
                }
                const sourceAbsoluteIndex = sourceAbsoluteRow(node.source, hypothesisRows);
                if (sourceAbsoluteIndex >= basePropositionCount) {
                    return finish({
                        index: sourceAbsoluteIndex - basePropositionCount,
                        proposition: astmgr.clone(propositionAt(sourceAbsoluteIndex).value)
                    });
                }
                const proposition = astmgr.clone(propositionAt(sourceAbsoluteIndex).value);
                const idStep: DeductionStep = { deductionIdx: ".i", conditionIdxs: [], replaceValues: [proposition] };
                const idIndex = propositions.length;
                propositions.push({ value: { type: "sym", name: ">", nodes: [astmgr.clone(proposition), astmgr.clone(proposition)] }, from: idStep });
                const mpStep: DeductionStep = { deductionIdx: "mp", conditionIdxs: [absolute(idIndex), sourceAbsoluteIndex], replaceValues: [] };
                const index = propositions.length;
                propositions.push({ value: proposition, from: mpStep });
                steps.push(idStep, mpStep);
                return finish({ index, proposition });
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
                    ...(proposition.from.info !== undefined ? { info: proposition.from.info } : {}),
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
function materializeAtomicTauto(fs: FormalSystem, deduction: Deduction,
    payload: DeferredAssistantPayload): void {
    const metadata = payload.tauto;
    if (!metadata) throw new Error(TR("tauto原子步骤缺少MCPT附加信息"));
    const previousPropositions = fs.propositions;
    const previousFastMetaRules = fs.fastmetarules;
    try {
        fs.fastmetarules = "cvuqe><:#zZQR";
        fs.propositions = payload.premises.map(premise => ({
            value: astmgr.clone(premise.value),
            from: null
        }));
        new Proof(fs).assertTautology(astmgr.clone(metadata.checkedTheorem));
        new Proof(fs).prove(astmgr.clone(metadata.checkedTheorem));
        let resultIndex = fs.propositions.length - 1;
        for (let index = 0; index < payload.premises.length; index++) {
            resultIndex = fs.deduct({
                deductionIdx: "mp",
                conditionIdxs: [resultIndex, index],
                replaceValues: []
            });
        }
        const result = fs.propositions[resultIndex]?.value;
        if (!result || !astmgr.equal(result, deduction.conclusion)) {
            throw new Error(TR("tauto原子步骤展开后的结论不匹配"));
        }
        const compiled = fs.compileMacroFromPropositions();
        deduction.steps = compiled.steps;
        deduction.tempvars = fs.findLocalNamesInDeductionStep(compiled.steps);
    } finally {
        fs.propositions = previousPropositions;
        fs.fastmetarules = previousFastMetaRules;
    }
}

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
    if (payload.tauto) {
        materializeAtomicTauto(fs, deduction, payload);
        return;
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
    // `pN` is also a valid user-chosen local hypothesis name (for example
    // `intro p0`).  Do not mistake that name for a theorem-list reference
    // while remapping the replay recipe's snapshotted page premises.
    const localNames = new Set<string>();
    for (const command of payload.history) {
        const match = /^(?:intro|intros)\s+(.+)$/.exec(command.trim());
        if (match) {
            match[1].split(/[\s,]+/).filter(Boolean).forEach(name => localNames.add(name));
        }
        const have = /^have\s+([^\s,:=]+)/.exec(command.trim());
        if (have) localNames.add(have[1]);
        const obtain = /^obtain\s+(?:<|⟨)?([^,\s<>⟩|]+)(?:\s*,\s*|\s*\|\s*)([^\s<>⟩|]+)\s*(?:>|⟩)?\s*:=/.exec(command.trim());
        if (obtain) {
            localNames.add(obtain[1]);
            localNames.add(obtain[2]);
        }
    }
    const remapPageReferences = (command: string): string => {
        return command.replace(/\bp([0-9]+)\b/g, (whole, rawIndex: string) => {
            const originalIndex = Number(rawIndex);
            if (localNames.has(whole)) return whole;
            const replayIndex = indexMap.get(originalIndex);
            if (replayIndex === undefined) {
                throw new Error(TR("证明助手延迟步骤缺少所引用的前提定理 p") + originalIndex);
            }
            return `p${replayIndex}`;
        });
    };
    let replayHistory: string[];
    try {
        replayHistory = payload.history.map(command => {
            const trimmed = command.trim();
            // Only commands that can name theorem-list rows are remapped. This
            // keeps arbitrary proposition text untouched while also handling
            // every `pN` argument in `have h := pN pM ...`.
            if (!/^(?:apply|exact|have|obtain|rw|rwb|nth_rw)\b/.test(trimmed)) return command;
            return remapPageReferences(command);
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
            allowMcpt: payload.allowMcpt !== false,
            allowIfft: payload.allowIfft !== false,
            allowIfftEu: payload.allowIfftEu !== false
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
