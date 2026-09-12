import { TR } from "../lang.js";
import { Assist, type Goal } from "./assist.js";
import { AST, ASTParser } from "./astparser.js";
import { Context, Core } from "./core.js";
import { TTCoreConfig, TTCoreEngine } from "./engine.js";
import { compactImplicitAliasesForDisplay, markExplicitAtSyntax } from "./presentation.js";
import { parseTTTacticScript, TTTacticNode, TTTacticScriptError } from "./tactic-script.js";

const parser = new ASTParser();
const commandMethods = new Set([
    "intro", "intros", "rintro", "change", "show", "cases", "rcases",
    "construct", "assumption", "simp", "simpa", "eq", "exact", "apply",
    "specialize", "rw", "rwb", "trunc", "rfl", "simpl", "fnext", "sup",
    "obtain", "have", "hyp", "induction", "destruct", "use", "ex", "left",
    "right", "case", "expand", "clear", "revert", "refine"
]);
export const TT_ASSIST_COMMANDS = [...commandMethods]
    .map(name => name === "construct" ? "constructor" : name).concat("qed");

/** Lean spellings inherit the same survival unlock as their existing tactic. */
export function isTTAssistTacticUnlocked(name: string, unlocked?: ReadonlySet<string>): boolean {
    if (name === "obtain") {
        return !unlocked || unlocked.has(name)
            || unlocked.has("hyp") && unlocked.has("destruct");
    }
    const aliases: Record<string, string> = {
        have: "hyp", use: "ex", rcases: "destruct", cases: "destruct", induction: "destruct",
        intros: "intro", clear: "intro", revert: "intro", refine: "apply"
    };
    return !unlocked || unlocked.has(name) || !!aliases[name] && unlocked.has(aliases[name]);
}

function isProofTargetSort(type: AST) {
    return (
        type?.type === "apply"
        && type.nodes?.[0]?.type === "var"
        && type.nodes[0].name === "U"
    ) || (
        type?.type === "var"
        && type.name === "U@:"
        && !type.bondVarId
    );
}

export type TTAssistOptions = {
    disableMultipleApply: boolean;
    disableDestructConds: boolean;
    disableDestructEq: boolean;
};

export type TTAssistGoalSnapshot = {
    context: Context;
    type: AST;
    holeName: string;
    /** Stable for this proof session, independent of the current goal queue position. */
    id?: string;
};

export type TTAssistSnapshot = {
    theorem: AST;
    elem: AST;
    goals: TTAssistGoalSnapshot[];
    tactics: string[];
    history: string[];
};

export type TTAssistQedResult = {
    proof: string;
    theorem: string;
};

/** DOM-free proof-assistant session shared by the Worker and fallback path. */
export class TTAssistEngine {
    readonly engine: TTCoreEngine;
    private assist: Assist = null;
    private targetSource = "";
    private history: string[] = [];
    private options: TTAssistOptions = null;
    private goalIds = new WeakMap<Goal, string>();
    private nextGoalId = 0;

    constructor(engine = new TTCoreEngine()) {
        this.engine = engine;
    }

    configure(config: TTCoreConfig) {
        this.engine.configure(config);
        this.clear();
    }

    start(target: AST | string, options: TTAssistOptions, history: string[] = []) {
        if (typeof target !== "string") markExplicitAtSyntax(target);
        const source = typeof target === "string" ? target : parser.stringify(target);
        this.options = { ...options };
        this.targetSource = source;
        this.replayHistory(history);
        return this.snapshot();
    }

    apply(command: string) {
        this.requireAssist();
        const history = this.history.slice();
        try {
            this.executeCommand(command, true);
            return this.snapshot();
        } catch (error) {
            this.replayHistory(history);
            throw error;
        }
    }

    undo() {
        this.requireAssist();
        this.history.pop();
        const history = this.history.slice();
        this.replayHistory(history);
        return this.snapshot();
    }

    qed(): TTAssistQedResult {
        const assist = this.requireAssist();
        const proof = assist.qed();
        const explicitAtNames = new Set<string>();
        return {
            proof: parser.stringify(this.presentAst(proof, explicitAtNames)),
            theorem: parser.stringify(this.presentAst(assist.theorem, explicitAtNames))
        };
    }

    clear() {
        this.assist = null;
        this.targetSource = "";
        this.history = [];
        this.goalIds = new WeakMap();
        this.nextGoalId = 0;
    }

    private createAssist() {
        if (!this.targetSource) throw new Error(TR("空表达式"));
        // A replay is a new proof-session instance. Reset the deterministic
        // counter so undo/history restoration keeps the same IDs. The GUI's
        // contextKey separates identical IDs belonging to different proofs.
        this.goalIds = new WeakMap();
        this.nextGoalId = 0;
        Assist.disableMultipleApply = this.options?.disableMultipleApply ?? true;
        Assist.disableDestructConds = this.options?.disableDestructConds ?? true;
        Assist.disableDestructEq = this.options?.disableDestructEq ?? true;

        // The GUI validates newly edited theorem text with parseSurface before
        // it creates a session.  This engine is also a DOM-free compatibility
        // API used by saved-history replay and regression fixtures, whose
        // target strings may still use the pre-Unicode spelling.  Keep that
        // internal boundary on the compatibility parser; strict validation
        // belongs at the user-input/save-load boundary, not in replay.
        const target = markExplicitAtSyntax(parser.parseSurfaceOrLegacy(this.targetSource));
        if (!target) throw new Error(TR("空表达式"));
        if (target.type === "===" || target.type === ":=" || target.type === ":") {
            throw new Error(TR(target.type === ":" ? "已断言该类型有值" : "不是命题类型"));
        }
        const type = this.engine.core.checkType(target, [], false);
        // Universe-polymorphic propositions (for example `Pi u:U@, ...`)
        // live in the Core's external sort `U@:` rather than an ordinary
        // `U level` application.  `U@` itself remains the type of level terms,
        // so values such as `@0` are still rejected as proof targets.
        if (!isProofTargetSort(type)) throw new Error(TR("不是命题类型"));
        this.assist = new Assist(this.engine.core, target);
        this.registerGoals();
        this.history = [];
    }

    /** Rebuild a session from commands without consulting UI recommendations. */
    private replayHistory(history: readonly string[]) {
        this.createAssist();
        for (const command of history) {
            this.executeCommand(command, true);
        }
    }

    private executeCommand(command: string, record: boolean) {
        const nodes = parseTTTacticScript(command);
        if (!nodes.length) throw new Error(TR("未知的证明策略"));
        this.executeNodes(nodes);
        if (record) this.history.push(command.trim());
    }

    private executeNodes(nodes: readonly TTTacticNode[]) {
        for (const node of nodes) {
            try {
                if (node.kind === "tactic") {
                    this.executeTactic(node.command);
                } else if (node.kind === "sequence") {
                    this.executeNodes(node.body);
                } else {
                    if (node.kind === "have") this.executeTactic(node.command);
                    this.executeFocused(node.body);
                }
            } catch (error) {
                if (error instanceof TTTacticScriptError) throw error;
                throw new TTTacticScriptError(node.lineNumber,
                    error instanceof Error ? error.message : String(error));
            }
        }
    }

    private executeFocused(body: readonly TTTacticNode[]) {
        const assist = this.requireAssist();
        if (!assist.goal.length) throw new Error(TR("无证明目标，请使用qed命令结束证明"));
        // Keep live goal references: solving a witness may update a hidden
        // sibling through GoalDependRel even while that sibling is unfocused.
        const siblings = assist.goal.slice(1);
        assist.goal = [assist.goal[0]];
        try {
            this.executeNodes(body);
            if (assist.goal.length) throw new Error(TR("子证明尚未完成"));
        } finally {
            assist.goal.push(...siblings);
        }
    }

    private executeTactic(command: string) {
        const assist = this.requireAssist();
        const value = command.trim();
        const commandEnd = value.search(/\s/);
        const name = commandEnd === -1 ? value : value.slice(0, commandEnd);
        const parameter = commandEnd === -1 ? null : value.slice(commandEnd);
        if (!name || name === "qed") throw new Error(TR("未知的证明策略"));
        // `constructor` is a JavaScript class keyword, so the assistant
        // exposes its Lean-style structural implementation as `construct`.
        const tacticName = name === "constructor" ? "construct" : name;
        if (!commandMethods.has(tacticName)) {
            throw new Error(TR("未知的证明策略"));
        }
        const tactic = assist[tacticName];
        tactic.call(assist, parameter);
        this.registerGoals();
    }

    private registerGoals() {
        if (!this.assist) return;
        for (const goal of this.assist.goal) {
            if (!this.goalIds.has(goal)) {
                this.goalIds.set(goal, `goal-${this.nextGoalId++}`);
            }
        }
    }

    private snapshot(): TTAssistSnapshot {
        const assist = this.requireAssist();
        const tactics = assist.autofillTactics();
        assist.markTargets();
        const explicitAtNames = new Set<string>();

        const theorem = this.presentAst(assist.theorem, explicitAtNames);
        // Intermediate proof terms intentionally contain dependent holes such as
        // (%0).  Checking the outer term before those holes are solved treats the
        // placeholders as user constants and emits misleading unknown-variable
        // / bound-variable diagnostics.  The completed term is checked by qed().
        if (!assist.goal.length) {
            try {
                this.engine.core.checkType(
                    theorem,
                    [],
                    false,
                    undefined,
                    false,
                    true
                );
            } catch { }
        }

        const goals = assist.goal.map(goal => {
            const localNames = new Set(goal.context.map(([name]) => name));
            // Keep a surface-shaped copy for the UI. The validation copy may
            // be desugared by Core.checkType (for example `=` to `eq` and `*`
            // to `compeq`), but that internal normalization must not leak into
            // the proof assistant display after a rewrite.
            const surfaceType = Core.clone(goal.type, true);
            const type = Core.clone(goal.type, true);
            // A dependent constructor goal may refer to a proof hole from an
            // earlier goal (for example (%0) after `ex`).  That placeholder is
            // intentionally outside the local context until the earlier goal
            // is solved, so checking it now only produces a false unknown
            // variable / bound-variable diagnostic.
            const freeVars = Core.getFreeVars(type);
            const hasUnresolvedHole = Array.from(freeVars).some(name =>
                name.startsWith("(%") || name.startsWith("(?#")
            );
            if (!hasUnresolvedHole) {
                try {
                    this.engine.core.checkType(
                        type,
                        goal.context,
                        false,
                        undefined,
                        false,
                        true
                    );
                } catch { }
            }
            return {
                context: goal.context.map(([name, value, id]) => [
                    name,
                    this.presentAst(value, explicitAtNames, localNames),
                    id
                ]),
                type: this.presentAst(surfaceType, explicitAtNames, localNames),
                holeName: goal.ast.name,
                id: this.goalIds.get(goal)
            } as TTAssistGoalSnapshot;
        });

        return {
            theorem,
            elem: this.presentAst(assist.elem, explicitAtNames),
            goals,
            tactics,
            history: this.history.slice()
        };
    }

    private presentAst(ast: AST, explicitAtNames: ReadonlySet<string>,
        inScopeNames: ReadonlySet<string> = new Set()) {
        return compactImplicitAliasesForDisplay(
            Core.clone(ast, true),
            this.engine.core.opaque,
            explicitAtNames,
            inScopeNames
        );
    }

    private requireAssist() {
        if (!this.assist) throw new Error(TR("请在定理列表中点选待证命题"));
        return this.assist;
    }
}
