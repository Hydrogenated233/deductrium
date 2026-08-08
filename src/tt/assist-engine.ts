import { TR } from "../lang.js";
import { Assist } from "./assist.js";
import { AST, ASTParser } from "./astparser.js";
import { Context, Core } from "./core.js";
import { TTCoreConfig, TTCoreEngine } from "./engine.js";

const parser = new ASTParser();

export type TTAssistOptions = {
    disableMultipleApply: boolean;
    disableDestructConds: boolean;
    disableDestructEq: boolean;
};

export type TTAssistGoalSnapshot = {
    context: Context;
    type: AST;
    holeName: string;
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

    constructor(engine = new TTCoreEngine()) {
        this.engine = engine;
    }

    configure(config: TTCoreConfig) {
        this.engine.configure(config);
        this.clear();
    }

    start(target: AST | string, options: TTAssistOptions, history: string[] = []) {
        const source = typeof target === "string" ? target : parser.stringify(target);
        this.options = { ...options };
        this.targetSource = source;
        this.createAssist();
        for (const command of history) this.executeCommand(command, true);
        return this.snapshot();
    }

    apply(command: string) {
        this.requireAssist();
        const history = this.history.slice();
        try {
            this.executeCommand(command, true);
            return this.snapshot();
        } catch (error) {
            this.createAssist();
            for (const previous of history) this.executeCommand(previous, true);
            throw error;
        }
    }

    undo() {
        this.requireAssist();
        this.history.pop();
        const history = this.history.slice();
        this.createAssist();
        for (const command of history) this.executeCommand(command, true);
        return this.snapshot();
    }

    qed(): TTAssistQedResult {
        const assist = this.requireAssist();
        assist.qed();
        return {
            proof: parser.stringify(assist.elem),
            theorem: parser.stringify(assist.theorem)
        };
    }

    clear() {
        this.assist = null;
        this.targetSource = "";
        this.history = [];
    }

    private createAssist() {
        if (!this.targetSource) throw new Error(TR("空表达式"));
        Assist.disableMultipleApply = this.options?.disableMultipleApply ?? true;
        Assist.disableDestructConds = this.options?.disableDestructConds ?? true;
        Assist.disableDestructEq = this.options?.disableDestructEq ?? true;

        const target = parser.parse(this.targetSource);
        if (!target) throw new Error(TR("空表达式"));
        if (target.type === "===" || target.type === ":=" || target.type === ":") {
            throw new Error(TR(target.type === ":" ? "已断言该类型有值" : "不是命题类型"));
        }
        const type = this.engine.core.checkType(target, [], false);
        if (type.type !== "apply" || type.nodes[0].name !== "U") throw new Error(TR("不是命题类型"));
        this.assist = new Assist(this.engine.core, this.targetSource);
        this.history = [];
    }

    private executeCommand(command: string, record: boolean) {
        const assist = this.requireAssist();
        const value = command.trim();
        const commandEnd = value.indexOf(" ");
        const name = commandEnd === -1 ? value : value.slice(0, commandEnd);
        const parameter = commandEnd === -1 ? null : value.slice(commandEnd);
        if (!name || name === "qed") throw new Error(TR("未知的证明策略"));
        const tactic = assist[name];
        if (typeof tactic !== "function" || name === "constructor" || name === "autofillTactics" || name === "markTargets") {
            throw new Error(TR("未知的证明策略"));
        }
        tactic.call(assist, parameter);
        if (record) this.history.push(value);
    }

    private snapshot(): TTAssistSnapshot {
        const assist = this.requireAssist();
        const tactics = assist.autofillTactics();
        assist.markTargets();

        const theorem = Core.clone(assist.theorem, true);
        // Intermediate proof terms intentionally contain dependent holes such as
        // (%0).  Checking the outer term before those holes are solved treats the
        // placeholders as user constants and emits misleading unknown-variable
        // / bound-variable diagnostics.  The completed term is checked by qed().
        if (!assist.goal.length) {
            try { this.engine.core.checkType(theorem, [], false); } catch { }
        }

        const goals = assist.goal.map(goal => {
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
                try { this.engine.core.checkType(type, goal.context, false); } catch { }
            }
            return {
                context: goal.context.map(([name, value, id]) => [name, Core.clone(value, true), id]),
                type,
                holeName: goal.ast.name
            } as TTAssistGoalSnapshot;
        });

        return {
            theorem,
            elem: Core.clone(assist.elem, true),
            goals,
            tactics,
            history: this.history.slice()
        };
    }

    private requireAssist() {
        if (!this.assist) throw new Error(TR("请在定理列表中点选待证命题"));
        return this.assist;
    }
}
