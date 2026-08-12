import { TR } from "../lang.js";
import { Assist } from "./assist.js";
import { ASTParser } from "./astparser.js";
import { Core } from "./core.js";
import { TTCoreEngine } from "./engine.js";
import { compactImplicitAliasesForDisplay, markExplicitAtSyntax, restoreSemanticMetaNamesForDisplay } from "./presentation.js";
const parser = new ASTParser();
function isProofTargetSort(type) {
    return (type?.type === "apply"
        && type.nodes?.[0]?.type === "var"
        && type.nodes[0].name === "U") || (type?.type === "var"
        && type.name === "U@:"
        && !type.bondVarId);
}
/** DOM-free proof-assistant session shared by the Worker and fallback path. */
export class TTAssistEngine {
    engine;
    assist = null;
    targetSource = "";
    history = [];
    options = null;
    constructor(engine = new TTCoreEngine()) {
        this.engine = engine;
    }
    configure(config) {
        this.engine.configure(config);
        this.clear();
    }
    start(target, options, history = []) {
        if (typeof target !== "string")
            markExplicitAtSyntax(target);
        const source = typeof target === "string" ? target : parser.stringify(target);
        this.options = { ...options };
        this.targetSource = source;
        this.createAssist();
        for (const command of history)
            this.executeCommand(command, true);
        return this.snapshot();
    }
    apply(command) {
        this.requireAssist();
        const history = this.history.slice();
        try {
            this.executeCommand(command, true);
            return this.snapshot();
        }
        catch (error) {
            this.createAssist();
            for (const previous of history)
                this.executeCommand(previous, true);
            throw error;
        }
    }
    undo() {
        this.requireAssist();
        this.history.pop();
        const history = this.history.slice();
        this.createAssist();
        for (const command of history)
            this.executeCommand(command, true);
        return this.snapshot();
    }
    qed() {
        const assist = this.requireAssist();
        assist.qed();
        const explicitAtNames = new Set();
        return {
            proof: parser.stringify(this.presentAst(assist.elem, explicitAtNames)),
            theorem: parser.stringify(this.presentAst(assist.theorem, explicitAtNames))
        };
    }
    clear() {
        this.assist = null;
        this.targetSource = "";
        this.history = [];
    }
    createAssist() {
        if (!this.targetSource)
            throw new Error(TR("空表达式"));
        Assist.disableMultipleApply = this.options?.disableMultipleApply ?? true;
        Assist.disableDestructConds = this.options?.disableDestructConds ?? true;
        Assist.disableDestructEq = this.options?.disableDestructEq ?? true;
        const target = markExplicitAtSyntax(parser.parse(this.targetSource));
        if (!target)
            throw new Error(TR("空表达式"));
        if (target.type === "===" || target.type === ":=" || target.type === ":") {
            throw new Error(TR(target.type === ":" ? "已断言该类型有值" : "不是命题类型"));
        }
        const type = this.engine.core.checkType(target, [], false);
        // Universe-polymorphic propositions (for example `Pi u:U@, ...`)
        // live in the Core's external sort `U@:` rather than an ordinary
        // `U level` application.  `U@` itself remains the type of level terms,
        // so values such as `@0` are still rejected as proof targets.
        if (!isProofTargetSort(type))
            throw new Error(TR("不是命题类型"));
        this.assist = new Assist(this.engine.core, target);
        this.history = [];
    }
    executeCommand(command, record) {
        const assist = this.requireAssist();
        const value = command.trim();
        const commandEnd = value.indexOf(" ");
        const name = commandEnd === -1 ? value : value.slice(0, commandEnd);
        const parameter = commandEnd === -1 ? null : value.slice(commandEnd);
        if (!name || name === "qed")
            throw new Error(TR("未知的证明策略"));
        const tactic = assist[name];
        if (typeof tactic !== "function" || name === "constructor" || name === "autofillTactics" || name === "markTargets") {
            throw new Error(TR("未知的证明策略"));
        }
        tactic.call(assist, parameter);
        if (record)
            this.history.push(value);
    }
    snapshot() {
        const assist = this.requireAssist();
        const tactics = assist.autofillTactics();
        assist.markTargets();
        const explicitAtNames = new Set();
        const theorem = this.presentAst(assist.theorem, explicitAtNames);
        // Intermediate proof terms intentionally contain dependent holes such as
        // (%0).  Checking the outer term before those holes are solved treats the
        // placeholders as user constants and emits misleading unknown-variable
        // / bound-variable diagnostics.  The completed term is checked by qed().
        if (!assist.goal.length) {
            try {
                this.engine.core.checkType(theorem, [], false, undefined, false, true);
            }
            catch { }
        }
        const goals = assist.goal.map(goal => {
            const type = Core.clone(goal.type, true);
            // A dependent constructor goal may refer to a proof hole from an
            // earlier goal (for example (%0) after `ex`).  That placeholder is
            // intentionally outside the local context until the earlier goal
            // is solved, so checking it now only produces a false unknown
            // variable / bound-variable diagnostic.
            const freeVars = Core.getFreeVars(type);
            const hasUnresolvedHole = Array.from(freeVars).some(name => name.startsWith("(%") || name.startsWith("(?#"));
            if (!hasUnresolvedHole) {
                try {
                    this.engine.core.checkType(type, goal.context, false, undefined, false, true);
                }
                catch { }
            }
            return {
                context: goal.context.map(([name, value, id]) => [
                    name,
                    this.presentAst(value, explicitAtNames),
                    id
                ]),
                type: this.presentAst(type, explicitAtNames),
                holeName: goal.ast.name
            };
        });
        return {
            theorem,
            elem: this.presentAst(assist.elem, explicitAtNames),
            goals,
            tactics,
            history: this.history.slice()
        };
    }
    presentAst(ast, explicitAtNames) {
        return restoreSemanticMetaNamesForDisplay(compactImplicitAliasesForDisplay(Core.clone(ast, true), this.engine.core.opaque, explicitAtNames));
    }
    requireAssist() {
        if (!this.assist)
            throw new Error(TR("请在定理列表中点选待证命题"));
        return this.assist;
    }
}
//# sourceMappingURL=assist-engine.js.map