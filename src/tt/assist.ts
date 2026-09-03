import { TR } from "../lang.js";
import { AST, ASTParser } from "./astparser.js";
import {
    assignContext,
    Context,
    Core,
    findContextByName,
    Varlist,
    wrapApply,
    wrapLambda,
    wrapVar,
    type CoreSystemInductiveMetadata
} from "./core.js";
import {
    hitPathConstructorCount,
    hitPathLevelsFromCanonicalOrLegacy
} from "./hit-path-levels.js";
import { markExplicitAtSyntax } from "./presentation.js";
let core = new Core;
let parser = new ASTParser;

/** Parse a user tactic/target expression without losing old replay support. */
function parseAssistInput(source: string): AST {
    return parser.parseSurfaceOrLegacy(source);
}
type GoalDependRel = { src: AST, dst: AST, goals: Goal[], varname: string };
export type Goal = { context: Context, type: AST, ast: AST, depend: GoalDependRel };
export class Assist {
    // the target theorem ast
    theorem: AST;
    // a goal has a context, a type (this is goal) and an ast pointer refered in elem
    goal: Goal[];
    // inhabited elem : theorem
    elem: AST;
    static disableMultipleApply = true;
    static disableDestructConds = true;
    static disableDestructEq = true;
    /** Names explicitly expanded while constructing this proof. */
    expandedDefinitions = new Set<string>();
    constructor(h: Core, target: AST | string) {
        core = h;
        core.clearSemanticState();
        // Direct Assist instances are also used by the engine/worker replay
        // path and by internal regression fixtures.  User-facing editors
        // validate their source with parseSurface before reaching this class;
        // keep this low-level constructor compatible with migrated/legacy AST
        // strings so replay does not reject historical targets.
        if (typeof target === "string") { target = markExplicitAtSyntax(parseAssistInput(target)); }
        this.theorem = Core.clone(target);
        // this.theorem = Core.clone(core.markBondVars(target, []),false);
        // this.theorem = core.markBondVars(core.desugar(Core.clone(target),false),[]);
        this.elem = { type: "var", name: "(?#0)", checked: target };
        this.goal = [{ context: [], type: target, ast: this.elem, depend: null }];
    }
    markTargets() {
        let count = 0;
        for (const g of this.goal) {
            g.ast.name = "(?#" + (count++) + ")";
            g.ast.checked = g.type;
        }
    }
    dependVarId = 0;
    private multipleApplyArity(valueName: string, goal: Goal) {
        if (Assist.disableMultipleApply) return 0;
        let fn: AST;
        try {
            fn = core.checkType(
                wrapVar(valueName),
                goal.context,
                false,
                undefined,
                false,
                true
            );
        } catch (e) {
            return 0;
        }
        let tail = fn;
        let fnWithHoles = wrapVar(valueName);
        let arity = 0;
        while (tail?.type === "P" || tail?.type === "->") {
            arity++;
            fnWithHoles = wrapApply(fnWithHoles, wrapVar("_"));
            tail = tail.nodes[1];
            try {
                core.checkType({
                    type: "===", name: "", nodes: [Core.clone(tail), Core.clone(goal.type)]
                }, goal.context, true, undefined, false, true);
                core.checkType({
                    type: ":", name: "", nodes: [Core.clone(fnWithHoles), Core.clone(goal.type)]
                }, goal.context, false, undefined, true, true);
                return arity;
            } catch (e) { }
        }
        return 0;
    }
    autofillTactics() {
        return core.withSilentErrors(() => this.collectAutofillTactics());
    }
    private collectAutofillTactics() {
        const tactics = [];
        const g = this.goal[0];
        if (!g) { return ["qed"]; }
        const type = g.type;
        const introVar = (n: string) => !type.name ? Core.getNewName(n, new Set(g.context.map(e => e[0]))) : type.name;
        const dynamicInductive = this.getDynamicInductiveMetadata(type);
        if (dynamicInductive) {
            tactics.push("constructor");
            for (const constructor of dynamicInductive.constructors) {
                const source = dynamicInductive.indexArguments.length
                    ? this.dynamicConstructorApplication(
                        constructor,
                        dynamicInductive.uniformArguments,
                        g
                    )
                    : this.dynamicConstructorSource(
                        constructor.name,
                        dynamicInductive.uniformArguments
                    );
                if (!source) continue;
                tactics.push(constructor.argumentTypes.length
                    ? "apply " + source
                    : "exact " + source);
            }
        } else if (type.type === "X") {
            tactics.push("case");
        } else if (type.type === "+" || type.type === "apply" && type.nodes?.[0]?.nodes?.[0]?.nodes?.[0]?.name === "Pushout") {
            tactics.push("left");
            tactics.push("right");
        } else if (type.type === "S") {
            // let found = false;
            for (const [k, v] of g.context) {
                if (Core.exactEqual(v, type.nodes[0])) {
                    tactics.push("ex " + k);
                    // found = true;
                }
            }
            tactics.push("ex");
        } else if (type.type === "P") {
            tactics.push("intro " + introVar(type.name));
        } else if (type.type === "W") {
            tactics.push("sup");
        } else if (type.name === "True") {
            tactics.push("exact true");
            return tactics;
        } else if (type.name === "Bool") {
            tactics.push("exact 0b");
            tactics.push("exact 1b");
        } else if (type.name === "nat") {
            tactics.push("exact 0");
            tactics.push("apply succ");
        } else if (type.name === "Z") {
            tactics.push("exact 0Z");
            tactics.push("apply pos");
            tactics.push("apply neg");
        } else if (type.name === "I") {
            tactics.push("apply 0I");
            tactics.push("apply 1I");
        } else if (type.type === "apply" && type.nodes[0].name === "Option") {
            tactics.push("exact none");
            tactics.push("apply some");
        } else if (type.type === "apply" && type.nodes[0].name === "List") {
            tactics.push("exact nil");
            tactics.push("apply cons");
        } else if (type.type === "apply" && type.nodes[0].name === "Even") {
            const index = Core.clone(type.nodes[1], true);
            this.whnf(index, g.context);
            const numeral = index.type === "var" && /^\d+$/.test(index.name) ? BigInt(index.name) : null;
            const doubleSuccessor = index.type === "apply"
                && index.nodes[0]?.name === "succ"
                && index.nodes[1]?.type === "apply"
                && index.nodes[1].nodes[0]?.name === "succ";
            if (numeral === 0n) tactics.push("exact even0");
            else if (doubleSuccessor || numeral !== null && numeral >= 2n) {
                tactics.push("apply evenss _");
            }
        } else if (type.type === "apply" && type.nodes[0].name === "Sus") {
            const a = parser.stringify(type.nodes[1]);
            tactics.push("exact North " + a);
            tactics.push("exact South " + a);
        } else if (type.name === "S1") {
            tactics.push("exact base");
        } else if (type.name === "S2") {
            tactics.push("exact base2");
        } else if (type.type === "->") {
            tactics.push("intro " + introVar("h"));
        } else {
            let matchEq = Core.match(type, parser.parse("$1 = $2"), /^\$/);
            if (!matchEq) matchEq = Core.match(type, parser.parse("eq $1 $2"), /^\$/);
            if (!matchEq) matchEq = Core.match(type, parser.parse("@eq $3 $4 $1 $2"), /^\$/);
            if (matchEq) {
                if (matchEq["$1"].name === "0I" && matchEq["$2"].name === "1I") tactics.push("apply segI");
                else if (matchEq["$1"].name === "1I" && matchEq["$2"].name === "0I" && core.hasConst("inveq")) tactics.push("apply inveq segI");
                if (matchEq["$1"].name === "base" && matchEq["$2"].name === "base") tactics.push("exact loop");
                try {
                    if (core.checkType({
                        type: "===",
                        name: "",
                        nodes: [Core.clone(matchEq["$1"]), Core.clone(matchEq["$2"])]
                    }, g.context, false, undefined, false, true)) {
                        tactics.push("rfl");
                    }
                } catch (e) { }
                if (this.semanticFunctionType(matchEq["$1"], g.context)) {
                    tactics.push("fnext");
                }
            }
        }
        const s = new Set<string>;
        for (const [val, typ] of g.context) {
            const matchEq = Core.match(typ, parser.parse("$2 = $3"), /^\$/) || Core.match(typ, parser.parse("eq $2 $3"), /^\$/) || Core.match(typ, parser.parse("@eq $0 $1 $2 $3"), /^\$/)
            if (matchEq) {
                const fnparam = "*";
                const fnbody2 = this.genReplaceFn(g.type, matchEq["$2"], fnparam, s);
                if (Core.getFreeVars(fnbody2).has(fnparam)) tactics.push("rw " + val);

                const fnbody3 = this.genReplaceFn(g.type, matchEq["$3"], fnparam, s);
                if (Core.getFreeVars(fnbody3).has(fnparam)) tactics.push("rwb " + val);
            }
            if (this.isIndType(typ)) {
                tactics.push("destruct " + val);
                if (this.getDynamicInductiveMetadata(typ)) tactics.push("induction " + val);
            }
            try {
                const k = Core.clone(typ);
                if (core.checkType({
                    type: "===", name: "", nodes: [
                        k, Core.clone(g.type)
                    ]
                }, g.context, true, undefined, false, true)) {
                    tactics.push("apply " + val);
                }
            } catch (e) { }
            try {
                const k2 = {
                    type: "===", name: "", nodes: [
                        Core.clone(typ), wrapLambda("P", "_", wrapVar("_"), Core.clone(g.type))
                    ]
                };
                if (core.checkType(k2, g.context, false, undefined, false, true))
                    tactics.push("apply " + val);
            } catch (e) { }
            if (!tactics.includes("apply " + val) && this.multipleApplyArity(val, g) > 1) {
                tactics.push("apply " + val);
            }
        }
        const simplified = this.semanticSimplification(type, g.context);
        if (simplified && !Core.exactEqual(simplified.source, simplified.normalized)) {
            tactics.push("simpl");
        }
        const vars = Core.getFreeVars(type);
        const defs1 = Object.keys(core.state.userDefs);
        const defs2 = Object.keys(core.state.sysDefs);
        const types = new Set(Object.keys(core.state.sysTypes));
        const defs = new Set([...defs1, ...defs2]);
        const ignore = new Set(["add", "mul", "addZ", "mulZ", "addO", "mulO", "leqO", "pair", "natO", "eq", "ua", "liftU", "LiftU", "lowerU", "rfl", "refl", "inl", "inr", "pr0", "pr1", "prd1"]);
        for (const v of defs) {
            if (vars.has(v) && !g.context.find(e => e[0] === v)) {
                if (ignore.has(v) || v.startsWith("ind_") || types.has("@" + v)) continue;
                tactics.push("expand " + v);
            }
        }
        const findEqv = (ast: AST) => {
            if (!ast) return false;
            if (ast.type === "~=") return true;
            if (ast.nodes?.length) return findEqv(ast.nodes[0]) || findEqv(ast.nodes[1]);
        }
        if (findEqv(type)) tactics.push("expand eqv");
        if (this.eq(true)) tactics.push("eq");
        return tactics;
    }
    resolveDependGoal(d: GoalDependRel) {
        if (!d) return;
        const { src, dst, varname, goals } = d;
        this.replaceFreeVar(dst, varname, src);
        for (const goal of goals) {
            this.replaceFreeVar(goal.type, varname, src);
            for (const [k, v, id] of goal.context) {
                this.replaceFreeVar(v, varname, src);
            }
        }
    }
    isIndType(typ: AST) {
        const dynamic = !!this.getDynamicInductiveMetadata(typ);
        return (dynamic || typ.name === "nat" || typ.name === "Bool" || typ.name === "I" || typ.name === "Z" || typ.name === "S1" || typ.name === "S2" || typ.name === "Ord" || typ.name === "True" || typ.name === "False" || (typ.type === "apply" && (typ.nodes[0].name === "Sus" || typ.nodes[0].name === "List" || typ.nodes[0].name === "Option" || typ.nodes[0].name === "Even" || typ.nodes[0]?.nodes?.[0]?.nodes?.[0]?.name === "Pushout"))
            || typ.type === "+" || typ.type === "[[]]" || typ.type === "X" || typ.type === "S" || typ.type === "W" || (!Assist.disableDestructEq && ((typ.type === "=") || typ.nodes?.[0]?.nodes?.[0]?.name === "eq")));
    }

    private getDynamicInductiveMetadata(typ: AST) {
        const application = core.flattenApplyList(typ);
        const head = application[0];
        if (head?.type !== "var" || !head.name) return undefined;
        const metadata = core.getInductiveMetadata?.(head.name);
        if (!metadata) return undefined;
        const uniformArguments = application.slice(1, metadata.parameters.length + 1);
        if (uniformArguments.length !== metadata.parameters.length) return undefined;
        const indexArguments = application.slice(
            metadata.parameters.length + 1,
            metadata.parameters.length + metadata.indices.length + 1
        );
        if (indexArguments.length !== metadata.indices.length
            || application.length !== metadata.parameters.length + metadata.indices.length + 1) {
            return undefined;
        }
        return {
            ...metadata,
            uniformArguments: uniformArguments.map(argument => Core.clone(argument)),
            indexArguments: indexArguments.map(argument => Core.clone(argument))
        };
    }

    private dynamicConstructorSource(name: string, uniformArguments: readonly AST[]) {
        return [name, ...uniformArguments.map(argument => parser.stringify(argument))].join(" ");
    }

    private dynamicConstructorApplication(
        constructor: { name: string; argumentTypes: readonly AST[] },
        uniformArguments: readonly AST[],
        goal: Goal
    ) {
        const source = this.dynamicConstructorSource(constructor.name, uniformArguments);
        const candidate = parseAssistInput(
            source + constructor.argumentTypes.map(() => " _").join("")
        );
        const assertion = {
            type: ":",
            name: "",
            nodes: [candidate, Core.clone(goal.type)]
        } as AST;
        try {
            core.withSilentErrors(() =>
                core.checkType(assertion, goal.context, true, undefined, true, true)
            );
            const elaborated = core.flattenApplyList(assertion.nodes[0]);
            const inferredArguments = elaborated.slice(uniformArguments.length + 1);
            const prefix: string[] = [];
            for (const argument of inferredArguments) {
                if (this.containsInferenceHole(argument)) break;
                prefix.push(parser.stringify(argument));
            }
            return [source, ...prefix].join(" ");
        } catch {
            return null;
        }
    }

    private universeLevelForType(type: AST, context: Context) {
        const sort = core.checkType(Core.clone(type), context, false);
        const application = core.flattenApplyList(sort);
        if (application[0]?.type !== "var" || application[0].name !== "U") return undefined;
        return application.length === 2 ? Core.clone(application[1]) : undefined;
    }
    intro(s: string) {
        s = s.trim();
        if (s.includes(" ")) {
            return this.intros(s);
        }
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        const tartgetType = goal.type;
        if (tartgetType.type !== "P" && tartgetType.type !== "->") {
            this.goal.unshift(goal);
            throw TR("intro 只能作用于函数类型");
        }
        s = Core.getNewName(s || tartgetType.name || "h", new Set(goal.context.map(e => e[0])));
        goal.context.unshift([s, tartgetType.nodes[0], 0]);
        // goal.ast is refferd at outter level hole,  we fill the hole first
        Core.assign(goal.ast, { "type": "L", name: s, nodes: [tartgetType.nodes[0], { type: "var", name: "(?#0)" }] }, true);
        goal.ast.checked = tartgetType;
        core.checkType(goal.ast.nodes[0], goal.context, false);

        // console.log(s + " : " + core.print(tartgetType.nodes[0]));
        const newtype = Core.clone(tartgetType.nodes[1]);
        this.replaceFreeVar(newtype, goal.type.name, { type: "var", name: s });
        // Core.assign(goal.type, newtype); // pq copy here? may contain dangerou refers
        goal.type = newtype;
        // then set goal.ast to refer the new smaller hole
        goal.ast = goal.ast.nodes[1];
        goal.ast.checked = goal.type;
        this.goal.unshift(goal);
        return this;
    }
    intros(s: string) {
        if (!s?.trim()) throw TR("意外的空表达式");
        s.split(/[\s,]+/).map(ss => ss ? this.intro(ss) : "");
        return this;
    }

    /**
     * Lean-style `rintro`: introduce binders and destructure one simple
     * product/sum pattern.  The proof tree already owns the dependent
     * eliminator, so this is deliberately a thin syntax layer over `intro`
     * and `destruct` rather than a second elimination implementation.
     */
    rintro(spec: string) {
        const patterns = this.splitRintroPatterns(spec?.trim() ?? "");
        if (!patterns.length) throw TR("rintro需要至少一个模式");
        for (const pattern of patterns) {
            if (/^[^\s,<>⟨⟩|()]+$/.test(pattern)) {
                this.intro(pattern === "_" ? "" : pattern);
                continue;
            }
            const pair = /^[<⟨]\s*([^,\s<>⟨⟩]+)\s*,\s*([^,\s<>⟨⟩]+)\s*[>⟩]$/.exec(pattern);
            if (pair) {
                const goal = this.goal[0];
                if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
                const temporary = Core.getNewName("h", new Set(goal.context.map(entry => entry[0])));
                this.intro(temporary);
                this.destruct(temporary, [pair[1], pair[2]]);
                this.reorderContextBindings(this.goal[0], [pair[1], pair[2]]);
                continue;
            }
            throw TR("rintro暂不支持该模式：") + pattern;
        }
        return this;
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

    private reorderContextBindings(goal: Goal | undefined, names: readonly string[]) {
        if (!goal || !names.length) return;
        const requested = new Set(names);
        const bindings = new Map(goal.context
            .filter(([name]) => requested.has(name))
            .map(entry => [entry[0], entry] as const));
        if (bindings.size !== names.length) return;
        goal.context = [
            ...names.map(name => bindings.get(name)),
            ...goal.context.filter(([name]) => !requested.has(name))
        ];
    }

    /** Change the current goal to a definitionally equal surface type. */
    change(spec: string) {
        const source = spec?.trim() ?? "";
        if (!source) throw TR("change需要一个目标类型");
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        let target: AST;
        try {
            target = markExplicitAtSyntax(parseAssistInput(source));
            core.checkType({
                type: "===", name: "", nodes: [Core.clone(goal.type), Core.clone(target)]
            }, goal.context, false, undefined, false, true);
        } catch (error) {
            this.goal.unshift(goal);
            throw error;
        }
        goal.type = target;
        goal.ast.checked = goal.type;
        this.goal.unshift(goal);
        return this;
    }

    /** Lean's `show` spelling for changing a definitionally equal goal. */
    show(spec: string) {
        return this.change(spec);
    }

    /** Lean-style aliases for common structural tactics. */
    cases(spec: string) {
        const value = spec?.trim() ?? "";
        if (!value) throw TR("cases需要一个变量名");
        // `cases n with d dh` is accepted as the compact form used by the
        // induction implementation; a bare `cases n` keeps the existing
        // destruct behavior and generated names.
        return /\s+with\s+/i.test(value) ? this.induction(value) : this.destruct(value);
    }

    /** Lean's `rcases` spelling is equivalent for this dependent eliminator. */
    rcases(spec: string) {
        return this.cases(spec);
    }

    /** Construct the current goal using its canonical inductive constructor. */
    construct() {
        const goal = this.goal[0];
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        const dynamicInductive = this.getDynamicInductiveMetadata(goal.type);
        const dynamicConstructor = dynamicInductive?.constructors
            .map(constructor => ({
                constructor,
                source: this.dynamicConstructorApplication(
                    constructor,
                    dynamicInductive.uniformArguments,
                    goal
                )
            }))
            .find(candidate => !!candidate.source);
        if (dynamicConstructor) {
            const source = dynamicConstructor.source;
            return dynamicConstructor.constructor.argumentTypes.length
                ? this.apply(source)
                : this.exact(source);
        }
        if (goal.type.type === "X") return this.case();
        if (goal.type.type === "S") return this.ex("");
        if (goal.type.name === "True") return this.exact("true");
        if (goal.type.type === "=" || goal.type.nodes?.[0]?.nodes?.[0]?.name === "eq") return this.rfl();
        throw TR("constructor无法确定当前目标的构造子，请使用left、right、case或ex");
    }

    /** Close a goal with the first local value whose type checks against it. */
    assumption() {
        const goal = this.goal[0];
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        for (const [name] of goal.context) {
            try {
                core.checkType({
                    type: ":",
                    name: "",
                    nodes: [wrapVar(name), Core.clone(goal.type)]
                }, goal.context, false);
                return this.exact(name);
            } catch { }
        }
        throw TR("未找到与当前目标匹配的假设");
    }

    /** Lean's `simp` spelling, with `simpa using h` for a local proof term. */
    simp(str?: string) {
        return this.simpl(str);
    }

    simpa(str?: string) {
        const value = str?.trim() ?? "";
        const usingMatch = /^(?:(.*?)\s+)?using\s+([\s\S]+)$/i.exec(value);
        if (!usingMatch) return this.simpl(value);
        this.simpl(usingMatch[1]?.trim() ?? "");
        return this.exact(usingMatch[2].trim());
    }

    static eq_matches = ([
        ["$1*rfl", "rightrfl $1", ["rightrfl"]],
        ["$1*(refl $2)", "rightrfl $1", ["rightrfl"]],
        ["inveq (inveq $1)", "invinveq $1", ["invinveq"]],
        ["$1 * (inveq $1)", "rightinveq $1", ["rightinveq"]],
        ["(inveq $1) * $1", "leftinveq $1", ["leftinveq"]],
        ["inveq ($1*$2)", "compinveq $1 $2", ["compinveq"]],
        ["($1*$2)*(inveq $2)", "compeqassoc $1 $2 (inveq $2)", ["compeqassoc"]],
        ["($1*(inveq $2))*$2", "compeqassoc $1 (inveq $2) $2", ["compeqassoc"]],
        ["(inveq $2)*($2*$1)", "inveq(compeqassoc (inveq $2) $2 $1)", ["compeqassoc"]],
        ["$2*((inveq $2)*$1)", "inveq(compeqassoc $2 (inveq $2) $1)", ["compeqassoc"]],
        ["trans (eq $x0) $p $q", "transright $p $q", ["transright"]],
        ["happly (fnext $x)", "happly_fnext $x"],
        ["fnext (happly $x)", "fnext_happly $x"],
        ["ua (id2eqv $x)", "ua_id2eqv $x"],
        ["id2eqv (ua $x)", "id2eqv_ua $x"],
        ["predZ (succZ $x)", "pred_succZ $x", ["pred_succZ"]],
        ["succZ (predZ $x)", "succ_predZ $x", ["succ_predZ"]],
        ["apd $C (ind_S1 $C $cb $cl) loop", "apd_loop $cl", ["apd_loop"]],
        ["ap (rec_S1 $cb $cl) loop", "ap_loop $cl", ["ap_loop"]],
        ["ap (ind_S1 $C $cb (transconst loop $cb)*$cl) loop", "ap_loop $cl", ["ap_loop"]],
        ["ap $apfn $p", "_"],// special case
        ["trans $transfn $p $x", "_"], // special case
    ] as [string, string, string[]][]).map(e => [parser.parse(e[0]), parser.parse(e[1]), e[2] || []] as [AST, AST, string[]]);
    eq(test?: boolean) {
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        this.goal.unshift(goal);
        const recurse = (ast: AST, pattern: AST, resArr: Varlist[] = []) => {
            let res: Varlist;
            res = Core.match(ast, pattern, /^\$/);
            if (res) resArr.push(res);
            if (ast.nodes?.length === 2) {
                recurse(ast.nodes[0], pattern, resArr);
                recurse(ast.nodes[1], pattern, resArr);
            }
            return resArr;
        }
        const fvs = Core.getFreeVars(goal.type);
        for (let [pattern, eq, evidences] of Assist.eq_matches) {
            let unlock_yet = false;
            for (let e of evidences) {
                if (!core.hasConst(e)) {
                    unlock_yet = true;
                    break;
                }
            }
            if (unlock_yet) continue;
            const resarr = recurse(goal.type, pattern);
            for (const res of resarr) {
                const npattern = Core.clone(pattern); Core.replaceByMatch(npattern, res, /^\$/);
                for (const v of Core.getFreeVars(npattern)) {
                    // if a freevar is captured, fail
                    if (!fvs.has(v)) return false;
                }
                let tfn = res["$transfn"];
                if (tfn?.type === "L") {
                    const paramType = tfn.nodes[0];
                    const fnbody = tfn.nodes[1];
                    if (!Core.getFreeVars(fnbody).has(tfn.name) && core.hasConst("transconst")) {
                        eq = wrapApply(wrapVar("transconst"), res["$p"], res["$x"]);
                    } else if (fnbody.type === "=" || (fnbody.nodes?.[0]?.nodes?.[0]?.name === "eq")) {
                        let l: AST, r: AST;
                        if (fnbody.type === "=") [l, r] = fnbody.nodes;
                        else { l = fnbody.nodes[0].nodes[1]; r = fnbody.nodes[1]; }
                        if (l.type == "var" && l.name === tfn.name) {
                            if (r.type == "var" && r.name === tfn.name && core.hasConst("transleftright")) {
                                eq = wrapApply(wrapVar("transleftright"), res["$p"], res["$x"]);
                            } else if (!Core.getFreeVars(r).has(tfn.name) && core.hasConst("transleft")) {
                                eq = wrapApply(wrapVar("transleft"), res["$p"], res["$x"]);
                            } else if (core.hasConst("transeq")) {
                                eq = wrapApply(wrapVar("transeq"), wrapLambda("L", tfn.name, paramType, l), wrapLambda("L", tfn.name, paramType, r), res["$p"], res["$x"]);
                            }
                        } else if (r.type == "var" && r.name === tfn.name && !Core.getFreeVars(l).has(tfn.name)) {
                            eq = wrapApply(wrapVar("transright"), res["$p"], res["$x"]);
                        } else if (core.hasConst("transeq")) {
                            eq = wrapApply(wrapVar("transeq"), wrapLambda("L", tfn.name, paramType, l), wrapLambda("L", tfn.name, paramType, r), res["$p"], res["$x"]);
                        }
                    } else continue;
                }
                tfn = res["$apfn"];
                if (tfn?.type === "L") {
                    const fnbody = tfn.nodes[1];
                    if (!Core.getFreeVars(fnbody).has(tfn.name) && core.hasConst("apconst")) {
                        eq = wrapApply(wrapVar("apconst"), res["$p"], fnbody);
                    } else if (fnbody.type === "var" && fnbody.name === tfn.name && core.hasConst("apid")) {
                        eq = wrapApply(wrapVar("apid"), res["$p"]);
                    } else continue;
                }
                if (eq.name === "_") continue;
                if (!test) {
                    const neq = Core.clone(eq); Core.replaceByMatch(neq, res, /^\$/);
                    this.rw(neq, false, npattern);
                } else {
                    return true;
                }
            }
        }
    }
    exact(ast: AST | string) {
        // Assist is also the compatibility/replay layer.  GUI-edited source
        // is validated with parseSurface before it reaches this class; keep
        // command arguments on the legacy parser so saved histories and
        // internal fixtures can be replayed after the one-shot save migration.
        if (typeof ast === "string") { ast = markExplicitAtSyntax(parseAssistInput(ast)); }
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        let context = goal.context;
        const hasInputHoles = this.containsInputHole(ast);
        try {
            const k = hasInputHoles
                ? this.elaborateAndAutofill(ast, goal.type, context)
                : Core.clone(ast);
            if (!hasInputHoles) {
                core.checkType({
                    type: ":", name: "", nodes: [
                        k, Core.clone(goal.type)
                    ]
                }, context, false);
            }
            Core.assign(goal.ast, k, true);
            this.resolveDependGoal(goal.depend);
            return this;
        } catch (e) {
            if (hasInputHoles) throw e;
            try {
                core.checkType(ast, context, false);
            } catch (e) {
                throw e;
            }
            throw TR("无法对类型") + parser.stringify(ast.checked) + TR("使用exact策略作用于类型") + parser.stringify(goal.type);
        }
    }
    private containsInputHole(ast: AST): boolean {
        return !!ast && (ast.type === "var" && ast.name === "_"
            || (ast.nodes ?? []).some(node => this.containsInputHole(node)));
    }
    private containsInferenceHole(ast: AST): boolean {
        return !!ast && (ast.type === "var"
            && (ast.name === "_" || ast.name?.startsWith("?"))
            || (ast.nodes ?? []).some(node => this.containsInferenceHole(node)));
    }
    private clearBondIds(ast: AST, seen = new WeakSet<object>()) {
        if (!ast || typeof ast !== "object" || seen.has(ast)) return;
        seen.add(ast);
        delete ast.bondVarId;
        for (const node of ast.nodes ?? []) this.clearBondIds(node, seen);
        if (ast.checked) this.clearBondIds(ast.checked, seen);
    }
    private findInputHole(ast: AST): AST | null {
        if (!ast) return null;
        if (ast.type === "var" && ast.name === "_") return ast;
        for (const node of ast.nodes ?? []) {
            const hole = this.findInputHole(node);
            if (hole) return hole;
        }
        return null;
    }
    private runAutofillCommand(command: string) {
        const commandEnd = command.indexOf(" ");
        const name = commandEnd === -1 ? command : command.slice(0, commandEnd);
        const parameter = commandEnd === -1 ? null : command.slice(commandEnd);
        const tactic = (this as unknown as Record<string, (...args: any[]) => unknown>)[name];
        if (typeof tactic !== "function" || name === "constructor"
            || name === "autofillTactics" || name === "markTargets" || name === "qed") {
            throw TR("未知的证明策略");
        }
        tactic.call(this, parameter);
    }
    private autofillTerm(type: AST, context: Context) {
        const savedGoals = this.goal;
        const root = wrapVar("(?#auto)");
        root.checked = Core.clone(type, true);
        this.goal = [{
            context: Core.cloneContext(context),
            type: Core.clone(type, true),
            ast: root,
            depend: null
        }];
        try {
            const seenStates = new Set<string>();
            for (let step = 0; step < 64 && this.goal.length; step++) {
                const command = this.autofillTactics().find(tactic => tactic !== "qed");
                if (!command) throw TR("无法自动填入") + parser.stringify(type);
                const stateKey = command + "\n" + this.goal
                    .map(goal => parser.stringify(goal.type))
                    .join("\n");
                if (seenStates.has(stateKey)) {
                    throw TR("无法自动填入") + parser.stringify(type);
                }
                seenStates.add(stateKey);
                this.runAutofillCommand(command);
            }
            if (this.goal.length) throw TR("自动填入步骤过多");
            return root;
        } finally {
            this.goal = savedGoals;
        }
    }
    private elaborateAndAutofill(ast: AST, expected: AST, context: Context) {
        let term = Core.clone(ast);
        for (let step = 0; step < 64; step++) {
            const assertion = {
                type: ":", name: "", nodes: [term, Core.clone(expected)]
            } as AST;
            core.checkType(assertion, context, true, undefined, true, true);
            term = assertion.nodes[0];
            const hole = this.findInputHole(term);
            if (!hole) return term;
            const holeType = hole.checked;
            if (!holeType || this.containsInputHole(holeType)) {
                throw TR("无法自动确定占位符类型");
            }
            Core.assign(hole, this.autofillTerm(holeType, context), true);
        }
        throw TR("自动填入步骤过多");
    }
    apply(ast: AST | string) {
        if (typeof ast === "string") {
            const source = ast.trim();
            const atMatch = /^(.*)\s+at\s+([^\s]+)$/.exec(source);
            if (atMatch && atMatch[1].trim()) return this.applyAt(atMatch[1], atMatch[2]);
            ast = markExplicitAtSyntax(parseAssistInput(source));
        }
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        let context = goal.context;
        const hasInputHoles = this.containsInputHole(ast);
        const autoFillSurfaceHoles = hasInputHoles;
        let explicitExactError: unknown;
        if (autoFillSurfaceHoles) {
            try {
                const completed = this.elaborateAndAutofill(ast, goal.type, context);
                Core.assign(goal.ast, completed, true);
                this.resolveDependGoal(goal.depend);
                return this;
            } catch (e) {
                explicitExactError = e;
            }
        } else {
            try {
                const k = Core.clone(ast);
                core.checkType({
                    type: ":", name: "", nodes: [
                        k, Core.clone(goal.type)
                    ]
                }, context, false);
                Core.assign(goal.ast, k, true);
                this.resolveDependGoal(goal.depend);
                return this;
            } catch (e) { }
        }
        let applyType: AST = null;
        let checkedApplyAst: AST = null;
        try {
            const k = {
                type: ":", name: "", nodes: [
                    Core.clone(ast), wrapLambda("P", "_", wrapVar("_"), Core.clone(goal.type))
                ]
            };
            if (autoFillSurfaceHoles) {
                checkedApplyAst = this.elaborateAndAutofill(k.nodes[0], k.nodes[1], context);
            } else {
                core.checkType(k, context, false);
                checkedApplyAst = k.nodes[0];
            }
            const checkedFunctionType = checkedApplyAst.checked;
            applyType = checkedFunctionType?.type === "P" || checkedFunctionType?.type === "->"
                ? checkedFunctionType.nodes[0]
                : k.nodes[1].nodes[0];
            if (applyType.checked?.type === ":") {
                applyType = applyType.checked.nodes[0];
            }
        } catch (e) {
            this.goal.unshift(goal);
            if (autoFillSurfaceHoles) throw explicitExactError ?? e;
            try {
                if (Assist.disableMultipleApply) throw e;
                this.apply2(ast); return;
            } catch (e) {
                try {
                    core.checkType(ast, context, false);
                } catch (e) {
                    throw e;
                }
                throw TR("无法对类型") + parser.stringify(ast.checked) + TR("使用apply策略作用于类型") + parser.stringify(goal.type);
            }
        }
        if (checkedApplyAst?.checked) ast = checkedApplyAst;
        else core.checkType(ast, context, false);
        // goal.ast is refferd at outter level hole,  we fill the hole first
        Core.assign(goal.ast, {
            type: "apply", name: "", nodes: [ast, {
                type: "var", name: "(?#0)", checked: applyType
            }], checked: goal.type
        }, true);
        // then set goal.ast to refer the new smaller hole
        goal.ast = goal.ast.nodes[1];
        goal.type = applyType;
        this.goal.unshift(goal);
        return this;
    }
    /**
     * Lean-style `apply f at h`: use `h` as the first argument of `f`,
     * replace the local binding with the resulting type, and expose any
     * remaining function arguments as ordinary proof goals.
     */
    applyAt(sourceText: string, hypothesisName: string) {
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        const sourceContext = goal.context;
        const bindingIndex = sourceContext.findIndex(([name]) => name === hypothesisName);
        if (bindingIndex < 0) {
            this.goal.unshift(goal);
            throw TR("未知的变量：") + hypothesisName;
        }
        const hypothesisType = Core.clone(sourceContext[bindingIndex][1]);
        let source: AST;
        let sourceType: AST;
        try {
            source = markExplicitAtSyntax(parseAssistInput(sourceText.trim()));
            sourceType = core.checkType(source, sourceContext, false);
            if (sourceType.type !== "P" && sourceType.type !== "->") {
                throw TR("apply at 来源必须是函数类型");
            }
            core.checkType({
                type: ":", name: "", nodes: [wrapVar(hypothesisName), Core.clone(sourceType.nodes[0])]
            }, sourceContext, false);
        } catch (error) {
            this.goal.unshift(goal);
            throw error;
        }

        const firstArgument = wrapVar(hypothesisName);
        firstArgument.checked = hypothesisType;
        let application = wrapApply(source, firstArgument);
        let resultType = Core.clone(sourceType.nodes[1]);
        if (sourceType.type === "P") this.replaceFreeVar(resultType, sourceType.name, firstArgument);

        const newGoals: Goal[] = [];
        const dependencies = new Map<string, {
            hole: AST;
            sourceGoal: Goal;
            varname: string;
            dependents: Goal[];
        }>();
        let holeIndex = 0;
        while (resultType.type === "P" || resultType.type === "->") {
            let parameterType = Core.clone(resultType.nodes[0]);
            for (const [holeName, dependency] of dependencies) {
                if (!Core.getFreeVars(parameterType).has(holeName)) continue;
                if (!dependency.varname) dependency.varname = this.getNewDependGoalVarName();
                this.replaceFreeVar(parameterType, holeName, wrapVar(dependency.varname));
            }
            const hole = wrapVar("(?#at" + (holeIndex++) + ")");
            hole.checked = parameterType;
            const premiseGoal: Goal = {
                context: Core.cloneContext(sourceContext),
                ast: hole,
                type: parameterType,
                depend: null
            };
            newGoals.push(premiseGoal);
            dependencies.set(hole.name, { hole, sourceGoal: premiseGoal, varname: "", dependents: [] });
            application = wrapApply(application, hole);
            if (resultType.type === "P") {
                const body = Core.clone(resultType.nodes[1]);
                this.replaceFreeVar(body, resultType.name, hole);
                resultType = body;
            } else {
                resultType = Core.clone(resultType.nodes[1]);
            }
            const current = newGoals.at(-1)!;
            for (const dependency of dependencies.values()) {
                const marker = dependency.varname || dependency.hole.name;
                if (dependency.sourceGoal === current || !Core.getFreeVars(current.type).has(marker)) continue;
                dependency.dependents.push(current);
            }
        }

        for (const [holeName, dependency] of dependencies) {
            if (!Core.getFreeVars(resultType).has(holeName)) continue;
            if (!dependency.varname) dependency.varname = this.getNewDependGoalVarName();
            this.replaceFreeVar(resultType, holeName, wrapVar(dependency.varname));
        }
        const bodyHole = wrapVar("(?#0)");
        bodyHole.checked = goal.type;
        const continuationContext = Core.cloneContext(
            sourceContext.filter((_entry, index) => index !== bindingIndex)
        );
        continuationContext.unshift([hypothesisName, resultType, 0]);
        const wrapped = wrapApply(
            wrapLambda("L", hypothesisName, resultType, bodyHole),
            application
        );
        Core.assign(goal.ast, wrapped, true);
        goal.ast = goal.ast.nodes[0].nodes[1];
        goal.ast.checked = goal.type;
        goal.context = continuationContext;

        for (const dependency of dependencies.values()) {
            if (!dependency.varname) continue;
            dependency.sourceGoal.depend = {
                src: dependency.hole,
                dst: resultType,
                goals: [...dependency.dependents, goal],
                varname: dependency.varname
            };
        }
        this.goal.unshift(goal);
        this.goal.unshift(...newGoals);
        return this;
    }

    /** Lean-style `specialize h a ...`, replacing a local function fact. */
    specialize(spec: string) {
        const value = spec?.trim() ?? "";
        const match = /^([^\s]+)\s+([\s\S]+)$/.exec(value);
        if (!match) throw TR("specialize语法应为 specialize h 参数...");
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        const bindingIndex = goal.context.findIndex(([name]) => name === match[1]);
        if (bindingIndex < 0) {
            this.goal.unshift(goal);
            throw TR("未知的变量：") + match[1];
        }
        const sourceContext = goal.context;
        let term: AST;
        let resultType: AST;
        try {
            term = markExplicitAtSyntax(parseAssistInput(value));
            resultType = core.checkType(term, sourceContext, false);
        } catch (error) {
            this.goal.unshift(goal);
            throw error;
        }
        const bodyHole = wrapVar("(?#0)");
        bodyHole.checked = goal.type;
        const continuationContext = Core.cloneContext(
            sourceContext.filter((_entry, index) => index !== bindingIndex)
        );
        continuationContext.unshift([match[1], Core.clone(resultType), 0]);
        const wrapped = wrapApply(
            wrapLambda("L", match[1], Core.clone(resultType), bodyHole),
            term
        );
        Core.assign(goal.ast, wrapped, true);
        goal.ast = goal.ast.nodes[0].nodes[1];
        goal.ast.checked = goal.type;
        goal.context = continuationContext;
        this.goal.unshift(goal);
        return this;
    }

    apply2(ast: AST) {
        const goal = this.goal.shift();
        let fn: AST;
        try { fn = core.checkType(ast, goal.context, false); } catch (e) {
            this.goal.unshift(goal);
            throw e;
        }

        let tail = fn;
        let holeNumbers = 1;
        let fnWith_ = ast;
        while (true) {
            fnWith_ = wrapApply(fnWith_, wrapVar("_"));
            if (tail.type === "->" || tail.type === "P") { tail = tail.nodes[1]; } else {
                this.goal.unshift(goal);
                throw TR("无法对类型") + parser.stringify(ast.checked) + TR("使用apply策略作用于类型") + parser.stringify(goal.type);
            }
            try {
                core.checkType(wrapLambda("===", "", Core.clone(tail), Core.clone(goal.type)), goal.context, true);
                core.checkType(
                    { nodes: [fnWith_, Core.clone(goal.type)], type: ":", name: "" },
                    goal.context,
                    false,
                    undefined,
                    true
                );
                break;
            } catch (e) { }
            holeNumbers++;
        }
        for (let i = holeNumbers; i > 0; i--) {
            fnWith_ = fnWith_.nodes[0];
        }
        fn = fnWith_.checked;
        const fnParams = this.flattenParams(fn, true);
        const fnParamNames = this.flattenParamNames(fn);

        const fnBody = [];
        const newGoals: Goal[] = [];
        const dependence: number[][] = [];

        for (let i = 0; i < holeNumbers; i++) {
            const fnParamType = fnParams[i];
            const fnParamName = fnParamNames[i];
            const gast = wrapVar("(?#0)");
            const ctx = Core.cloneContext(goal.context);
            gast.checked = fnParamType;
            // mark depend
            const depend = [];
            if (fnParamName) {
                for (let j = i; j < holeNumbers; j++) {
                    if (j === i) continue;
                    if (Core.getFreeVars(fnParams[j]).has(fnParamName)) {
                        depend.push(j);
                    }
                }
            }
            dependence.push(depend);
            newGoals.push({ context: ctx, ast: gast, type: fnParamType, depend: null });
            fnBody.push(gast);
        }
        // record dependences in goals
        for (let i = 0; i < holeNumbers; i++) {
            const d = dependence[i];
            if (!d.length) continue;
            const goals = d.map(j => newGoals[j]);
            const varname = this.getNewDependGoalVarName();
            newGoals[i].depend = {
                src: newGoals[i].ast, dst: goal.ast, goals, varname
            };
            const srcname = fnParamNames[i];
            for (const g of goals) {
                this.replaceFreeVar(g.type, srcname, wrapVar(varname));
            }
        }
        Core.assign(goal.ast, wrapApply(ast, ...fnBody), true);
        if (!newGoals.length) {
            this.resolveDependGoal(goal.depend);
            return;
        }
        newGoals[newGoals.length - 1].depend = goal.depend;
        this.goal.unshift(...newGoals);
    }
    rw(eq: string | AST, back: boolean = false, forcingMatchAST?: AST) {
        if (typeof eq === "string") {
            const source = eq.trim();
            if (source.startsWith("[") && source.endsWith("]")) {
                const entries = this.splitTopLevelCommaList(source.slice(1, -1));
                if (!entries.length) throw TR("rw改写列表不能为空");
                for (const entry of entries) this.rw(entry);
                return this;
            }
        }
        if (typeof eq === "string") eq = markExplicitAtSyntax(parseAssistInput(eq));
        if (!eq) throw TR("请输入用于改写的相等假设");
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        let matched: { [variable: string]: AST; };
        const matchEquality = (type: AST) => Core.match(type, parser.parse("$2 = $3"), /^\$/)
            || Core.match(type, parser.parse("eq $2 $3"), /^\$/)
            || Core.match(type, parser.parse("@eq $0 $1 $2 $3"), /^\$/);
        const containsInputHole = (ast: AST) => ast?.type === "var" && ast.name === "_"
            || (ast?.nodes ?? []).some(containsInputHole);
        const hadInputHoles = containsInputHole(eq);
        if (hadInputHoles) {
            // Explicit rewrite holes are inferred from the occurrence being
            // rewritten. Probe larger target subterms first, constraining the
            // theorem's source (or destination for rwb) to each candidate.
            const candidates: AST[] = [];
            const stack = [forcingMatchAST || goal.type];
            const seen = new WeakSet<object>();
            while (stack.length && candidates.length < 512) {
                const candidate = stack.pop();
                if (!candidate || typeof candidate !== "object" || seen.has(candidate)) continue;
                seen.add(candidate);
                candidates.push(candidate);
                const nodes = candidate.nodes ?? [];
                for (let index = nodes.length - 1; index >= 0; index--) {
                    stack.push(nodes[index]);
                }
            }
            for (const candidate of candidates) {
                const expectedEquality = back
                    ? wrapApply(wrapVar("eq"), wrapVar("_"), Core.clone(candidate))
                    : wrapApply(wrapVar("eq"), Core.clone(candidate), wrapVar("_"));
                let completed: AST;
                try {
                    completed = this.elaborateAndAutofill(
                        eq,
                        expectedEquality,
                        goal.context
                    );
                } catch {
                    continue;
                }
                if (containsInputHole(completed)) continue;
                const inferredType = completed.checked;
                const inferredMatch = inferredType && matchEquality(inferredType);
                if (!inferredMatch) continue;
                eq = completed;
                matched = inferredMatch;
                break;
            }
            if (!matched) {
                this.goal.unshift(goal);
                throw TR("未找到任何指定改写的项");
            }
        } else {
            try {
                const t = core.checkType(eq, goal.context, false);
                matched = matchEquality(t);
            } catch (e) {
                this.goal.unshift(goal);
                throw e;
            }
        }
        let isRfl = false;
        try {
            core.checkType(
                wrapLambda("===", "", eq, wrapVar("rfl")),
                goal.context,
                false,
                undefined,
                false,
                hadInputHoles
            );
            isRfl = true;
        } catch (e) {

        }

        if (!matched) {
            this.goal.unshift(goal);
            throw TR("使用rewrite策略必须提供一个相等类型");
        }
        matched["$eq"] = eq;
        const ctxtSet = new Set(goal.context.map(e => e[0]));
        const fnbody = this.genReplaceFn(goal.type, forcingMatchAST || matched[back ? "$3" : "$2"], "(?#)", ctxtSet);
        const fnparam = Core.getNewName("x", ctxtSet);
        this.replaceFreeVar(fnbody, "(?#)", wrapVar(fnparam));
        // eq: eleq: eq t a b
        // type: F(a/b) 
        // F(a/b)->F(a/b), eleq  |- F(b/a)->F(a/b) 
        // newgoal: F(b/a)
        const fn = { type: "L", name: fnparam, nodes: [core.checkType(matched[back ? "$3" : "$2"], goal.context, false), fnbody] };
        matched["$fn"] = fn;
        const rewrittenGoal = Core.clone(fn.nodes[1]);
        this.replaceFreeVar(rewrittenGoal, fnparam, matched[back ? "$2" : "$3"]);
        if (!isRfl) {
            matched["$type"] = matched[back ? "$3" : "$2"].checked;
            const y = Core.getNewName("y", ctxtSet);
            const m = Core.getNewName("m", ctxtSet);
            // F(a/b)
            matched["$fn_2"] = Core.clone(fnbody); this.replaceFreeVar(matched["$fn_2"], fnparam, matched["$2"]);
            // F(a/#y)
            matched["$fn_y"] = Core.clone(fnbody); this.replaceFreeVar(matched["$fn_y"], fnparam, wrapVar(y));
            let compeq = {};
            Core.match(fnbody, parser.parse("$1 = " + fnparam), /^\$/, compeq) ||
                Core.match(fnbody, parser.parse("eq $1 " + fnparam), /^\$/, compeq = {}) ||
                Core.match(fnbody, parser.parse("eq " + fnparam + " $2"), /^\$/, compeq = {}) ||
                Core.match(fnbody, parser.parse(fnparam + " = $2"), /^\$/, compeq = {});
            let newAst: AST;
            const wrapInvOrNot = (ast: AST, wrap: boolean) => wrap ? wrapApply(wrapVar("inveq"), ast) : ast;
            if (compeq["$2"] && !Core.getFreeVars(compeq['$2']).has(fnparam) && (!back || core.hasConst("inveq")) && core.hasConst("compeq")) {
                // h:a0=a1, a0=b -> ?:a1=b =>  h * ? 
                // h:a0=a1, a1=b -> ?:a0=b =>  inv(h) * ? 
                const newGoalAst = { type: "var", name: "(?#0)" };
                newAst = wrapLambda("*", "", wrapInvOrNot(eq, back), newGoalAst);
                Core.assign(goal.ast, newAst);
                goal.ast.checked = goal.type;
                goal.ast = goal.ast.nodes[1];
            } else if (compeq["$1"] && !Core.getFreeVars(compeq['$1']).has(fnparam) && (back || core.hasConst("inveq")) && core.hasConst("compeq")) {
                // h:b0=b1, a=b0 -> ?:a=b1 =>  ? * inv(h) 
                // h:b0=b1, a=b1 -> ?:a=b0 =>  ? * h 
                const newGoalAst = { type: "var", name: "(?#0)" };
                newAst = wrapLambda("*", "", newGoalAst, wrapInvOrNot(eq, !back));
                Core.assign(goal.ast, newAst);
                goal.ast.checked = goal.type;
                goal.ast = goal.ast.nodes[0];
            } else {
                const useTrans = core.hasConst("trans") && (back || core.hasConst("inveq"));
                newAst = parser.parse(useTrans ?
                    `trans $fn ` + (back ? `$eq` : `(inveq $eq)`) : `ind_eq $2 (L${y}:$type.L${m}:${core.state.disableSimpleEq ? `eq $2 ` + y : `$2=${y}`}. P${m}:` + (back ? `$fn_2, $fn_y` : `$fn_y, $fn_2`) + `) (Lx:_.x) $3 $eq`);
                Core.replaceByMatch(newAst, matched, /^\$/);
                // The equality proof and both endpoint types were checked
                // above, while fnbody was obtained by capture-safe
                // substitution from the live goal.  Re-synthesizing this
                // mechanically constructed transport is redundant and can
                // expand every implicit alias in a large HoTT goal, creating
                // thousands of unrelated metas before reaching the known
                // function type.
                newAst = { type: "apply", name: "", nodes: [newAst, { type: "var", name: "(?#0)" }] };
                Core.assign(goal.ast, newAst, true);
                goal.ast.checked = goal.type;
                goal.ast = goal.ast.nodes[1];
            }
        }
        goal.type = rewrittenGoal;
        goal.ast.checked = goal.type;
        this.goal.unshift(goal);
        return this;
    }

    private splitTopLevelCommaList(source: string): string[] {
        const result: string[] = [];
        let current = "";
        let depth = 0;
        for (const char of source) {
            if (char === "," && depth === 0) {
                if (current.trim()) result.push(current.trim());
                current = "";
                continue;
            }
            current += char;
            if ("([{<".includes(char)) depth++;
            else if (")]}>".includes(char)) depth = Math.max(0, depth - 1);
        }
        if (current.trim()) result.push(current.trim());
        return result;
    }
    rwb(eq: string | AST) {
        this.rw(eq, true);
        return this;
    }
    trunc(n: string | AST) {
        // todo: 1. goal is [[a]] -> apply Lx.[x],then goal is a
        // todo: 2. goal is a = b -> apply trunc a b 
        // in autofill, there will be a condition: goal is [[a]] = b or [[a]] = [[b]] or a = [[b]]
    }
    // replace "search" in ast by "varname"
    genReplaceFn(ast: AST, search: AST, varname: string, excludedNames: Set<string>, freevarsinSearch = Core.getFreeVars(search), scope: string[] = []): AST {

        if (this.exactEqualByAlphaConversion(ast, search)) {
            let bounded = false;
            for (const v of scope) {
                if (freevarsinSearch.has(v)) {
                    bounded = true; break;
                }
            }
            if (!bounded) return { type: "var", name: varname };
        }
        if (ast.type === "var") {
            excludedNames.add(ast.name);
            return ast;
        }
        if (ast.nodes?.length === 1) {
            const nast = Core.clone(ast);
            nast.nodes[0] = this.genReplaceFn(nast.nodes[0], search, varname, excludedNames, freevarsinSearch, scope);
            return nast;
        }
        if (ast.nodes?.length === 2) {
            const nast = Core.clone(ast);
            const nscope = scope.slice(0);
            if (ast.type === "L" || ast.type === "P" || ast.type === "W" || ast.type === "S") nscope.push(ast.name);
            nast.nodes[1] = this.genReplaceFn(nast.nodes[1], search, varname, excludedNames, freevarsinSearch, nscope);
            nast.nodes[0] = this.genReplaceFn(nast.nodes[0], search, varname, excludedNames, freevarsinSearch, scope);
            return nast;
        }
        // Keep malformed or future leaf-shaped nodes intact. All parser
        // leaves are currently `var`, but semantic helpers may construct
        // other zero-arity nodes; returning undefined here corrupts the
        // generated rewrite function.
        return ast;
    }
    boundId = 0;
    exactEqualByAlphaConversion(ast1: AST, ast2: AST) {
        if (ast1 === ast2) return true;
        if (ast1.type !== ast2.type) return false;
        if (ast1.type === "var") return ast1.name === ast2.name;
        if (ast1.nodes?.length !== ast2.nodes?.length) return false;
        if (ast1.type === "L" || ast1.type === "P" || ast1.type === "S") {
            const n1 = ast1.name;
            const n2 = ast2.name;
            if (n1 !== n2) {
                ast1 = Core.clone(ast1);
                ast2 = Core.clone(ast2);
                ast1.name = ast2.name = (this.boundId++).toString();
                this.replaceFreeVar(ast1.nodes[1], n1, wrapVar(ast1.name));
                this.replaceFreeVar(ast2.nodes[1], n2, wrapVar(ast1.name));
            }
        }
        if (ast1.nodes?.length) {
            for (let i = 0; i < ast1.nodes.length; i++) {
                if (!this.exactEqualByAlphaConversion(ast1.nodes[i], ast2.nodes[i])) return false;
            }
        }
        return true;
    }
    search(ast: AST, search: AST): boolean {
        if (this.exactEqualByAlphaConversion(ast, search)) {
            return true;
        }
        if (ast.nodes?.length) {
            // exactEqualByAlphaConversion clones only the binder subtrees it
            // needs to rename, so searching the original children is safe and
            // avoids cloning the entire remaining tree on every miss.
            for (let i = ast.nodes.length - 1; i >= 0; i--) {
                if (this.search(ast.nodes[i], search)) return true;
            }
        }
        return false;
    }
    rfl() {
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        let matched = Core.match(goal.type, parser.parse("$1 = $2"), /^\$/);
        if (!matched) matched = Core.match(goal.type, parser.parse("eq $1 $2"), /^\$/);
        if (!matched) matched = Core.match(goal.type, parser.parse("@eq $3 $4 $1 $2"), /^\$/);
        if (!matched) {
            this.goal.unshift(goal);
            throw TR("无法对非相等类型使用该策略");
        }
        try {
            if (!core.checkType({ type: "===", name: "", nodes: [matched["$1"], matched["$2"]] }, goal.context, false)) {
                throw TR("使用rfl策略失败：等式两边无法化简至相等");
            }
        } catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
        const newAst = wrapVar("rfl");
        Core.assign(goal.ast, newAst, true);
        goal.ast.checked = goal.type;
        this.resolveDependGoal(goal.depend);
        return this;
    }
    qed() {
        if (this.goal.length) throw TR("证明尚未完成");
        const term = Core.clone(this.elem);
        const theorem = Core.clone(this.theorem);
        // Keep validation aligned with explicit expansions made in the proof.
        // The user-facing theorem remains unchanged; only this validation copy
        // unfolds aliases such as polymorphic `Join`.
        for (const name of this.expandedDefinitions) {
            core.expandDef(theorem, [], name, [0, 1]);
        }
        // Tactics are checked one goal at a time. A substitution copied from
        // one of those temporary contexts can therefore retain binder ids
        // which do not belong to the completed proof's lexical tree. The
        // serialized proof has no ids, so validate that same representation:
        // discard assistant-internal ids and let Core bind it afresh by scope.
        this.clearBondIds(term);
        this.clearBondIds(theorem);
        core.checkType(
            {
                type: ":",
                name: "",
                nodes: [term, theorem]
            },
            [],
            false,
            undefined,
            false,
            true
        );
    }
    simpl(str?: string) {
        if (str) {
            str = str.trim();
        }
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        const type = goal.context.find(e => e[0] === str)?.[1];
        if (!type && str) {
            this.goal.unshift(goal);
            throw TR("未知的变量：") + str;
        }
        try {
            this.whnf(type ?? goal.type, type ? goal.context.slice(0, goal.context.findIndex(e => e[0] === str)) : goal.context);
        } catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
        this.goal.unshift(goal);
        return this;
    }
    fnext() {
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        let matched: Varlist;
        try {
            const t = goal.type;
            matched = Core.match(t, parser.parse("$2 = $3"), /^\$/) || Core.match(t, parser.parse("eq $2 $3"), /^\$/) || Core.match(t, parser.parse("@eq $0 $1 $2 $3"), /^\$/);
            if (!matched) throw TR("无法对非相等类型使用该策略");
            if (!this.semanticFunctionType(matched["$2"], goal.context)) {
                throw TR("无法对非函数相等类型使用fnext策略");
            }
            this.goal.unshift(goal);
        } catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
        this.apply(wrapApply(wrapVar("fnext")));
    }
    sup() {
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        this.goal.unshift(goal);
        if (goal.type.type !== "W") throw TR("无法对非W类型使用该策略");
        const L = Core.clone(goal.type);
        L.type = "L";
        this.apply2(wrapApply(wrapVar("sup"), L));
    }
    hyp(astr: string) {
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        try {
            let ast = markExplicitAtSyntax(parseAssistInput(astr));
            const ctxtNames = new Set(goal.context.map(e => e[0]));
            let name = Core.getNewName("hyp", ctxtNames);
            if (ast.type === ":" && ast.nodes[0].type === "var") {
                if (ctxtNames.has(ast.nodes[0].name)) throw TR("无法引入重复名称的假设变量");
                name = ast.nodes[0].name;
                ast = ast.nodes[1];
            }
            const targetType = Core.clone(goal.type.nodes?.[1] ?? goal.type);
            const newast = wrapApply({
                type: "L",
                name,
                nodes: [ast, wrapVar("(?#0)")]
            }, wrapVar("(?#0)"));
            Core.assign(goal.ast, newast, true);
            goal.ast.checked = goal.type;
            goal.ast.nodes[0].checked = { type: "->", name: "", nodes: [ast, goal.type] };
            core.checkType(ast, goal.context, false);
            const anotherGoal = {
                ast: goal.ast.nodes[1],
                context: goal.context,
                type: Core.clone(ast),
                depend: goal.depend
            };
            anotherGoal.ast.checked = anotherGoal.type;
            goal.ast = goal.ast.nodes[0].nodes[1];
            goal.type = targetType;
            goal.ast.checked = goal.type;
            goal.context = goal.context.slice(0);
            goal.context.unshift([name, ast, 0]);
            this.goal.unshift(goal);
            goal.depend = null;
            this.goal.unshift(anotherGoal);

        } catch (e) { this.goal.unshift(goal); throw e; }

    }
    private flattenParams(typ: AST, withEnd?: boolean) {
        let params: AST[] = [];
        while (typ.type === "P" || typ.type === "->") {
            params.push(typ.nodes[0]);
            typ = typ.nodes[1];
        }
        if (withEnd) params.push(typ);
        return params;
    }
    private flattenParamNames(typ: AST) {
        let names: string[] = [];
        while (typ.type === "P" || typ.type === "->") {
            names.push(typ.name);
            typ = typ.nodes[1];
        }
        return names;
    }

    private restoreDynamicRecursiveBinderNames(
        names: string[],
        constructor: CoreSystemInductiveMetadata["constructors"][number] | undefined
    ) {
        if (!constructor?.recursiveArguments?.length) return names;
        const recursiveArguments = new Map(
            constructor.recursiveArguments.map(argument => [argument.index, argument] as const)
        );
        let binderIndex = 0;
        for (let argumentIndex = 0;
            argumentIndex < constructor.argumentTypes.length;
            argumentIndex++) {
            binderIndex++;
            if (!recursiveArguments.has(argumentIndex)) continue;
            if (!names[binderIndex]) {
                // Normalization may turn an unused recursive Pi binder into an
                // anonymous arrow; metadata still identifies the IH slot.
                const argumentName = constructor.argumentNames?.[argumentIndex]
                    || `a${argumentIndex}`;
                const generated = /^a(\d+)_(\d+)$/.exec(argumentName);
                names[binderIndex] = generated
                    ? `ih${generated[1]}_${generated[2]}`
                    : `${argumentName}_ih`;
            }
            binderIndex++;
        }
        return names;
    }
    /**
     * Specialize a previously inferred eliminator type without asking the
     * semantic checker to synthesize the whole eliminator application again.
     * A destruct motive contains the current goal, so that application can be
     * much larger than the individual arguments whose types constrain it.
     */
    private specializeKnownFunctionType(typ: AST, args: AST[], context: Context) {
        let result = Core.clone(typ);
        const metas = new Map<string, AST>();
        for (const arg of args) {
            result = this.substituteSemanticMetas(result, metas);
            result = this.reduceBetaSyntax(result);
            if (result.type !== "P" && result.type !== "->") {
                throw TR("归纳器参数数量不匹配");
            }

            const argumentType = core.checkType(Core.clone(arg), context, false);
            this.constrainSemanticMetas(result.nodes[0], argumentType, metas);
            result = this.substituteSemanticMetas(result, metas);

            const body = Core.clone(result.nodes[1]);
            if (result.type === "P") this.replaceFreeVar(body, result.name, arg);
            result = this.reduceBetaSyntax(body);
        }
        return this.substituteSemanticMetas(result, metas);
    }
    private isPrivateSemanticMeta(ast: AST) {
        return ast?.type === "var" && !ast.bondVarId
            && ast.nbeGeneratedMeta === true;
    }
    private substituteSemanticMetas(ast: AST, metas: ReadonlyMap<string, AST>): AST {
        if (this.isPrivateSemanticMeta(ast) && metas.has(ast.name)) {
            return Core.clone(metas.get(ast.name));
        }
        const result: AST = {
            type: ast.type,
            name: ast.name,
            bondVarId: ast.bondVarId,
            displayExplicitAt: ast.displayExplicitAt,
            nbeGeneratedMeta: ast.nbeGeneratedMeta
        };
        if (ast.nodes) result.nodes = ast.nodes.map(node => this.substituteSemanticMetas(node, metas));
        return result;
    }
    private constrainSemanticMetas(expected: AST, actual: AST, metas: Map<string, AST>) {
        const expectedScope: { name: string, id: number }[] = [];
        const actualScope: { name: string, id: number }[] = [];
        const boundDepth = (ast: AST, scope: { name: string, id: number }[]) => {
            for (let index = scope.length - 1; index >= 0; index--) {
                const binding = scope[index];
                if (ast.bondVarId && binding.id === ast.bondVarId
                    || !ast.bondVarId && binding.name === ast.name) return scope.length - index;
            }
            return 0;
        };
        const visit = (left: AST, right: AST) => {
            left = this.substituteSemanticMetas(left, metas);
            if (this.isPrivateSemanticMeta(left)) {
                metas.set(left.name, Core.clone(right));
                return;
            }
            if (!left || !right || left.type !== right.type) return;
            if (left.type === "var") {
                const leftDepth = boundDepth(left, expectedScope);
                const rightDepth = boundDepth(right, actualScope);
                if (leftDepth || rightDepth) return;
                return;
            }
            if (left.type === "L" || left.type === "P" || left.type === "S" || left.type === "W") {
                visit(left.nodes[0], right.nodes[0]);
                expectedScope.push({ name: left.name, id: left.bondVarId });
                actualScope.push({ name: right.name, id: right.bondVarId });
                visit(left.nodes[1], right.nodes[1]);
                expectedScope.pop();
                actualScope.pop();
                return;
            }
            for (let index = 0; index < (left.nodes?.length ?? 0); index++) {
                if (right.nodes?.[index]) visit(left.nodes[index], right.nodes[index]);
            }
        };
        visit(expected, actual);
    }
    private reduceBetaSyntax(ast: AST): AST {
        if (!ast.nodes?.length) return Core.clone(ast);
        const nodes = ast.nodes.map(node => this.reduceBetaSyntax(node));
        if (ast.type === "apply" && nodes[0]?.type === "L") {
            const body = Core.clone(nodes[0].nodes[1]);
            this.replaceFreeVar(body, nodes[0].name, nodes[1]);
            return this.reduceBetaSyntax(body);
        }
        return {
            type: ast.type,
            name: ast.name,
            nodes,
            bondVarId: ast.bondVarId,
            displayExplicitAt: ast.displayExplicitAt,
            nbeGeneratedMeta: ast.nbeGeneratedMeta
        };
    }
    /** Lean-style induction entry point.  `with` names the inductive-step
     * data and induction-hypothesis bindings, e.g. `induction n with d dh`.
     * The existing destruct implementation remains the shared eliminator. */
    induction(spec: string) {
        const value = spec?.trim() ?? "";
        const match = /^([^\s]+)(?:\s+with\s+([\s\S]+))?$/.exec(value);
        if (!match) throw TR("induction语法应为 induction 变量 [with 名称...]");
        const names = match[2]
            ? match[2].split(/[\s,]+/).filter(Boolean)
            : [];
        if (names.some(name => !/^[^\s,]+$/.test(name))) {
            throw TR("induction分支名称无效");
        }
        return this.destruct(match[1], names);
    }

    private renameInductionBinding(goal: Goal, branchRoot: AST, source: string, destination: string) {
        if (!source || source === destination) return;
        if (goal.context.some(([name]) => name === destination)) {
            throw TR("induction分支名称已存在：" + destination);
        }
        const replacement = wrapVar(destination);
        let branch = branchRoot;
        let renamedBinder = false;
        while (branch?.type === "L" && branch.nodes?.[1]) {
            if (branch.name === source) {
                this.replaceFreeVar(branch.nodes[1], source, replacement);
                branch.name = destination;
                renamedBinder = true;
                break;
            }
            branch = branch.nodes[1];
        }
        if (!renamedBinder) throw TR("无法重命名归纳分支变量：" + source);
        for (const entry of goal.context) {
            if (entry[0] === source) entry[0] = destination;
            this.replaceFreeVar(entry[1], source, replacement);
        }
        this.replaceFreeVar(goal.type, source, replacement);
        this.replaceFreeVar(goal.ast, source, replacement);
        goal.ast.checked = goal.type;
    }

    private renameInductionBindings(goal: Goal, branchRoot: AST,
        introducedNames: string[], names: string[]) {
        if (introducedNames.length !== names.length) return;
        for (let index = 0; index < names.length; index++) {
            this.renameInductionBinding(goal, branchRoot, introducedNames[index], names[index]);
        }
    }

    destruct(n: string, inductionNames: string[] = []) {
        n = n.trim();
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        const nast = { type: "var", name: n };
        let nType: AST;
        // A local variable's type is already recorded in the goal context.
        // Re-synthesizing the variable as an ordinary term can desugar a
        // surface Sum (for example `True+True`) into `@Sum _ _ ...`; the
        // annotated semantic path then rejects those implicit holes even
        // though the context binding was checked when it was introduced.
        // Read the nearest binding directly and only fall back to synthesis
        // for malformed/legacy contexts that do not carry a type.
        const binding = findContextByName(goal.context, n);
        if (binding?.[1]) {
            nType = Core.clone(binding[1]);
        } else {
            try { nType = core.checkType(nast, goal.context, false); } catch (e) {
                this.goal.unshift(goal); throw e;
            }
        }
        if (!this.isIndType(nType)) { this.goal.unshift(goal); throw TR("只能解构解锁的归纳类型的变量"); }
        const dynamicInductive = this.getDynamicInductiveMetadata(nType);

        const excludedSet = new Set(goal.context.map(e => e[0]));
        Core.getFreeVars(goal.type, excludedSet);


        const isEqType = nType.nodes?.[0]?.nodes?.[0]?.name === "eq" || nType.type === "=";
        const isPushoutType = nType.type === "apply"
            && nType.nodes?.[0]?.nodes?.[0]?.nodes?.[0]?.name === "Pushout";
        let indFnName = dynamicInductive?.eliminatorName
            ?? "ind_" + ((nType.nodes?.[0]?.name === "Sus" || nType.nodes?.[0]?.name === "List" || nType.nodes?.[0]?.name === "Option" || nType.nodes?.[0]?.name === "Even") ? nType.nodes[0].name : isEqType ? "eq" : nType.type === "+" ? "Sum" : nType.type === "X" ? "Prod" : nType.type === "[[]]" ? "Trunc" : nType.type === "S" ? "Prod" : nType.type === "W" ? "W" : isPushoutType ? "Pushout" : nType.name);
        // x in x=y, just parameter for types 

        // nType.nodes?.[0]?.name === "Sus" ? [nType.nodes[1]] :
        const fixedEqEndpoint = nType.nodes?.[0]?.nodes?.[0]?.name === "eq"
            ? nType.nodes[0].nodes[1]
            : nType.type === "=" ? nType.nodes[0] : null;
        let typeParams = dynamicInductive
            ? dynamicInductive.uniformArguments.map(argument => Core.clone(argument))
            : isEqType ? [fixedEqEndpoint]
                : nType.type === "X" ? [wrapLambda("L", Core.getNewName("x", excludedSet), nType.nodes[0], nType.nodes[1])]
                    : nType.type === "S" || nType.type === "W" ? [wrapLambda("L", nType.name, nType.nodes[0], nType.nodes[1])]
                        : [];
        if (isPushoutType) {
            const pushoutArgs = core.flattenApplyList(nType).slice(1);
            const [pushoutC, pushoutF, pushoutG] = pushoutArgs;
            let pushoutA = pushoutC?.type === "X" ? pushoutC.nodes[0] : null;
            let pushoutB = pushoutC?.type === "X" ? pushoutC.nodes[1] : null;
            if (!pushoutA || !pushoutB) {
                try {
                    const fType = core.checkType(Core.clone(pushoutF), goal.context, false);
                    const gType = core.checkType(Core.clone(pushoutG), goal.context, false);
                    pushoutA = fType.nodes?.[1];
                    pushoutB = gType.nodes?.[1];
                } catch { }
            }
            if (pushoutA && pushoutB && pushoutC && pushoutF && pushoutG) {
                const universeLevel = (term: AST) => {
                    try {
                        const termType = core.checkType(Core.clone(term), goal.context, false);
                        if (termType.type === "apply" && termType.nodes?.[0]?.name === "U") {
                            return Core.clone(termType.nodes[1]);
                        }
                    } catch { }
                    return wrapVar("@0");
                };
                // The public ind_Pushout alias leaves c/f/g and their endpoint
                // types as semantic metas. Supply the full eliminator prefix
                // so branch types do not retain ?nbe variables.
                indFnName = "@ind_Pushout";
                typeParams = [
                    universeLevel(pushoutA),
                    universeLevel(goal.type),
                    Core.clone(pushoutA),
                    Core.clone(pushoutB),
                    Core.clone(pushoutC),
                    Core.clone(pushoutF),
                    Core.clone(pushoutG)
                ];
            }
        }
        // y in x=y: induction on this group of types
        const groupParam = (isEqType || nType.nodes?.[0]?.name === "Even") ? nType.nodes[1] : null;
        const selfLoopEq = isEqType && this.exactEqualByAlphaConversion(fixedEqEndpoint, groupParam);

        // destruct with other variables in context as condition added in target C
        const conds = [];
        if (!Assist.disableDestructConds) {
            for (const [k, v, id] of goal.context) {
                if (k === n) continue;
                if (Core.getFreeVars(v).has(n) || (groupParam && this.search(v, groupParam))) {
                    conds.push([k, v, id]);
                }
            }
        }
        const condsNames = conds.map(e => e[0]);
        let goalWithConds = Core.clone(goal.type);

        for (const [k, v, id] of conds) {
            goalWithConds = wrapLambda("P", k, v, goalWithConds);
        }

        if (dynamicInductive?.fullEliminatorName) {
            const motiveUniverse = this.universeLevelForType(goalWithConds, goal.context);
            if (motiveUniverse && !(motiveUniverse.type === "var" && motiveUniverse.name === "@0")) {
                indFnName = dynamicInductive.fullEliminatorName;
                typeParams = [
                    motiveUniverse,
                    ...dynamicInductive.uniformArguments.map(argument => Core.clone(argument))
                ];
            }
        }


        let C = wrapLambda("L", n, nType, goalWithConds);
        if (dynamicInductive?.indexArguments.length) {
            for (let index = dynamicInductive.indexArguments.length - 1; index >= 0; index--) {
                const indexArgument = dynamicInductive.indexArguments[index];
                const indexType = core.checkType(Core.clone(indexArgument), goal.context, false);
                const indexName = Core.getNewName(
                    dynamicInductive.indices[index]?.name || `i${index}`,
                    excludedSet
                );
                excludedSet.add(indexName);
                C = wrapLambda("L", indexName, indexType, Core.clone(C, true));
                C.nodes[1] = this.genReplaceFn(
                    C.nodes[1],
                    indexArgument,
                    indexName,
                    excludedSet
                );
            }
        }
        if (groupParam) {
            const eqType = core.checkType(groupParam, goal.context, false);
            const newY = Core.getNewName(groupParam.type === "var" ? groupParam.name : indFnName === "ind_Even" ? "n" : "y", excludedSet);
            C = wrapLambda("L", newY, eqType, Core.clone(C, true));
            if (selfLoopEq) {
                // For p : x=x, path induction keeps the left endpoint fixed and
                // varies only the right endpoint. Replacing every occurrence of
                // x would incorrectly produce p : y=y and an invalid motive.
                C.nodes[1].nodes[0].nodes[1] = wrapVar(newY);
            } else {
                C.nodes[1] = this.genReplaceFn(C.nodes[1], groupParam, newY, excludedSet);
            }
        }
        const indFn = wrapVar(indFnName);
        const indFnHead = wrapApply(indFn, ...typeParams.map(e => Core.clone(e)), Core.clone(C));
        // Goal snapshots are checked against cloned contexts, so their bound
        // variable ids do not belong to the live assistant context. Rebind the
        // whole eliminator application before NbE substitutes the motive.
        this.clearBondIds(indFnHead);
        let headType: AST;
        let indFnType: AST;
        try {
            if (selfLoopEq) {
                try {
                    core.withSilentErrors(() =>
                        core.checkType(Core.clone(indFnHead), goal.context, false)
                    );
                } catch {
                    throw TR("无法构造合法的等式归纳目标");
                }
            }
            // Semantic synthesis returns the application's type without
            // annotating every child node. Read the eliminator type directly
            // instead of relying on indFn.checked being populated as a side effect.
            indFnType = core.checkType(Core.clone(indFn), goal.context, false);
            const indFnArgs = core.flattenApplyList(indFnHead).slice(1);
            headType = this.specializeKnownFunctionType(indFnType, indFnArgs, goal.context);
        } catch (e) {
            this.goal.unshift(goal);
            throw e;
        }

        const indFnParams = this.flattenParams(indFnType);
        const indFnParamNames = this.flattenParamNames(indFnType);
        // holes includes ctor holes and also grpara / tail: x->C x
        const holes = this.flattenParams(headType);
        // grpara is group param
        // ind_xxx :param->C->(C grpara? ctor1)->(C grpara? ctor2)->...->grpara->x:xxx->(C grpara xxx)
        const inferredBranchCount = indFnParams.length
            - typeParams.length
            - 1
            - (dynamicInductive?.indexArguments.length ?? 0)
            - (groupParam ? 1 : 0)
            - 1;
        // Ordinary inductive metadata lists exactly the branch-producing point
        // constructors. A first-order HIT additionally carries one eliminator
        // coherence argument per path constructor; those are proof goals too,
        // but must never be exposed as data constructors by `constructor` or
        // its recommendations above. Keep the arity-derived count as the
        // compatibility path for legacy and built-in eliminators.
        const metadataBranchCount = dynamicInductive?.kind === "hit1"
            || dynamicInductive?.kind === "hit2"
            || dynamicInductive?.kind === "hit3"
            ? dynamicInductive.constructors.length
                + hitPathConstructorCount(
                    hitPathLevelsFromCanonicalOrLegacy(
                        dynamicInductive as CoreSystemInductiveMetadata
                    )
                )
            : undefined;
        const ctorNumbers = metadataBranchCount ?? inferredBranchCount;
        if (ctorNumbers < 0 || holes.length < ctorNumbers) {
            this.goal.unshift(goal);
            throw TR("归纳消去器分支元数据与类型不一致");
        }
        const indFnBody = [];
        const newGoals: Goal[] = [];
        const introNums: string[][] = [];
        const ctorOffset = typeParams.length + 1;
        const dependence: number[][] = [];
        for (let i = 0; i < ctorNumbers; i++) {
            const gtype = holes[i];
            const gast = wrapVar("(?#0)");
            const ctx = Core.cloneContext(goal.context).filter(e => e[0] !== n && !condsNames.includes(e[0]));
            gast.checked = gtype;
            const indFnParamType = indFnParams[i + ctorOffset];
            const indFnParamName = indFnParamNames[i + ctorOffset];
            const indexedHitConstructor = dynamicInductive?.kind === "hit1"
                && dynamicInductive.indexArguments.length
                ? dynamicInductive.constructors[i]
                : undefined;
            const holeParams = this.restoreDynamicRecursiveBinderNames(
                this.flattenParamNames(indFnParamType),
                indexedHitConstructor
            );
            holeParams.push(...condsNames);
            introNums.push(holeParams);
            // mark depend
            const depend = [];
            if (indFnParamName) {
                for (let j = i; j < ctorNumbers; j++) {
                    if (j === i) continue;
                    if (Core.getFreeVars(indFnParams[j + ctorOffset]).has(indFnParamName)) {
                        depend.push(j);
                    }
                }
            }
            dependence.push(depend);
            newGoals.push({ context: ctx, ast: gast, type: gtype, depend: null });
            indFnBody.push(gast);
        }
        // record dependences in goals
        for (let i = 0; i < ctorNumbers; i++) {
            const d = dependence[i];
            if (!d.length) continue;
            const goals = d.map(j => newGoals[j]);
            const varname = this.getNewDependGoalVarName();
            newGoals[i].depend = {
                src: newGoals[i].ast, dst: goal.ast, goals, varname
            };
            const srcname = indFnParamNames[i + ctorOffset];
            for (const g of goals) {
                this.replaceFreeVar(g.type, srcname, wrapVar(varname));
            }
        }
        if (groupParam) indFnBody.push(groupParam);
        if (dynamicInductive?.indexArguments.length) {
            indFnBody.push(...dynamicInductive.indexArguments.map(argument => Core.clone(argument)));
        }
        conds.reverse();
        Core.assign(goal.ast, wrapApply(indFnHead, ...indFnBody, nast, ...conds.map(e => {
            const k = wrapVar(e[0]); k.checked = e[1]; return k;
        })), true);
        let k = 0;
        for (const g of newGoals) {
            this.goal.unshift(g);
            const intros = introNums[k++];
            const branchRoot = g.ast;
            const introducedNames: string[] = [];
            intros.forEach(e => {
                this.intro((n + "_" + e).replaceAll("_x", ""));
                introducedNames.push(g.context[0][0]);
            });
            if (inductionNames.length) {
                this.renameInductionBindings(g, branchRoot, introducedNames, inductionNames);
            }
            this.goal.shift();
        }
        if (!newGoals.length) {
            this.resolveDependGoal(goal.depend);
            return;
        }
        newGoals[newGoals.length - 1].depend = goal.depend;
        this.goal.unshift(...newGoals);
        return this;
    }
    getNewDependGoalVarName() {
        return "(%" + (this.dependVarId++) + ")";
    }
    ex(n: string) {
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        if (goal.type.type !== "S") throw TR("ex策略只能作用于依赖积类型");
        const dfn = Core.clone(goal.type); dfn.type = "L";
        n = n?.trim();
        if (n?.startsWith("?") || n === "_") n = null;
        try {
            let val = n ? markExplicitAtSyntax(parseAssistInput(n)) : wrapVar("(?#0)");
            // Instantiate the primitive constructor with the dependent
            // family explicitly.  The surface `pair` alias leaves its
            // universe/family parameters to NBE inference; with an indexed
            // witness that can create two incompatible constraints for the
            // same metavariable in the second component.
            Core.assign(goal.ast, wrapApply(
                wrapVar("@pair"),
                wrapVar("_"),
                wrapVar("_"),
                Core.clone(dfn.nodes[0]),
                dfn,
                val,
                wrapVar("(?#0)")
            ), true);
            goal.ast.checked = goal.type;
            if (n) {
                core.checkType(goal.ast.nodes[0], goal.context, false);
            } else {
                const newGoal: Goal = {
                    ast: goal.ast.nodes[0].nodes[1],
                    type: dfn.nodes[0],
                    context: Core.cloneContext(goal.context),
                    depend: {
                        src: goal.ast.nodes[0].nodes[1],
                        dst: goal.ast.nodes[1],
                        goals: [goal],
                        varname: this.getNewDependGoalVarName()
                    }
                };
                val = wrapVar(newGoal.depend.varname);
                this.goal.unshift(newGoal, goal);
            }
            goal.ast = goal.ast.nodes[1];
            goal.type = Core.clone(dfn.nodes[1]);
            this.replaceFreeVar(goal.type, dfn.name, val);
            if (n) {
                core.checkType(goal.type, goal.context, false);
                this.goal.unshift(goal);
            }

        } catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
    }
    left() {
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        if (goal.type.type === "apply" && goal.type.nodes?.[0]?.nodes?.[0]?.nodes?.[0]?.name === "Pushout") {
            this.goal.unshift(goal);
            return this.apply(wrapApply(wrapVar("pol"), goal.type.nodes[0].nodes[0].nodes[1], goal.type.nodes[0].nodes[1], goal.type.nodes[1]));
        }
        if (goal.type.type !== "+") throw TR("left策略只能作用于和类型");
        Core.assign(goal.ast, wrapApply(wrapVar("inl"), wrapVar("(?#0)")), true);
        goal.ast.checked = goal.type;
        goal.ast.nodes[0].checked = wrapLambda("->", "", goal.type.nodes[0], goal.type);
        goal.ast = goal.ast.nodes[1];
        goal.type = goal.type.nodes[0];
        goal.ast.checked = goal.type;
        this.goal.unshift(goal);
    }
    right() {
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        if (goal.type.type === "apply" && goal.type.nodes?.[0]?.nodes?.[0]?.nodes?.[0]?.name === "Pushout") {
            this.goal.unshift(goal);
            return this.apply(wrapApply(wrapVar("por"), goal.type.nodes[0].nodes[0].nodes[1], goal.type.nodes[0].nodes[1], goal.type.nodes[1]));
        }
        if (goal.type.type !== "+") throw TR("right策略只能作用于和类型");
        Core.assign(goal.ast, wrapApply(wrapVar("inr"), wrapVar("(?#0)")), true);
        goal.ast.checked = goal.type;
        goal.ast.nodes[0].checked = wrapLambda("->", "", goal.type.nodes[1], goal.type);
        goal.ast = goal.ast.nodes[1];
        goal.type = goal.type.nodes[1];
        goal.ast.checked = goal.type;
        this.goal.unshift(goal);
    }
    case() {
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        if (goal.type.type !== "X") throw TR("case策略只能作用于积类型");
        // `X` is the surface product notation for a Sigma with a constant
        // family.  Use the primitive constructor with that family made
        // explicit; the shorthand `pair` alias leaves the family to NBE
        // inference and is ambiguous in dependent branches.
        const family = wrapLambda(
            "L",
            "_",
            Core.clone(goal.type.nodes[0]),
            Core.clone(goal.type.nodes[1])
        );
        Core.assign(goal.ast, wrapApply(
            wrapVar("@pair"),
            wrapVar("_"),
            wrapVar("_"),
            Core.clone(goal.type.nodes[0]),
            family,
            wrapVar("(?#0)"),
            wrapVar("(?#0)")
        ), true);
        const firstComponentHole = goal.ast.nodes[0].nodes[1];
        const secondComponentHole = goal.ast.nodes[1];
        const anotherGoal: Goal = {
            ast: secondComponentHole,
            context: goal.context.slice(0),
            type: goal.type.nodes[1],
            depend: goal.depend
        };
        anotherGoal.ast.checked = anotherGoal.type;
        goal.ast.checked = goal.type;
        goal.ast = firstComponentHole;
        goal.type = goal.type.nodes[0];
        goal.ast.checked = goal.type;
        goal.depend = null;
        this.goal.unshift(anotherGoal);
        this.goal.unshift(goal);
    }
    expand(n: string) {
        n = n?.trim();
        if (!n) throw TR("意外的空表达式");
        const k = n.split(" ");
        if (k.length === 1) k.unshift("0");
        const pos = Number(k.shift());
        n = k.join(" ");
        if (Math.round(pos) !== pos) throw TR("未找到任何指定展开的项");
        const goal = this.goal.shift();
        if (!goal) throw TR("无证明目标，请使用qed命令结束证明");
        let requiresStrictSimplification = false;
        try {
            // The goal AST may have been checked in an earlier assistant
            // snapshot.  Its bond ids belong to that check's context and are
            // stale after dependent goals are rewritten; reusing them causes
            // false "Bound Var Leakage" diagnostics during expansion.
            const freshGoal = core.desugar(Core.clone(goal.type), false);
            this.clearBondIds(freshGoal);
            goal.type = core.markBondVars(freshGoal, goal.context);
            if (!core.expandDef(goal.type, goal.context, n, [pos, 1])) {
                this.goal.unshift(goal);
                throw TR("未找到任何指定展开的项");
            };
            if (core.opaque.find(e => e[0] === n) && core.state.sysDefs["@" + n]) {
                core.expandDef(goal.type, goal.context, "@" + n, [0, 1])
            }
            // Expansion can instantiate a lambda definition (for example
            // `isProp`), but the selected definition is still the only named
            // constant that should be unfolded. Reduce the newly introduced
            // beta redexes syntactically so the surrounding `not (...)` (or
            // any other user-facing wrapper) remains opaque and readable.
            Core.assign(goal.type, this.reduceBetaSyntax(goal.type), true);
            const expandedDefinition = core.state.sysDefs[n] || core.state.userDefs[n];
            const explicitDefinition = core.opaque.find(e => e[0] === n)
                ? core.state.sysDefs["@" + n]
                : undefined;
            const expansionHasHoles = [expandedDefinition, explicitDefinition]
                .some(definition => definition && this.containsInferenceHole(definition));
            if (expandedDefinition && core.hasDefinitionCache(n) && !expansionHasHoles) {
                core.normalizeExpandedProofGoal(goal.type, goal.context);
            } else {
                // Type checking may desugar and beta-reduce the complete AST.
                // Validate a clone so an explicit `expand name` does not also
                // rewrite unrelated surface syntax such as `not (...)`.
                core.checkType(
                    Core.clone(goal.type),
                    goal.context,
                    false,
                    undefined,
                    false,
                    true,
                    false
                );
                requiresStrictSimplification = true;
            }
        } catch (e) {
            this.goal.unshift(goal);
            throw e;
        }
        this.goal.unshift(goal);
        if (requiresStrictSimplification) {
            // The generic simpl tactic routes through a WHNF request. An
            // expanded eqv goal can still contain a freshly desugared Sum
            // argument, which that route rejects even though the expanded
            // goal itself has already passed type checking. Normalize the
            // local expansion directly instead.
            core.normalizeExpandedProofGoal(goal.type, goal.context);
        }
        this.expandedDefinitions.add(n);
        return this;
    }
    private replaceFreeVar(ast: AST, src: string, dst: AST, freevarInDst: Set<string> = Core.getFreeVars(dst)) {
        if (ast.type === "var") {
            if (ast.name === src) {
                Core.assign(ast, dst, true);
            }
        } else if (ast.type === "L" || ast.type === "P" || ast.type === "W" || ast.type === "S") {
            if (freevarInDst.has(ast.name)) {
                // alpha conversion
                const exset = Core.getFreeVars(ast.nodes[1]);
                const nn = Core.getNewName(Core.getNewName(ast.name, freevarInDst), exset);
                this.replaceFreeVar(ast.nodes[1], ast.name, wrapVar(nn));
                ast.name = nn;
            }
            this.replaceFreeVar(ast.nodes[0], src, dst, freevarInDst);
            if (ast.name !== src) {
                this.replaceFreeVar(ast.nodes[1], src, dst, freevarInDst);
            }
        } else if (ast.nodes?.length) {
            for (const child of ast.nodes) {
                this.replaceFreeVar(child, src, dst, freevarInDst);
            }
        }
    }
    // private replaceVar(ast: AST, varname: string, dst: AST, context: Context = []) {
    //     Core.assign(ast, this.whnf(wrapApply(wrapLambda("L", varname, wrapVar("_"), Core.clone(ast)), Core.clone(dst)), context), true);
    // }
    private whnf(ast: AST, context: Context) {
        return core.checkType({ type: "whnf", nodes: [ast, wrapVar("_")], name: "" }, context, true);
    }
    private semanticSimplification(ast: AST, context: Context) {
        const source = Core.clone(ast);
        try {
            core.checkType(
                source,
                context,
                false,
                undefined,
                true,
                true,
                false
            );
            const normalized = Core.clone(source);
            core.checkType(
                { type: "whnf", nodes: [normalized, wrapVar("_")], name: "" },
                context,
                true,
                undefined,
                false,
                true,
                false
            );
            return { source, normalized };
        } catch {
            return null;
        }
    }
    private semanticFunctionType(ast: AST, context: Context) {
        const candidate = Core.clone(ast);
        let type: AST;
        try {
            type = core.checkType(
                candidate,
                context,
                false,
                undefined,
                true,
                true
            );
            if (type.type !== "P" && type.type !== "->") {
                type = Core.clone(type);
                core.checkType(
                    { type: "whnf", nodes: [type, wrapVar("_")], name: "" },
                    context,
                    true,
                    undefined,
                    false,
                    true
                );
            }
        } catch {
            return null;
        }
        return type.type === "P" || type.type === "->" ? type : null;
    }
}
