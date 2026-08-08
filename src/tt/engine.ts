import { AST, ASTParser } from "./astparser.js";
import { Context, Core, DefinitionTypeCacheSnapshot } from "./core.js";
import { initTypeSystem } from "./initial.js";
import { langMgr, TR } from "../lang.js";

const parser = new ASTParser();

export type TTCoreConfig = {
    unlockedTypes: string[];
    disableSimpleFn?: boolean;
    disableSimpleEq?: boolean;
    inferDisplayMode?: "_" | "@";
    timeout?: number;
    language?: string;
    /** Definitions must already be desugared, as TTGui.userDefinedConsts stores them. */
    userDefinitions?: [string, AST][];
    /** Inference state needed to instantiate generalized types of prior user definitions. */
    userDefinitionCaches?: [string, DefinitionTypeCacheSnapshot][];
};

export type TTCoreCheckResult = {
    ok: boolean;
    ast?: AST;
    type?: AST;
    error?: string;
    timeout: boolean;
    durationMs: number;
    /** Present for := declarations after Core.registConstType has filled inference holes. */
    filledDefinition?: AST;
    /** Transferable cache needed to preserve generalized inference variables on the UI Core. */
    definitionCache?: DefinitionTypeCacheSnapshot;
};

/**
 * DOM-free owner for a configured type-theory Core. This is shared by the
 * worker entry point and any future non-visual callers.
 */
export class TTCoreEngine {
    core = new Core();
    private readonly rules = initTypeSystem();

    configure(config: TTCoreConfig) {
        langMgr.lang = config.language ?? langMgr.lang;
        this.core = new Core();
        Core.timeout = config.timeout ?? Core.timeout;
        Core.timeoutOccured = false;
        this.registerComputeRules();

        const terms = new Set(config.unlockedTypes);
        const inferDisplayMode = config.inferDisplayMode ?? "_";
        const disableSimpleFn = !!config.disableSimpleFn;
        const disableSimpleEq = !!config.disableSimpleEq;

        this.core.state.eagerInferRel = true;
        for (const rule of this.rules) {
            const vname = rule.ast.nodes?.[0]?.name;
            if (!terms.has(rule.id)) continue;

            this.core.state.disableSimpleEq = false;
            this.core.state.disableSimpleFn = false;
            if (rule.ast.type === ":" && rule.ast.nodes[0].type === "var") {
                if (terms.has("// " + vname)) delete this.core.state.sysTypes[vname];
                else this.core.state.sysTypes[vname] = this.core.desugar(Core.clone(rule.ast.nodes[1]), true);
            }
            if (rule.ast.type === ":=" && rule.ast.nodes[0].type === "var") {
                const value = rule.ast.nodes[1].type === ":" ? rule.ast.nodes[1].nodes[0] : rule.ast.nodes[1];
                if (terms.has("// " + vname)) delete this.core.state.sysDefs[vname];
                else this.core.state.sysDefs[vname] = this.core.desugar(Core.clone(value), true);
            }
            if (terms.has("// " + vname)) {
                delete this.core.state.defTypes[vname];
                continue;
            }

            // This mirrors TTGui.updateTypeList. The display mode controls
            // which of the paired inferred/original declarations is active.
            if ((rule.inferMode === "@" && inferDisplayMode === "_") || (rule.inferMode === "_" && inferDisplayMode === "@")) {
                if (rule.ast.type === ":=") {
                    if (rule.ast.nodes[1].type === ":") {
                        this.core.state.sysTypes[vname] = this.core.desugar(Core.clone(rule.ast.nodes[1].nodes[1]), true);
                    } else {
                        try { this.core.registConstType(vname, rule.ast.nodes[1]); } catch { }
                    }
                }
                continue;
            }

            if (rule.ast.type === ":=") {
                const value = rule.ast.nodes[1].type === ":" ? rule.ast.nodes[1].nodes[0] : rule.ast.nodes[1];
                if (rule.ast.nodes[1].type === ":") {
                    this.core.state.sysTypes[vname] = this.core.desugar(Core.clone(rule.ast.nodes[1].nodes[1]), true);
                } else {
                    try { this.core.registConstType(vname, value); } catch { }
                }
            }
        }
        this.core.state.eagerInferRel = false;

        this.core.state.disableSimpleFn = disableSimpleFn;
        this.core.state.disableSimpleEq = disableSimpleEq;
        this.core.state.userDefs = {};
        for (const [name, definition] of config.userDefinitions ?? []) {
            this.core.state.userDefs[name] = Core.clone(definition);
        }
        for (const [name, cache] of config.userDefinitionCaches ?? []) {
            if (this.core.state.userDefs[name]) this.core.restoreDefinitionCache(name, cache);
        }
    }

    check(input: string, context: Context = []): TTCoreCheckResult {
        return this.checkAst(parser.parse(input), context);
    }

    checkAst(ast: AST, context: Context = []): TTCoreCheckResult {
        const started = performance.now();
        Core.timeoutOccured = false;
        try {
            if (!ast) throw new Error(TR("空表达式"));
            const type = this.core.checkType(ast, context, false);
            return { ok: true, ast, type, timeout: !!Core.timeoutOccured, durationMs: performance.now() - started };
        } catch (error) {
            return {
                ok: false,
                ast,
                error: String(error),
                timeout: !!Core.timeoutOccured,
                durationMs: performance.now() - started
            };
        }
    }

    /** Validate a declaration and return the inferred declaration used by TTGui's definition cache. */
    registerDefinition(ast: AST, context: Context = []): TTCoreCheckResult {
        const started = performance.now();
        Core.timeoutOccured = false;
        try {
            if (ast?.type !== ":=" || ast.nodes?.[0]?.type !== "var") {
                throw new Error(TR("只能注册具名定义"));
            }
            this.core.checkType(ast, context, false);
            const filledDefinition = this.core.registConstType(ast.nodes[0].name, ast.nodes[1]);
            const definitionCache = this.core.serializeDefinitionCache(ast.nodes[0].name);
            return {
                ok: true,
                ast,
                type: ast.checked,
                filledDefinition,
                definitionCache,
                timeout: !!Core.timeoutOccured,
                durationMs: performance.now() - started
            };
        } catch (error) {
            return {
                ok: false,
                ast,
                error: String(error),
                timeout: !!Core.timeoutOccured,
                durationMs: performance.now() - started
            };
        }
    }

    private registerComputeRules() {
        const expand: { [name: string]: AST[] } = {};
        for (const rule of this.rules) {
            if (rule.ast.type === ":=" && rule.ast.nodes[0].type === "var") {
                let sub = rule.ast.nodes[1];
                const applyList: AST[] = [];
                let isInfer = true;
                while (sub.type === "apply") {
                    applyList.unshift(sub.nodes[1]);
                    if (sub.nodes[1].type !== "var" || sub.nodes[1].name !== "_") isInfer = false;
                    sub = sub.nodes[0];
                }
                applyList.unshift(sub);
                if (sub.name[0] === "@" && isInfer) this.core.opaque.push([rule.ast.nodes[0].name, applyList.length]);
                expand[rule.ast.nodes[0].name] = applyList;
            }
            if (rule.postfix !== "计算" || rule.ast.type !== "===" || rule.id === "Function") continue;

            const applyList: AST[] = [];
            let sub = rule.ast.nodes[0];
            while (sub.type === "apply") {
                applyList.unshift(sub.nodes[1]);
                sub = sub.nodes[0];
            }
            applyList.unshift(sub);
            const result = this.core.desugar(Core.clone(rule.ast.nodes[1]), true);
            this.core.state.computeRules[sub.name] ??= [];
            this.core.state.computeRules[sub.name].push({ pattern: applyList, result });

            const expanded = sub.type === "var" ? expand[sub.name] : undefined;
            if (expanded) {
                const expandedPattern = applyList.slice(1);
                expandedPattern.unshift(...expanded);
                this.core.state.computeRules[expanded[0].name] ??= [];
                this.core.state.computeRules[expanded[0].name].push({ pattern: expandedPattern, result });
            }
        }
    }
}
