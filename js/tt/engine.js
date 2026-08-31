import { ASTParser } from "./astparser.js";
import { Core } from "./core.js";
import { initTypeSystem } from "./initial.js";
import { langMgr, TR } from "../lang.js";
import { markExplicitAtSyntax, restoreSemanticMetaNamesForDisplay } from "./presentation.js";
import { theoremInferenceComplete } from "./theorem-validation.js";
const parser = new ASTParser();
/**
 * Install the creative sandbox projection without reordering declarations by
 * category. Older callers without an explicit order retain the legacy
 * axioms/inductives/definitions sequence.
 */
export function installTrustedDeclarations(core, config) {
    const axioms = config.trustedAxioms ?? [];
    const inductives = config.trustedInductives ?? [];
    const definitions = config.trustedDefinitions ?? [];
    const axiomByName = new Map(axioms);
    const inductiveByName = new Map(inductives.map(bundle => [bundle.type[0], bundle]));
    const definitionByName = new Map(definitions);
    const allEntries = [
        ...axioms.map(([name]) => ({ kind: "axiom", name })),
        ...inductives.map(bundle => ({ kind: "inductive", name: bundle.type[0] })),
        ...definitions.map(([name]) => ({ kind: "definition", name }))
    ];
    const allNames = new Set(allEntries.map(entry => entry.name));
    const expectedKeys = new Set(allEntries.map(entry => `${entry.kind}:${entry.name}`));
    if (allNames.size !== allEntries.length || expectedKeys.size !== allEntries.length) {
        throw new Error("沙盒 bridge 包含重复声明名称");
    }
    let ordered = allEntries;
    if (config.trustedDeclarationOrder !== undefined) {
        const seen = new Set();
        ordered = config.trustedDeclarationOrder.map(entry => {
            const key = `${entry?.kind}:${entry?.name}`;
            if (!entry || !expectedKeys.has(key)) {
                throw new Error(`沙盒 bridge 顺序包含未知声明：${entry?.name ?? ""}`);
            }
            if (seen.has(key)) {
                throw new Error(`沙盒 bridge 顺序包含重复声明：${entry.name}`);
            }
            seen.add(key);
            return { kind: entry.kind, name: entry.name };
        });
        if (seen.size !== expectedKeys.size) {
            const missing = allEntries.find(entry => !seen.has(`${entry.kind}:${entry.name}`));
            throw new Error(`沙盒 bridge 顺序缺少声明：${missing?.name ?? ""}`);
        }
    }
    try {
        for (const entry of ordered) {
            if (entry.kind === "axiom") {
                const type = axiomByName.get(entry.name);
                if (type)
                    core.setSystemType(entry.name, core.desugar(Core.clone(type), true));
                continue;
            }
            if (entry.kind === "inductive") {
                const bundle = inductiveByName.get(entry.name);
                if (bundle)
                    core.registerSystemInductive(bundle);
                continue;
            }
            const definition = definitionByName.get(entry.name);
            if (definition)
                core.registerSystemDefinition(entry.name, Core.clone(definition));
        }
    }
    catch (error) {
        // Definitions install their source before checking it, and an earlier
        // inductive bundle may already be live. Revoke the entire candidate
        // projection before exposing the failure.
        core.clearSystemInductives();
        for (const [name] of definitions) {
            core.setSystemDefinition(name);
            core.clearDefinitionCache(name);
        }
        for (const [name] of axioms)
            core.setSystemType(name);
        throw error;
    }
}
/**
 * DOM-free owner for a configured type-theory Core. This is shared by the
 * worker entry point and any future non-visual callers.
 */
export class TTCoreEngine {
    core = new Core();
    rules = initTypeSystem();
    configure(config) {
        langMgr.lang = config.language ?? langMgr.lang;
        this.core = new Core();
        Core.timeout = config.timeout ?? Core.timeout;
        if (config.semanticResourceScale !== undefined) {
            Core.setSemanticResourceScale(config.semanticResourceScale);
        }
        Core.timeoutOccured = false;
        this.registerComputeRules();
        // Seed built-in universe-level types before definitions are checked;
        // subsequent rules are synchronized incrementally in declaration order.
        this.core.syncSemanticDefinitions();
        const terms = new Set(config.unlockedTypes);
        const inferDisplayMode = config.inferDisplayMode ?? "_";
        const disableSimpleFn = !!config.disableSimpleFn;
        const disableSimpleEq = !!config.disableSimpleEq;
        const pendingDefinitions = new Map();
        for (const rule of this.rules) {
            const vname = rule.ast.nodes?.[0]?.name;
            if (!terms.has(rule.id))
                continue;
            this.core.state.disableSimpleEq = false;
            this.core.state.disableSimpleFn = false;
            if (rule.ast.type === ":" && rule.ast.nodes[0].type === "var") {
                if (terms.has("// " + vname))
                    this.core.setSystemType(vname);
                else
                    this.core.setSystemType(vname, this.core.desugar(Core.clone(rule.ast.nodes[1]), true));
            }
            if (rule.ast.type === ":=" && rule.ast.nodes[0].type === "var") {
                const value = rule.ast.nodes[1].type === ":" ? rule.ast.nodes[1].nodes[0] : rule.ast.nodes[1];
                if (terms.has("// " + vname))
                    this.core.setSystemDefinition(vname);
                else
                    this.core.setSystemDefinition(vname, this.core.desugar(Core.clone(value), true));
            }
            if (terms.has("// " + vname)) {
                this.core.clearDefinitionCache(vname);
                continue;
            }
            // This mirrors TTGui.updateTypeList. The display mode controls
            // which of the paired inferred/original declarations is active.
            if ((rule.inferMode === "@" && inferDisplayMode === "_") || (rule.inferMode === "_" && inferDisplayMode === "@")) {
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
            if (rule.ast.type === ":=") {
                const value = rule.ast.nodes[1].type === ":" ? rule.ast.nodes[1].nodes[0] : rule.ast.nodes[1];
                if (rule.ast.nodes[1].type === ":") {
                    this.core.setSystemType(vname, this.core.desugar(Core.clone(rule.ast.nodes[1].nodes[1]), true));
                }
                else {
                    try {
                        this.core.registerSystemDefinition(vname, value);
                    }
                    catch {
                        pendingDefinitions.set(vname, Core.clone(value));
                    }
                }
            }
        }
        // Complete implicit binder/universe elaboration for system types, then
        // retry aliases whose dependencies were registered later in the table.
        // A few declarations depend on one another through their public alias,
        // so keep the pass bounded and stop once no progress is made.
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
        // The sandbox Worker validates declarations in workspace order. Keep
        // that exact order here so definitions and inductives may depend on
        // any preceding trusted declaration without worker/UI drift.
        installTrustedDeclarations(this.core, config);
        this.core.syncSemanticTypes();
        this.core.state.disableSimpleFn = disableSimpleFn;
        this.core.state.disableSimpleEq = disableSimpleEq;
        this.core.state.userDefs = {};
        const userDefinitions = config.userDefinitions ?? [];
        const userDefinitionCaches = config.userDefinitionCaches ?? [];
        const definitionCounts = new Map();
        const cacheCounts = new Map();
        for (const [name] of userDefinitions) {
            definitionCounts.set(name, (definitionCounts.get(name) ?? 0) + 1);
        }
        for (const [name] of userDefinitionCaches) {
            cacheCounts.set(name, (cacheCounts.get(name) ?? 0) + 1);
        }
        const ambiguousCacheNames = new Set(Array.from(definitionCounts)
            .filter(([name, count]) => (cacheCounts.get(name) ?? 0) !== count)
            .map(([name]) => name));
        for (const [name, definition] of userDefinitions) {
            this.core.state.userDefs[name] = Core.clone(definition);
        }
        for (const [name, cache] of userDefinitionCaches) {
            if (ambiguousCacheNames.has(name))
                continue;
            if (this.core.state.userDefs[name])
                this.core.restoreDefinitionCache(name, cache);
        }
        this.core.syncSemanticDefinitions();
        // A stale Worker or an older persisted session can provide a verified
        // definition without its transferable type cache.  The definition is
        // then visible to delta reduction but unusable as a theorem because
        // the semantic checker has no constant type. Rebuild only those rare
        // missing entries, in visible declaration order, and keep the result
        // as a native NbE cache for subsequent proof-assistant requests.
        const lastDefinitionIndex = new Map();
        userDefinitions.forEach(([name], index) => lastDefinitionIndex.set(name, index));
        for (let index = 0; index < userDefinitions.length; index++) {
            const [name, definition] = userDefinitions[index];
            if (lastDefinitionIndex.get(name) !== index
                || this.core.hasDefinitionCache(name))
                continue;
            try {
                this.recoverUserDefinitionCache(name, definition);
            }
            catch { }
        }
    }
    recoverUserDefinitionCache(name, definition = this.core.state.userDefs[name]) {
        if (!definition)
            return null;
        const declaration = {
            type: ":=", name: "", nodes: [
                { type: "var", name, nodes: [] },
                Core.clone(definition)
            ]
        };
        const { definitionCache } = this.core.checkDefinition(declaration, []);
        this.core.restoreDefinitionCache(name, definitionCache);
        return definitionCache;
    }
    check(input, context = []) {
        return this.checkAst(parser.parse(input), context);
    }
    checkAst(ast, context = []) {
        const started = performance.now();
        Core.timeoutOccured = false;
        try {
            if (!ast)
                throw new Error(TR("空表达式"));
            markExplicitAtSyntax(ast);
            const type = this.core.checkType(ast, context, false);
            restoreSemanticMetaNamesForDisplay(ast);
            const inferenceComplete = theoremInferenceComplete(ast);
            return {
                ok: true,
                ast,
                type,
                inferenceComplete,
                timeout: !!Core.timeoutOccured,
                durationMs: performance.now() - started
            };
        }
        catch (error) {
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
    registerDefinition(ast, context = []) {
        const started = performance.now();
        Core.timeoutOccured = false;
        try {
            if (ast?.type !== ":=" || ast.nodes?.[0]?.type !== "var") {
                throw new Error(TR("只能注册具名定义"));
            }
            markExplicitAtSyntax(ast);
            const { filledDefinition, definitionCache } = this.core.checkDefinition(ast, context);
            this.core.restoreDefinitionCache(ast.nodes[0].name, definitionCache);
            const inferenceComplete = theoremInferenceComplete(filledDefinition);
            return {
                ok: true,
                ast,
                type: ast.checked,
                filledDefinition,
                inferenceComplete,
                definitionCache,
                timeout: !!Core.timeoutOccured,
                durationMs: performance.now() - started
            };
        }
        catch (error) {
            return {
                ok: false,
                ast,
                error: String(error),
                timeout: !!Core.timeoutOccured,
                durationMs: performance.now() - started
            };
        }
    }
    registerComputeRules() {
        const expand = {};
        for (const rule of this.rules) {
            if (rule.ast.type === ":=" && rule.ast.nodes[0].type === "var") {
                let sub = rule.ast.nodes[1];
                const applyList = [];
                let isInfer = true;
                while (sub.type === "apply") {
                    applyList.unshift(sub.nodes[1]);
                    if (sub.nodes[1].type !== "var" || sub.nodes[1].name !== "_")
                        isInfer = false;
                    sub = sub.nodes[0];
                }
                applyList.unshift(sub);
                if (sub.name[0] === "@" && isInfer)
                    this.core.opaque.push([rule.ast.nodes[0].name, applyList.length]);
                expand[rule.ast.nodes[0].name] = applyList;
            }
            if (rule.postfix !== "计算" || rule.ast.type !== "===" || rule.id === "Function")
                continue;
            const applyList = [];
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
        this.core.syncSemanticComputeRules();
    }
}
//# sourceMappingURL=engine.js.map