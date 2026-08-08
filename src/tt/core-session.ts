import { AST } from "./astparser.js";
import { Context, Core, DefinitionTypeCacheSnapshot } from "./core.js";
import { TTCoreCheckResult, TTCoreConfig, TTCoreEngine } from "./engine.js";

export type TTDefinitionSlot = [string, AST, DefinitionTypeCacheSnapshot?] | null;

/**
 * Ordered, persistent definition state for a type-theory worker. Sequential
 * validation only appends one slot; edits and moves truncate the affected
 * suffix instead of rebuilding every preceding definition for every request.
 */
export class TTCoreSession {
    readonly engine = new TTCoreEngine();
    private config: TTCoreConfig = null;
    private definitions: TTDefinitionSlot[] = [];
    private loadedThrough = 0;

    configure(config: TTCoreConfig, definitions: TTDefinitionSlot[] = []) {
        const { userDefinitions, userDefinitionCaches, ...systemConfig } = config;
        this.config = systemConfig;
        this.definitions = definitions.map(cloneDefinitionSlot);
        this.rebuild(this.definitions.length);
    }

    truncate(startIndex: number) {
        const start = Math.max(0, Math.floor(startIndex));
        const retainedNames = new Set<string>();
        for (let i = 0; i < start; i++) {
            const definition = this.definitions[i];
            if (definition) retainedNames.add(definition[0]);
        }
        let needsRebuild = false;
        for (let i = start; i < this.loadedThrough; i++) {
            const definition = this.definitions[i];
            if (!definition) continue;
            if (retainedNames.has(definition[0])) needsRebuild = true;
            delete this.engine.core.state.userDefs[definition[0]];
            delete this.engine.core.state.defTypes[definition[0]];
        }
        this.definitions.length = Math.min(this.definitions.length, start);
        this.loadedThrough = Math.min(this.loadedThrough, start);
        // A local definition may intentionally shadow an ancestor using the
        // same short name (for example `f` in two proof folders). Removing
        // the child must restore the retained ancestor, not leave the name
        // absent from the persistent Worker session.
        if (needsRebuild) this.rebuild(this.loadedThrough);
    }

    validate(index: number, ast: AST, context: Context = []): TTCoreCheckResult {
        this.prepare(index);
        const previousDefinition = this.definitions[index];
        const result = ast.type === ":="
            ? this.engine.registerDefinition(ast, context)
            : this.engine.checkAst(ast, context);

        if (ast.type === ":=" || previousDefinition) {
            this.definitions.length = index + 1;
        }

        if (result.ok && ast.type === ":=") {
            const definition = this.definitionFromResult(ast, result);
            this.definitions[index] = definition;
            this.loadDefinition(definition);
        } else {
            this.definitions[index] = null;
        }
        this.loadedThrough = index + 1;
        return result;
    }

    /** Synchronize a result produced by the main-thread fallback checker. */
    setDefinition(index: number, definition: TTDefinitionSlot) {
        this.prepare(index);
        const previousDefinition = this.definitions[index];
        if (definition || previousDefinition) this.definitions.length = index + 1;
        const stored = cloneDefinitionSlot(definition);
        this.definitions[index] = stored;
        if (stored) this.loadDefinition(stored);
        this.loadedThrough = index + 1;
    }

    getDefinitionSlots(end = this.definitions.length) {
        return this.definitions.slice(0, Math.max(0, end)).map(cloneDefinitionSlot);
    }

    private prepare(index: number) {
        if (!this.config) throw new Error("Type-theory worker session is not configured");
        index = Math.max(0, Math.floor(index));
        if (this.loadedThrough > index) {
            this.rebuild(index);
        } else {
            for (let i = this.loadedThrough; i < index; i++) {
                const definition = this.definitions[i];
                if (definition) this.loadDefinition(definition);
            }
            this.loadedThrough = index;
        }
    }

    private rebuild(end: number) {
        if (!this.config) throw new Error("Type-theory worker session is not configured");
        const userDefinitions: [string, AST][] = [];
        const userDefinitionCaches: [string, DefinitionTypeCacheSnapshot][] = [];
        for (let i = 0; i < end; i++) {
            const definition = this.definitions[i];
            if (!definition) continue;
            userDefinitions.push([definition[0], Core.clone(definition[1])]);
            if (definition[2]) userDefinitionCaches.push([definition[0], definition[2]]);
        }
        this.engine.configure({ ...this.config, userDefinitions, userDefinitionCaches });
        this.loadedThrough = end;
    }

    private loadDefinition(definition: Exclude<TTDefinitionSlot, null>) {
        const [name, value, cache] = definition;
        // Definition values are immutable inputs to the checker: Core clones
        // them before reduction. Reusing this owned AST avoids keeping a
        // second full copy of every restored theorem in the Worker session.
        this.engine.core.state.userDefs[name] = value;
        if (cache) this.engine.core.restoreDefinitionCache(name, cache);
    }

    private definitionFromResult(ast: AST, result: TTCoreCheckResult): Exclude<TTDefinitionSlot, null> {
        if (!result.filledDefinition) {
            throw new Error(`${ast.nodes[0].name} did not return a filled definition`);
        }
        // The checked subtree belongs to the transient validation result and
        // is not needed when the definition is expanded later. Omitting it is
        // important for large restored theorem chains.
        const filled = clearBondIds(Core.clone(result.filledDefinition));
        const value = ast.nodes[1].type === ":" ? filled.nodes[0] : filled;
        return [
            ast.nodes[0].name,
            this.engine.core.desugar(Core.clone(value), true),
            result.definitionCache
        ];
    }
}

function cloneDefinitionSlot(definition: TTDefinitionSlot): TTDefinitionSlot {
    if (!definition) return null;
    return [
        definition[0],
        Core.clone(definition[1]),
        definition[2] ? structuredClone(definition[2]) : undefined
    ];
}

function clearBondIds(ast: AST) {
    ast.bondVarId = null;
    for (const node of ast.nodes ?? []) clearBondIds(node);
    if (ast.checked) clearBondIds(ast.checked);
    return ast;
}
