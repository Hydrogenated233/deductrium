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
        this.rewind(start);
        this.definitions.length = Math.min(this.definitions.length, start);
    }

    /**
     * Move the loaded definition cursor backwards without discarding stored
     * slots. This keeps ordinary same-row checks O(1) and lets a later forward
     * move reload only the definitions it crosses.
     */
    private rewind(start: number) {
        start = Math.min(Math.max(0, Math.floor(start)), this.loadedThrough);
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
            this.engine.core.setUserDefinition(definition[0]);
            delete this.engine.core.state.defTypes[definition[0]];
        }
        this.loadedThrough = start;
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
            // registerDefinition already installed this exact validated cache.
            // Preserve it while attaching the definition source so the large
            // term is compiled once instead of once before and once after the
            // same cache is restored.
            this.loadDefinition(definition, true);
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
            this.rewind(index);
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

    private loadDefinition(
        definition: Exclude<TTDefinitionSlot, null>,
        cacheAlreadyInstalled = false
    ) {
        const [name, value, cache] = definition;
        // Definition values are immutable inputs to the checker: Core clones
        // them before reduction. Reusing this owned AST avoids keeping a
        // second full copy of every restored theorem in the Worker session.
        this.engine.core.setUserDefinition(name, value, cacheAlreadyInstalled && !!cache);
        if (cache) {
            if (!cacheAlreadyInstalled) this.engine.core.restoreDefinitionCache(name, cache);
            return;
        }
        try {
            definition[2] = this.engine.recoverUserDefinitionCache(name, value);
        } catch { }
    }

    private definitionFromResult(ast: AST, result: TTCoreCheckResult): Exclude<TTDefinitionSlot, null> {
        if (!result.filledDefinition) {
            throw new Error(`${ast.nodes[0].name} did not return a filled definition`);
        }
        // The checked subtree belongs to the transient validation result and
        // is not needed when the definition is expanded later. Omitting it is
        // important for large restored theorem chains.
        const filled = makePortableDefinition(Core.clone(result.filledDefinition), this.engine.core);
        const value = ast.nodes[1].type === ":" ? filled.nodes[0] : filled;
        return [
            ast.nodes[0].name,
            // checkDefinition captured this subtree after desugaring and
            // before presentation restoration. It is already kernel-ready;
            // cloning and desugaring it again is pure O(size(term)) overhead.
            value,
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

type PortableBinding = Readonly<{ id: number, name: string }>;

function makePortableDefinition(ast: AST, core: Core) {
    const freeNames = new Set<string>;
    collectFreeNames(ast, freeNames);

    const uniqueBinderName = (source: string, scope: readonly PortableBinding[]) => {
        let name = source || "*";
        while (freeNames.has(name) || scope.some(binding => binding.name === name)) name += "'";
        return name;
    };

    const visit = (node: AST, scope: readonly PortableBinding[]) => {
        if (node.type === "var") {
            if (validBondVarId(node.bondVarId)) {
                const binding = scope.find(candidate =>
                    candidate.id === node.bondVarId
                    || core.isBondVarIdEqual(candidate.id, node.bondVarId)
                );
                if (binding) node.name = binding.name;
            }
            node.bondVarId = undefined;
            return;
        }

        if (isBinder(node) && validBondVarId(node.bondVarId)) {
            visit(node.nodes?.[0], scope);
            const id = node.bondVarId;
            const name = uniqueBinderName(node.name, scope);
            node.name = name;
            node.bondVarId = undefined;
            visit(node.nodes?.[1], [{ id, name }, ...scope]);
            return;
        }

        node.bondVarId = undefined;
        for (const child of node.nodes ?? []) visit(child, scope);
    };

    visit(ast, []);
    return ast;
}

function collectFreeNames(ast: AST, names: Set<string>) {
    if (ast.type === "var" && !validBondVarId(ast.bondVarId) && ast.name) {
        names.add(ast.name);
    }
    for (const child of ast.nodes ?? []) collectFreeNames(child, names);
}

function isBinder(ast: AST) {
    return ast.type === "L" || ast.type === "P" || ast.type === "S" || ast.type === "W";
}

function validBondVarId(id: number | undefined): id is number {
    return Number.isFinite(id) && id > 0;
}
