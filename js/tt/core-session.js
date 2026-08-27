import { Core } from "./core.js";
import { TTCoreEngine } from "./engine.js";
import { cloneTTCoreSessionSnapshot, cloneTTDefinitionSlot, createTTCoreSessionSnapshot } from "./core-session-snapshot.js";
import { ScopeCursor, isBinderNode, validBondVarId } from "./scoped-syntax.js";
/**
 * Ordered, persistent definition state for a type-theory worker. Sequential
 * validation only appends one slot; edits and moves truncate the affected
 * suffix instead of rebuilding every preceding definition for every request.
 */
export class TTCoreSession {
    engine = new TTCoreEngine();
    config = null;
    definitions = [];
    loadedThrough = 0;
    configure(config, definitions, loadedThrough) {
        const snapshot = createTTCoreSessionSnapshot(config, definitions, loadedThrough);
        this.config = snapshot.config;
        this.definitions = snapshot.definitions;
        this.rebuild(snapshot.loadedThrough);
    }
    /** Restore a previously exported portable session state. */
    restore(snapshot) {
        const restored = cloneTTCoreSessionSnapshot(snapshot);
        this.config = restored.config;
        this.definitions = restored.definitions;
        this.rebuild(restored.loadedThrough);
    }
    /**
     * Execute one command against this persistent session. This is the seam
     * shared by the Worker and Node-process adapters, so they cannot drift in
     * their definition cursor, rewind, or cache restoration semantics.
     */
    dispatch(request) {
        switch (request.kind) {
            case "configure":
                this.configure(request.config, request.definitions, request.loadedThrough);
                return undefined;
            case "truncate":
                this.truncate(request.startIndex);
                return undefined;
            case "set-definition":
                this.setDefinition(request.index, request.definition);
                return undefined;
            case "validate":
                return this.validate(request.index, request.ast, request.context);
            case "check":
                return request.ast
                    ? this.checkAst(request.ast, request.context)
                    : this.check(request.input, request.context);
            default:
                throw new Error(`Unknown core request: ${String(request.kind)}`);
        }
    }
    check(input, context = []) {
        return this.engine.check(input, context);
    }
    checkAst(ast, context = []) {
        return this.engine.checkAst(ast, context);
    }
    truncate(startIndex) {
        const start = Math.max(0, Math.floor(startIndex));
        this.rewind(start);
        this.definitions.length = Math.min(this.definitions.length, start);
    }
    /**
     * Move the loaded definition cursor backwards without discarding stored
     * slots. This keeps ordinary same-row checks O(1) and lets a later forward
     * move reload only the definitions it crosses.
     */
    rewind(start) {
        start = Math.min(Math.max(0, Math.floor(start)), this.loadedThrough);
        const retainedNames = new Set();
        for (let i = 0; i < start; i++) {
            const definition = this.definitions[i];
            if (definition)
                retainedNames.add(definition[0]);
        }
        let needsRebuild = false;
        for (let i = start; i < this.loadedThrough; i++) {
            const definition = this.definitions[i];
            if (!definition)
                continue;
            if (retainedNames.has(definition[0]))
                needsRebuild = true;
            this.engine.core.setUserDefinition(definition[0]);
            delete this.engine.core.state.defTypes[definition[0]];
        }
        this.loadedThrough = start;
        // A local definition may intentionally shadow an ancestor using the
        // same short name (for example `f` in two proof folders). Removing
        // the child must restore the retained ancestor, not leave the name
        // absent from the persistent Worker session.
        if (needsRebuild)
            this.rebuild(this.loadedThrough);
    }
    validate(index, ast, context = []) {
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
        }
        else {
            this.definitions[index] = null;
        }
        this.loadedThrough = index + 1;
        return result;
    }
    /** Synchronize a result produced by the main-thread fallback checker. */
    setDefinition(index, definition) {
        this.prepare(index);
        const previousDefinition = this.definitions[index];
        if (definition || previousDefinition)
            this.definitions.length = index + 1;
        const stored = cloneTTDefinitionSlot(definition);
        this.definitions[index] = stored;
        if (stored)
            this.loadDefinition(stored);
        this.loadedThrough = index + 1;
    }
    getDefinitionSlots(end = this.definitions.length) {
        return this.definitions.slice(0, Math.max(0, end)).map(cloneTTDefinitionSlot);
    }
    /** A portable state snapshot for recovery and adapter tests. */
    snapshot(end = this.definitions.length) {
        if (!this.config)
            throw new Error("Type-theory worker session is not configured");
        return createTTCoreSessionSnapshot(this.config, this.definitions.slice(0, Math.max(0, end)), Math.min(this.loadedThrough, Math.max(0, end)));
    }
    prepare(index) {
        if (!this.config)
            throw new Error("Type-theory worker session is not configured");
        index = Math.max(0, Math.floor(index));
        if (this.loadedThrough > index) {
            this.rewind(index);
        }
        else {
            for (let i = this.loadedThrough; i < index; i++) {
                const definition = this.definitions[i];
                if (definition)
                    this.loadDefinition(definition);
            }
            this.loadedThrough = index;
        }
    }
    rebuild(end) {
        if (!this.config)
            throw new Error("Type-theory worker session is not configured");
        const userDefinitions = [];
        const userDefinitionCaches = [];
        for (let i = 0; i < end; i++) {
            const definition = this.definitions[i];
            if (!definition)
                continue;
            userDefinitions.push([definition[0], Core.clone(definition[1])]);
            if (definition[2])
                userDefinitionCaches.push([definition[0], definition[2]]);
        }
        this.engine.configure({ ...this.config, userDefinitions, userDefinitionCaches });
        this.loadedThrough = end;
    }
    loadDefinition(definition, cacheAlreadyInstalled = false) {
        const [name, value, cache] = definition;
        // Definition values are immutable inputs to the checker: Core clones
        // them before reduction. Reusing this owned AST avoids keeping a
        // second full copy of every restored theorem in the Worker session.
        this.engine.core.setUserDefinition(name, value, cacheAlreadyInstalled && !!cache);
        if (cache) {
            if (!cacheAlreadyInstalled)
                this.engine.core.restoreDefinitionCache(name, cache);
            return;
        }
        try {
            definition[2] = this.engine.recoverUserDefinitionCache(name, value);
        }
        catch { }
    }
    definitionFromResult(ast, result) {
        if (!result.filledDefinition) {
            throw new Error(`${ast.nodes[0].name} did not return a filled definition`);
        }
        // The checked subtree belongs to the transient validation result and
        // is not needed when the definition is expanded later. Omitting it is
        // important for large restored theorem chains.
        const filled = makePortableDefinition(Core.clone(result.filledDefinition));
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
function makePortableDefinition(ast) {
    const freeNames = new Set;
    collectFreeNames(ast, freeNames);
    const scope = new ScopeCursor();
    const uniqueBinderName = (source) => {
        let name = source || "*";
        while (freeNames.has(name) || scope.hasName(name))
            name += "'";
        return name;
    };
    const visit = (node) => {
        if (node.type === "var") {
            if (validBondVarId(node.bondVarId)) {
                const binding = scope.findById(node.bondVarId);
                if (binding)
                    node.name = binding.name;
            }
            node.bondVarId = undefined;
            return;
        }
        if (isBinderNode(node) && validBondVarId(node.bondVarId)) {
            visit(node.nodes?.[0]);
            const id = node.bondVarId;
            const name = uniqueBinderName(node.name);
            node.name = name;
            node.bondVarId = undefined;
            scope.push({ id, name });
            try {
                visit(node.nodes?.[1]);
            }
            finally {
                scope.pop();
            }
            return;
        }
        node.bondVarId = undefined;
        for (const child of node.nodes ?? [])
            visit(child);
    };
    visit(ast);
    return ast;
}
function collectFreeNames(ast, names) {
    if (ast.type === "var" && !validBondVarId(ast.bondVarId) && ast.name) {
        names.add(ast.name);
    }
    for (const child of ast.nodes ?? [])
        collectFreeNames(child, names);
}
//# sourceMappingURL=core-session.js.map