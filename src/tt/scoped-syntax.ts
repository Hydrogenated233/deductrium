import type { AST } from "./astparser.js";

/**
 * A checker context is ordered from the nearest binding to the outermost one.
 * The tuple shape stays compatible with saves and the legacy Core API.
 */
export type Context = [string, AST, number][];

/** A binder visible while traversing syntax. */
export type ScopeBinding = {
    name: string;
    id?: number;
    sourceId?: number;
    type?: AST;
};

/** A serializable lexical scope snapshot used by non-recursive transforms. */
export type ScopeSnapshot = readonly ScopeBinding[];

export type ContextBinding = {
    name: string;
    id?: number;
    key: string;
};

export type ContextIndex = {
    /** Positions are ordered nearest-first. */
    byName: Map<string, number[]>;
    /** Positions are ordered nearest-first. */
    byBondVarId: Map<number | undefined, number[]>;
    entries: Context[number][];
    bindings: ContextBinding[];
    nextId: number;
};

const contextIndexes = new WeakMap<Context, ContextIndex>();
const EMPTY_CONTEXT_INDEX: ContextIndex = {
    byName: new Map(),
    byBondVarId: new Map(),
    entries: [],
    bindings: [],
    nextId: 1
};

/** Positive IDs are real binder identities; 0 and Infinity are sentinels. */
export function validBondVarId(id: unknown): id is number {
    return typeof id === "number" && Number.isFinite(id) && id > 0;
}

export function isBinderType(type: string | undefined): boolean {
    return type === "L" || type === "P" || type === "S" || type === "W";
}

export function isBinderNode(ast: AST | null | undefined): boolean {
    return isBinderType(ast?.type);
}

/** Whether a binder remains semantically visible in its body. Domains of a
 * nested binder are outside that nested binder's scope, while its body may
 * shadow a malformed reused id. */
export function referencesBoundBinder(ast: AST, targetId: number): boolean {
    if (!validBondVarId(targetId)) return false;
    const visit = (node: AST, shadowed: boolean): boolean => {
        if (!node || typeof node !== "object") return false;
        if (node.type === "var") {
            return !shadowed && node.bondVarId === targetId;
        }
        if (isBinderNode(node)) {
            return visit(node.nodes?.[0], shadowed)
                || visit(
                    node.nodes?.[1],
                    shadowed || node.bondVarId === targetId
                );
        }
        return (node.nodes ?? []).some(child => visit(child, shadowed));
    };
    return visit(ast, false);
}

function contextIsCached(context: Context, cached: ContextIndex) {
    return cached.entries.length === context.length
        && (!context.length
            || (cached.entries[0] === context[0]
                && cached.entries[context.length - 1] === context[context.length - 1]));
}

/**
 * Return the shared indexed view of a context. Context arrays remain ordinary
 * mutable arrays for compatibility; the edge-reference check invalidates the
 * common push/unshift/slice mutations without adding a wrapper object to each
 * checker call.
 */
export function getContextIndex(context: Context): ContextIndex {
    if (!context.length) return EMPTY_CONTEXT_INDEX;
    const cached = contextIndexes.get(context);
    if (cached && contextIsCached(context, cached)) return cached;

    const index: ContextIndex = {
        byName: new Map(),
        byBondVarId: new Map(),
        entries: Array.from(context),
        bindings: [],
        nextId: 1
    };
    for (let position = 0; position < context.length; position++) {
        const [name, , id] = context[position];
        const namePositions = index.byName.get(name) ?? [];
        namePositions.push(position);
        index.byName.set(name, namePositions);
        const idPositions = index.byBondVarId.get(id) ?? [];
        idPositions.push(position);
        index.byBondVarId.set(id, idPositions);
        if (validBondVarId(id)) index.nextId = Math.max(index.nextId, id + 1);
        index.bindings.push({
            name,
            id: validBondVarId(id) ? id : undefined,
            key: validBondVarId(id) ? `context-id:${id}` : `context-name:${position}:${name}`
        });
    }
    contextIndexes.set(context, index);
    return index;
}

export function contextBindings(context: Context): ContextIndex {
    return getContextIndex(context);
}

export function findContextByName(context: Context, name: string): Context[number] | undefined {
    const position = getContextIndex(context).byName.get(name)?.[0];
    return position === undefined ? undefined : context[position];
}

export function findContextIndexByName(context: Context, name: string): number {
    return getContextIndex(context).byName.get(name)?.[0] ?? -1;
}

export function hasContextName(context: Context, name: string): boolean {
    return getContextIndex(context).byName.has(name);
}

export function findContextIndexByBondVarId(
    context: Context,
    id: number,
    equivalent: (left: number, right: number) => boolean
): number {
    const index = getContextIndex(context);
    const exact = index.byBondVarId.get(id)?.[0];
    if (exact !== undefined) return exact;
    for (const [candidate, positions] of index.byBondVarId) {
        if (candidate !== undefined && candidate !== id && equivalent(candidate, id)) {
            return positions[0];
        }
    }
    return -1;
}

export function findContextEntriesBeforeByName(
    context: Context,
    name: string,
    end: number
): Context[number][] {
    const positions = getContextIndex(context).byName.get(name) ?? [];
    return positions.filter(position => position < end).map(position => context[position]);
}

/** Clone syntax without checked metadata; this is the standard portable form. */
export function cloneSyntax(ast: AST): AST {
    if (!ast) return ast;
    return {
        type: ast.type,
        name: ast.name,
        bondVarId: ast.bondVarId,
        nodes: ast.nodes?.map(cloneSyntax),
        displayExplicitAt: ast.displayExplicitAt,
        nbeGeneratedMeta: ast.nbeGeneratedMeta
    };
}

export function prependContext(added: Context[number], context: Context): Context {
    const result = context.slice();
    result.unshift(added);
    return result;
}

const scopedContextCache = new WeakMap<Context, WeakMap<object, Context>>();

/** Merge a prepared binder telescope with a context, preserving object reuse. */
export function contextWithScope(
    scope: readonly ScopeBinding[],
    context: Context
): Context {
    if (!scope.length) return context;
    let byScope = scopedContextCache.get(context);
    if (!byScope) {
        byScope = new WeakMap();
        scopedContextCache.set(context, byScope);
    }
    const cached = byScope.get(scope as object);
    if (cached) return cached;
    const scoped: Context = [];
    for (const binding of scope) {
        if (binding.type) scoped.push([binding.name, binding.type, binding.id]);
    }
    const merged = scoped.length ? [...scoped, ...context] : context;
    byScope.set(scope as object, merged);
    return merged;
}

/**
 * Scope lookup used by the semantic checker. A marked occurrence first tries
 * the source binder id and may fall back to the freshly allocated id; an
 * unmarked occurrence uses nearest-name lookup.
 */
export function lookupScope(
    ast: AST,
    scope: readonly ScopeBinding[] | ScopeCursor,
    sourceIdsOnly = false
): ScopeBinding | undefined {
    if (scope instanceof ScopeCursor) return scope.lookup(ast, sourceIdsOnly);
    if (validBondVarId(ast?.bondVarId)) {
        return scope.find(binding => binding.sourceId === ast.bondVarId)
            ?? (!sourceIdsOnly
                ? scope.find(binding => binding.id === ast.bondVarId)
                : undefined);
    }
    return scope.find(binding => binding.name === ast?.name);
}

/** Return the nearest matching binding and its nearest-first position. */
export function lookupScopePosition(
    ast: AST,
    scope: readonly ScopeBinding[] | ScopeCursor,
    sourceIdsOnly = false
): { binding: ScopeBinding, position: number } | undefined {
    if (scope instanceof ScopeCursor) {
        const position = sourceIdsOnly
            ? scope.sourcePosition(ast)
            : scope.position(ast);
        const binding = position < 0 ? undefined : scope.at(position);
        return binding ? { binding, position } : undefined;
    }
    if (validBondVarId(ast?.bondVarId)) {
        const sourcePosition = scope.findIndex(binding => binding.sourceId === ast.bondVarId);
        if (sourcePosition >= 0) return { binding: scope[sourcePosition], position: sourcePosition };
        if (sourceIdsOnly) return undefined;
        const idPosition = scope.findIndex(binding => binding.id === ast.bondVarId);
        return idPosition < 0 ? undefined : { binding: scope[idPosition], position: idPosition };
    }
    const position = scope.findIndex(binding => binding.name === ast?.name);
    return position < 0 ? undefined : { binding: scope[position], position };
}

/** Kernel lookup: marked ids are authoritative; unmarked names only match an
 * unmarked binder so a substituted free constant is never captured. */
export function findKernelScopeIndex(
    ast: AST,
    scope: readonly ScopeBinding[] | ScopeCursor
): number {
    if (scope instanceof ScopeCursor) return scope.findIndex(ast);
    if (validBondVarId(ast?.bondVarId)) {
        return scope.findIndex(binding => binding.id === ast.bondVarId);
    }
    return scope.findIndex(binding => !validBondVarId(binding.id)
        && binding.name === ast?.name);
}

export function findContextBinding(
    ast: AST,
    context: readonly ContextBinding[] | ContextIndex
): ContextBinding | undefined {
    if (isContextIndex(context)) {
        const positions = validBondVarId(ast?.bondVarId)
            ? context.byBondVarId.get(ast.bondVarId)
            : context.byName.get(ast?.name);
        const position = positions?.[0];
        return position === undefined ? undefined : context.bindings[position];
    }
    if (validBondVarId(ast?.bondVarId)) {
        return context.find(binding => binding.id === ast.bondVarId);
    }
    return context.find(binding => binding.name === ast?.name);
}

function isContextIndex(
    context: readonly ContextBinding[] | ContextIndex
): context is ContextIndex {
    return !Array.isArray(context);
}

/** Scope position used by alpha-safe syntax transforms. */
export function scopePosition(
    ast: AST,
    scope: readonly ScopeBinding[] | ScopeCursor
): number {
    if (scope instanceof ScopeCursor) return scope.position(ast);
    if (validBondVarId(ast?.bondVarId)) {
        return scope.findIndex(binding => binding.id === ast.bondVarId
            || binding.sourceId === ast.bondVarId);
    }
    return scope.findIndex(binding => !validBondVarId(binding.id)
        && !validBondVarId(binding.sourceId)
        && binding.name === ast?.name);
}

/**
 * A mutable lexical scope cursor. `withBinding` gives recursive traversals
 * O(1) push/pop and indexed name/id lookup without allocating
 * `[binding, ...scope]` at every binder.
 */
export class ScopeCursor {
    private readonly entries: ScopeBinding[] = [];
    private readonly idPositions = new Map<number, number[]>();
    private readonly sourceIdPositions = new Map<number, number[]>();
    private readonly unmarkedSourceNamePositions = new Map<string, number[]>();
    private readonly unmarkedNamePositions = new Map<string, number[]>();
    private readonly namePositions = new Map<string, number[]>();

    get length() {
        return this.entries.length;
    }

    at(index: number) {
        const position = this.entries.length - 1 - Math.floor(index);
        return position >= 0 ? this.entries[position] : undefined;
    }

    findIndex(ast: AST): number {
        if (validBondVarId(ast?.bondVarId)) {
            const positions = this.idPositions.get(ast.bondVarId);
            const position = positions?.[positions.length - 1];
            return position === undefined ? -1 : this.entries.length - 1 - position;
        }
        const positions = this.unmarkedNamePositions.get(ast?.name);
        const position = positions?.[positions.length - 1];
        return position === undefined ? -1 : this.entries.length - 1 - position;
    }

    find(ast: AST) {
        const index = this.findIndex(ast);
        return index < 0 ? undefined : this.at(index);
    }

    findById(id: number) {
        if (!validBondVarId(id)) return undefined;
        const positions = this.idPositions.get(id);
        const position = positions?.[positions.length - 1];
        return position === undefined ? undefined : this.entries[position];
    }

    findBySourceId(sourceId: number) {
        if (!validBondVarId(sourceId)) return undefined;
        const positions = this.sourceIdPositions.get(sourceId);
        const position = positions?.[positions.length - 1];
        return position === undefined ? undefined : this.entries[position];
    }

    /** Preserve legacy nearest-first matching when either identity can match. */
    findBySourceOrId(id: number) {
        if (!validBondVarId(id)) return undefined;
        const sourcePosition = this.sourceIdPositions.get(id)?.at(-1);
        const idPosition = this.idPositions.get(id)?.at(-1);
        const position = sourcePosition === undefined
            ? idPosition
            : idPosition === undefined ? sourcePosition : Math.max(sourcePosition, idPosition);
        return position === undefined ? undefined : this.entries[position];
    }

    findByName(name: string) {
        const position = this.namePositions.get(name)?.at(-1);
        return position === undefined ? undefined : this.entries[position];
    }

    /** An id-less occurrence may only bind an originally id-less binder. */
    findByUnmarkedSourceName(name: string) {
        const position = this.unmarkedSourceNamePositions.get(name)?.at(-1);
        return position === undefined ? undefined : this.entries[position];
    }

    /** Iterate the currently-live positive binder identities without a scope snapshot. */
    activeBondVarIds(): IterableIterator<number> {
        return this.idPositions.keys();
    }

    /** Checker lookup preserves source binder ids across freshening. */
    lookup(ast: AST, sourceIdsOnly = false) {
        if (validBondVarId(ast?.bondVarId)) {
            const bySource = this.findBySourceId(ast.bondVarId);
            if (bySource) return bySource;
            return sourceIdsOnly ? undefined : this.findById(ast.bondVarId);
        }
        return this.findByName(ast?.name);
    }

    /** Alpha-safe checker position: source ids precede fresh ids. */
    position(ast: AST): number {
        let position: number | undefined;
        if (validBondVarId(ast?.bondVarId)) {
            position = this.sourceIdPositions.get(ast.bondVarId)?.at(-1)
                ?? this.idPositions.get(ast.bondVarId)?.at(-1);
        } else {
            const positions = this.unmarkedNamePositions.get(ast?.name);
            position = positions?.at(-1);
        }
        return position === undefined ? -1 : this.entries.length - 1 - position;
    }

    sourcePosition(ast: AST): number {
        if (!validBondVarId(ast?.bondVarId)) return -1;
        const position = this.sourceIdPositions.get(ast.bondVarId)?.at(-1);
        return position === undefined ? -1 : this.entries.length - 1 - position;
    }

    hasName(name: string) {
        return !!this.namePositions.get(name)?.length;
    }

    push(binding: ScopeBinding) {
        const position = this.entries.length;
        this.entries.push(binding);
        const namePositions = this.namePositions.get(binding.name) ?? [];
        namePositions.push(position);
        this.namePositions.set(binding.name, namePositions);
        if (validBondVarId(binding.id)) {
            const positions = this.idPositions.get(binding.id) ?? [];
            positions.push(position);
            this.idPositions.set(binding.id, positions);
        } else {
            const positions = this.unmarkedNamePositions.get(binding.name) ?? [];
            positions.push(position);
            this.unmarkedNamePositions.set(binding.name, positions);
        }
        if (validBondVarId(binding.sourceId)) {
            const positions = this.sourceIdPositions.get(binding.sourceId) ?? [];
            positions.push(position);
            this.sourceIdPositions.set(binding.sourceId, positions);
        } else {
            const positions = this.unmarkedSourceNamePositions.get(binding.name) ?? [];
            positions.push(position);
            this.unmarkedSourceNamePositions.set(binding.name, positions);
        }
    }

    pop() {
        const binding = this.entries.pop();
        if (!binding) return undefined;
        const namePositions = this.namePositions.get(binding.name);
        namePositions?.pop();
        if (!namePositions?.length) this.namePositions.delete(binding.name);
        if (validBondVarId(binding.id)) {
            const positions = this.idPositions.get(binding.id);
            positions?.pop();
            if (!positions?.length) this.idPositions.delete(binding.id);
        } else {
            const positions = this.unmarkedNamePositions.get(binding.name);
            positions?.pop();
            if (!positions?.length) this.unmarkedNamePositions.delete(binding.name);
        }
        if (validBondVarId(binding.sourceId)) {
            const positions = this.sourceIdPositions.get(binding.sourceId);
            positions?.pop();
            if (!positions?.length) this.sourceIdPositions.delete(binding.sourceId);
        } else {
            const positions = this.unmarkedSourceNamePositions.get(binding.name);
            positions?.pop();
            if (!positions?.length) this.unmarkedSourceNamePositions.delete(binding.name);
        }
        return binding;
    }

    withBinding<T>(binding: ScopeBinding, callback: () => T): T {
        this.push(binding);
        try {
            return callback();
        } finally {
            this.pop();
        }
    }

    /** Compatibility escape hatch for diagnostics and tests. */
    toArray(): ScopeBinding[] {
        return this.entries.slice().reverse();
    }
}

/** Mark unannotated binder occurrences using a caller-owned id allocator. */
export function markScopedBondVars(
    ast: AST,
    context: Context,
    allocateId: () => number
) {
    const scope = new Map<string, Context[number]>();
    for (let index = context.length - 1; index >= 0; index--) {
        scope.set(context[index][0], context[index]);
    }
    const visit = (node: AST): void => {
        if (!node) return;
        if (node.type === "var") {
            if (!node.bondVarId) node.bondVarId = scope.get(node.name)?.[2];
            return;
        }
        if (isBinderNode(node)) {
            if (node.bondVarId) return;
            node.bondVarId = allocateId();
            if (node.name === "_") node.name = "*" + node.bondVarId;
            visit(node.nodes?.[0]);
            const previous = scope.get(node.name);
            scope.set(node.name, [node.name, node.nodes?.[0], node.bondVarId]);
            visit(node.nodes?.[1]);
            if (previous) scope.set(node.name, previous);
            else scope.delete(node.name);
            return;
        }
        for (const child of node.nodes ?? []) visit(child);
    };
    visit(ast);
    return ast;
}

/** Collect binder ids that occur free in a syntax tree without allocating a
 * fresh Set for every binder body. */
export function collectFreeBondVarIds(
    ast: AST,
    result = new Set<number>(),
    scope = new Set<number>()
): Set<number> {
    if (!ast || typeof ast !== "object") return result;
    if (ast.type === "var" && validBondVarId(ast.bondVarId)) {
        if (!scope.has(ast.bondVarId)) result.add(ast.bondVarId);
        return result;
    }
    if (isBinderNode(ast) && validBondVarId(ast.bondVarId)) {
        collectFreeBondVarIds(ast.nodes?.[0], result, scope);
        const alreadyBound = scope.has(ast.bondVarId);
        scope.add(ast.bondVarId);
        collectFreeBondVarIds(ast.nodes?.[1], result, scope);
        if (!alreadyBound) scope.delete(ast.bondVarId);
        return result;
    }
    for (const child of ast.nodes ?? []) {
        collectFreeBondVarIds(child, result, scope);
    }
    return result;
}
