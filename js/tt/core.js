import { TR } from "../lang.js";
import { ASTParser } from "./astparser.js";
import { SemanticNbeTypeChecker } from "./nbe-checker.js";
import { SemanticNbeKernel } from "./nbe-kernel.js";
import { compactImplicitAliasesForDisplay, hasExplicitAtOccurrence } from "./presentation.js";
const parser = new ASTParser;
const semanticResourceBaseLimits = Object.freeze({
    nbeMaxNodes: 512,
    elaborationMaxNodes: 1_024,
    synthesisMaxSteps: 8_192,
    assertionMaxSteps: 131_072,
    assertionMaxNodes: 2_048,
    outputMaxNodes: 256
});
function fitsSemanticNbeBudget(ast, maxNodes, allowRigidMetas = false, context = [], allowHoles = false, allowedMetaNames) {
    if (!ast)
        return false;
    const contextIds = new Set(context.map(([, , id]) => id).filter(id => Number.isFinite(id) && id > 0));
    const stack = [[ast, false, new Set()]];
    let count = 0;
    while (stack.length) {
        const [node, underBinder, activeIds] = stack.pop();
        if (!node || typeof node !== "object")
            continue;
        if (++count > maxNodes)
            return false;
        if (node.origin && typeof node.origin === "object")
            return false;
        const isAllowedMeta = node.type === "var"
            && !!node.name
            && !!allowedMetaNames?.has(node.name);
        if (node.type === "var" && ((node.name === "_" && !allowHoles)
            || (node.name?.startsWith("?")
                && !isAllowedMeta
                && (!allowRigidMetas || underBinder))))
            return false;
        const isBinder = node.type === "L" || node.type === "P" || node.type === "S" || node.type === "W";
        if (node.type === "var" && node.bondVarId
            && !activeIds.has(node.bondVarId) && !contextIds.has(node.bondVarId))
            return false;
        const childUnderBinder = underBinder || isBinder;
        const bodyIds = isBinder && Number.isFinite(node.bondVarId) && node.bondVarId > 0
            ? new Set(activeIds).add(node.bondVarId)
            : activeIds;
        for (let index = 0; index < (node.nodes ?? []).length; index++) {
            const child = node.nodes[index];
            stack.push([child, childUnderBinder, isBinder && index === 1 ? bodyIds : activeIds]);
        }
    }
    return true;
}
function exceedsSemanticNbeNodeBudget(ast, maxNodes) {
    if (!ast)
        return false;
    const stack = [ast];
    let count = 0;
    while (stack.length) {
        const node = stack.pop();
        if (!node || typeof node !== "object")
            continue;
        if (++count > maxNodes)
            return true;
        for (const child of node.nodes ?? [])
            stack.push(child);
    }
    return false;
}
function countSemanticNbeNodes(ast) {
    if (!ast)
        return 0;
    const stack = [ast];
    let count = 0;
    while (stack.length) {
        const node = stack.pop();
        if (!node || typeof node !== "object")
            continue;
        count++;
        for (const child of node.nodes ?? [])
            stack.push(child);
    }
    return count;
}
function semanticAssertionKernelNodeBudget(source, kernel, sourceMaxNodes) {
    if (!source)
        return sourceMaxNodes;
    // The kernel tree was produced from this exact source subtree by the
    // trusted desugarer. Keep the finite source cap and compensate only for
    // nodes introduced by that deterministic transformation.
    return sourceMaxNodes + Math.max(0, countSemanticNbeNodes(kernel) - countSemanticNbeNodes(source));
}
function hasSemanticElaborationHole(ast) {
    const stack = [ast];
    const seen = new WeakSet();
    while (stack.length) {
        const node = stack.pop();
        if (!node || typeof node !== "object" || seen.has(node))
            continue;
        seen.add(node);
        if (node.type === "var"
            && (node.name === "_" || node.name?.startsWith("?")))
            return true;
        for (const child of node.nodes ?? [])
            stack.push(child);
    }
    return false;
}
// sugars begin
export function wrapVar(v) {
    return { type: "var", name: v };
}
function wrapU(v) {
    return { type: "apply", name: "", nodes: [wrapVar("U"), wrapVar(v)] };
}
export function wrapLambda(type, param, paramType, body) {
    return { type, name: param, nodes: [paramType, body] };
}
export function wrapApply(...terms) {
    let ast = terms[0];
    for (let i = 1; i < terms.length; i++) {
        ast = { type: "apply", name: "", nodes: [ast, terms[i]] };
    }
    return ast;
}
function isPositiveBondVarId(id) {
    return Number.isFinite(id) && id > 0;
}
/** Rebind a cloned type pattern without touching Core's mutable checker state. */
function prepareSemanticTypePattern(ast, context, firstId, collectSourceMetas) {
    let nextId = firstId;
    const contextScope = [];
    for (const [name, , sourceId] of context) {
        if (!isPositiveBondVarId(sourceId))
            continue;
        contextScope.push({ name, sourceId, id: sourceId });
        nextId = Math.max(nextId, sourceId + 1);
    }
    const metaScopes = new Map();
    const visit = (node, scope) => {
        if (!node || typeof node !== "object")
            return;
        if (node.type === "var") {
            if (/^\?[^:]+$/.test(node.name)) {
                if (collectSourceMetas) {
                    const occurrenceScope = new Set(scope.map(binding => binding.id));
                    const allowed = metaScopes.get(node.name);
                    if (!allowed)
                        metaScopes.set(node.name, occurrenceScope);
                    else {
                        for (const id of allowed) {
                            if (!occurrenceScope.has(id))
                                allowed.delete(id);
                        }
                    }
                }
                delete node.bondVarId;
                return;
            }
            const sourceId = isPositiveBondVarId(node.bondVarId) ? node.bondVarId : undefined;
            const binding = sourceId !== undefined
                ? scope.find(candidate => candidate.sourceId === sourceId || candidate.id === sourceId)
                : scope.find(candidate => candidate.name === node.name);
            if (binding)
                node.bondVarId = binding.id;
            else
                delete node.bondVarId;
            return;
        }
        const binder = node.type === "L" || node.type === "P"
            || node.type === "S" || node.type === "W";
        if (!binder) {
            for (const child of node.nodes ?? [])
                visit(child, scope);
            return;
        }
        visit(node.nodes?.[0], scope);
        const sourceId = isPositiveBondVarId(node.bondVarId) ? node.bondVarId : undefined;
        const id = nextId++;
        node.bondVarId = id;
        visit(node.nodes?.[1], [{ name: node.name, sourceId, id }, ...scope]);
    };
    visit(ast, contextScope);
    return {
        nextId,
        sourceMetas: Array.from(metaScopes, ([name, allowedBondVarIds]) => ({
            name,
            role: "type",
            allowedBondVarIds: Array.from(allowedBondVarIds)
        }))
    };
}
// Context remains a normal array for callers and serialized data. The index is
// deliberately external so array operations such as slice/map keep working.
// Contexts are structurally persistent in the checker; the entry snapshot also
// invalidates the cache when callers mutate an array with unshift/push/replace.
const contextIndexes = new WeakMap();
function getContextIndex(context) {
    const cached = contextIndexes.get(context);
    // Length plus edge references catch normal push/unshift/slice mutations in
    // O(1); binder tuple fields are immutable after a checker context is
    // indexed (checkType clones contexts before assigning IDs/types).
    if (cached && cached.entries.length === context.length &&
        (!context.length || (cached.entries[0] === context[0] && cached.entries[context.length - 1] === context[context.length - 1]))) {
        return cached;
    }
    const index = {
        byName: new Map,
        byBondVarId: new Map,
        entries: Array.from(context)
    };
    for (let position = 0; position < context.length; position++) {
        const [name, , bondVarId] = context[position];
        const namePositions = index.byName.get(name) ?? [];
        namePositions.push(position);
        index.byName.set(name, namePositions);
        const idPositions = index.byBondVarId.get(bondVarId) ?? [];
        idPositions.push(position);
        index.byBondVarId.set(bondVarId, idPositions);
    }
    contextIndexes.set(context, index);
    return index;
}
/** Return the nearest context binding for a name. */
export function findContextByName(context, name) {
    const position = getContextIndex(context).byName.get(name)?.[0];
    return position === undefined ? undefined : context[position];
}
/** Return the nearest context position for a name, or -1 when absent. */
export function findContextIndexByName(context, name) {
    return getContextIndex(context).byName.get(name)?.[0] ?? -1;
}
/** Check whether a name is bound in the context. */
export function hasContextName(context, name) {
    return getContextIndex(context).byName.has(name);
}
/**
 * Return the nearest binder equivalent to id. Exact IDs use the index fast
 * path; the fallback preserves alpha-union semantics supplied by the caller.
 */
export function findContextIndexByBondVarId(context, id, equivalent) {
    const index = getContextIndex(context);
    const exact = index.byBondVarId.get(id)?.[0];
    // An identical binder ID is an exact match even when the caller's
    // equivalence predicate intentionally treats sentinel IDs (for example 0)
    // as non-binders.
    if (exact !== undefined)
        return exact;
    for (const [candidate, positions] of index.byBondVarId) {
        if (candidate !== id && equivalent(candidate, id))
            return positions[0];
    }
    return -1;
}
/** Return duplicate-name bindings before a given position, nearest first. */
export function findContextEntriesBeforeByName(context, name, end) {
    const positions = getContextIndex(context).byName.get(name) ?? [];
    return positions.filter(position => position < end).map(position => context[position]);
}
/** Clone AST metadata once while preserving sharing between contexts. */
function cloneAstMemo(ast, cloneChecked, memo) {
    if (!ast || typeof ast !== "object")
        return ast;
    const previous = memo.get(ast);
    if (previous)
        return previous;
    const copy = {
        type: ast.type,
        name: ast.name,
        checked: null,
        err: ast.err,
        bondVarId: ast.bondVarId,
        displayExplicitAt: ast.displayExplicitAt
    };
    memo.set(ast, copy);
    if (ast.nodes)
        copy.nodes = ast.nodes.map(node => cloneAstMemo(node, cloneChecked, memo));
    if (cloneChecked && ast.checked)
        copy.checked = cloneAstMemo(ast.checked, true, memo);
    return copy;
}
function collectInferenceMetaNames(ast, result = new Set()) {
    if (!ast)
        return result;
    const stack = [ast];
    const seen = new WeakSet();
    while (stack.length) {
        const node = stack.pop();
        if (!node || typeof node !== "object" || seen.has(node))
            continue;
        seen.add(node);
        if (node.type === "var" && node.name?.startsWith("?"))
            result.add(node.name);
        if (node.checked)
            stack.push(node.checked);
        for (const child of node.nodes ?? [])
            stack.push(child);
    }
    return result;
}
function normalizeSchemeMetaName(name) {
    return name.replace(/^\?/, "").replace(/:+$/, "");
}
function isSemanticDefinitionCacheSnapshot(cache) {
    if (!cache || typeof cache !== "object")
        return false;
    const candidate = cache;
    return candidate.kind === "nbe"
        && !!candidate.type
        && typeof candidate.type.type === "string"
        && Array.isArray(candidate.metas)
        && candidate.metas.every(meta => !!meta && typeof meta.name === "string")
        && Number.isFinite(candidate.bondVarId);
}
function cloneSemanticDefinitionCache(cache) {
    const memo = new WeakMap();
    const metas = cache.metas.map(meta => ({
        name: meta.name,
        expectedType: meta.expectedType
            ? cloneAstMemo(meta.expectedType, false, memo)
            : undefined,
        preset: meta.preset ? cloneAstMemo(meta.preset, false, memo) : undefined
    }));
    return {
        kind: "nbe",
        type: cloneAstMemo(cache.type, false, memo),
        metas,
        bondVarId: cache.bondVarId
    };
}
function migrateLegacyDefinitionCache(cache) {
    const schemeInput = {
        type: Core.clone(cache.type),
        metas: cache.inferTable.list.map(([rawName, context]) => {
            // Context-dependent legacy metas need the old unifier's closure
            // representation. They are not safe to flatten into a portable
            // native scheme; callers can re-infer the definition source.
            if (context.length)
                return null;
            const name = normalizeSchemeMetaName(rawName);
            const expectedType = cache.inferTable.rel[`?${name}:`];
            const preset = cache.inferTable.rel[`?${name}`];
            return {
                name,
                expectedType: expectedType ? Core.clone(expectedType) : undefined,
                preset: preset ? Core.clone(preset) : undefined
            };
        })
    };
    if (schemeInput.metas.some(meta => !meta)
        || cache.inferTable.defered.length
        || cache.bondVarRel.parent.some(([id, parent]) => id !== parent)
        || cache.bondVarRel.size.some(([, size]) => size > 1))
        return null;
    const referenced = collectInferenceMetaNames(schemeInput.type);
    for (const meta of schemeInput.metas) {
        if (meta.expectedType)
            collectInferenceMetaNames(meta.expectedType, referenced);
        if (meta.preset)
            collectInferenceMetaNames(meta.preset, referenced);
    }
    const declared = new Set(schemeInput.metas.map(meta => normalizeSchemeMetaName(meta.name)));
    if ([...referenced].some(name => !declared.has(normalizeSchemeMetaName(name))))
        return null;
    return {
        kind: "nbe",
        type: schemeInput.type,
        metas: schemeInput.metas,
        bondVarId: cache.bondVarId
    };
}
function collectAstBondVarIds(ast, result) {
    const seen = new WeakSet();
    const stack = [ast];
    while (stack.length) {
        const current = stack.pop();
        if (!current || typeof current !== "object" || seen.has(current))
            continue;
        seen.add(current);
        if (Number.isFinite(current.bondVarId) && current.bondVarId > 0) {
            result.add(current.bondVarId);
        }
        if (current.checked)
            stack.push(current.checked);
        for (const node of current.nodes ?? [])
            stack.push(node);
    }
}
function isNbeTypeFailure(value) {
    if (!value || typeof value !== "object")
        return false;
    const status = value.status;
    return status === "invalid" || status === "unsupported";
}
/** return a cloned Context */
export function assignContext(added, oldContext) {
    const n = oldContext.slice(0);
    n.unshift(added);
    return n;
}
export class Core {
    static timeout = 10_000;
    static timeoutOccured;
    /** Enable recursive semantic synthesis. */
    static semanticTypeCheckRecursive = false;
    /** Automatically use recursive synthesis once a large theorem library is loaded. */
    static semanticTypeCheckRecursiveMinDefinitions = 48;
    static semanticResourceScale = 1;
    static semanticResourceScaleMin = 1;
    static semanticResourceScaleMax = 64;
    static semanticNbEMaxNodes = semanticResourceBaseLimits.nbeMaxNodes;
    /** Hard input cap for local-meta elaboration; equality/WHNF retain their smaller budget. */
    static semanticTypeElaborationMaxNodes = semanticResourceBaseLimits.elaborationMaxNodes;
    /** Bound semantic synthesis work. */
    static semanticTypeSynthesisMaxSteps = semanticResourceBaseLimits.synthesisMaxSteps;
    /** Explicit assertions can justify a larger bounded conversion search. */
    static semanticTypeAssertionMaxSteps = semanticResourceBaseLimits.assertionMaxSteps;
    /** Explicit annotations bound elaboration, so larger proof terms can use the semantic checker safely. */
    static semanticTypeAssertionMaxNodes = semanticResourceBaseLimits.assertionMaxNodes;
    /** Reject expanded semantic result types before they enter definition caches. */
    static semanticTypeCheckMaxOutputNodes = semanticResourceBaseLimits.outputMaxNodes;
    static semanticWhnfAttempts = 0;
    static semanticWhnfHits = 0;
    static semanticTypeCheckAttempts = 0;
    static semanticTypeCheckHits = 0;
    static semanticTypeCheckFastPathHits = 0;
    static setSemanticResourceScale(value) {
        const numeric = Number(value);
        const scale = Number.isFinite(numeric)
            ? Math.min(Core.semanticResourceScaleMax, Math.max(Core.semanticResourceScaleMin, Math.floor(numeric)))
            : 1;
        Core.semanticResourceScale = scale;
        Core.semanticNbEMaxNodes = semanticResourceBaseLimits.nbeMaxNodes * scale;
        Core.semanticTypeElaborationMaxNodes = semanticResourceBaseLimits.elaborationMaxNodes * scale;
        Core.semanticTypeSynthesisMaxSteps = semanticResourceBaseLimits.synthesisMaxSteps * scale;
        Core.semanticTypeAssertionMaxSteps = semanticResourceBaseLimits.assertionMaxSteps * scale;
        Core.semanticTypeAssertionMaxNodes = semanticResourceBaseLimits.assertionMaxNodes * scale;
        Core.semanticTypeCheckMaxOutputNodes = semanticResourceBaseLimits.outputMaxNodes * scale;
        return scale;
    }
    /** Source-shaped clones used when reporting errors after elaboration mutates ASTs. */
    displaySurfaceNodes = new WeakMap();
    silentErrors = 0;
    static assign(ast, value, moveSemantic) {
        // Most substitutions assign a leaf variable/constant. Cloning a leaf
        // here is semantically unnecessary and shows up tens of millions of
        // times in the large K609 theorem. Preserve Core.clone's behavior for
        // checked metadata (cloneChecked is false) while avoiding recursion.
        if (!moveSemantic && !value.nodes) {
            ast.type = value.type;
            ast.name = value.name;
            ast.nodes = undefined;
            ast.checked = null;
            ast.bondVarId = value.bondVarId;
            ast.displayExplicitAt = value.displayExplicitAt;
            return;
        }
        const v = moveSemantic ? value : this.clone(value);
        ast.type = v.type;
        ast.name = v.name;
        ast.nodes = v.nodes;
        ast.checked = v.checked;
        ast.bondVarId = v.bondVarId;
        ast.displayExplicitAt = v.displayExplicitAt;
    }
    static match(ast, pattern, regexp, res = {}) {
        if (pattern.type === "var" && pattern.name.match(regexp)) {
            res[pattern.name] ??= ast;
            if (!this.exactEqual(ast, res[pattern.name]))
                return null;
            return res;
        }
        if (NatLiteral.is(ast) && pattern.nodes?.[0].name === "succ") {
            if (ast.name !== "0")
                return this.match(wrapVar(String(BigInt(ast.name) - 1n)), pattern.nodes[1], regexp, res);
        }
        if (ast.type !== pattern.type)
            return null;
        if (ast.nodes?.length !== pattern.nodes?.length)
            return null;
        if (ast.nodes?.length) {
            for (let i = 0; i < ast.nodes.length; i++) {
                if (!this.match(ast.nodes[i], pattern.nodes[i], regexp, res))
                    return null;
            }
        }
        if (ast.name !== pattern.name)
            return null;
        return res;
    }
    static clone(ast, cloneChecked) {
        const checked = (cloneChecked && ast.checked) ? this.clone(ast.checked) : null;
        const newast = {
            type: ast.type, name: ast.name, checked, err: ast.err, bondVarId: ast.bondVarId,
            displayExplicitAt: ast.displayExplicitAt
        };
        if (ast.nodes) {
            newast.nodes = ast.nodes.map(p => this.clone(p, cloneChecked));
        }
        return newast;
    }
    static replaceByMatch(ast, res, regexp) {
        if (!res)
            throw TR("未匹配");
        if (!ast)
            return; // here not panic because aftercheck need it
        if (ast.type === "var" && ast.name.match(regexp)) {
            if (!res[ast.name])
                return false;
            this.assign(ast, this.clone(res[ast.name]));
            return true;
        }
        else if (ast.nodes?.length) {
            let modified = false;
            for (const n of ast.nodes) {
                if (this.replaceByMatch(n, res, regexp))
                    modified = true;
            }
            return modified;
        }
    }
    static cloneContext(c) {
        return c.map(e => [e[0], e[1] ? this.clone(e[1]) : null, e[2]]);
    }
    hasBondVar(ast, id) {
        if (!ast)
            return false;
        if (ast.type === "var") {
            if (ast.name === "_" && ast.checked?.type === ":") {
                return this.hasBondVar(ast.checked.nodes[0], id);
            }
            return this.isBondVarIdEqual(ast.bondVarId, id);
        }
        else if (ast.nodes?.length) {
            return this.hasBondVar(ast.nodes[0], id) || this.hasBondVar(ast.nodes[1], id);
        }
    }
    // mark bonvar ids for an ast
    markBondVars(ast, context) {
        const scope = new Map;
        // Context is stored from innermost to outermost. Populate in reverse so
        // the nearest binding wins for duplicate names.
        for (let i = context.length - 1; i >= 0; i--) {
            scope.set(context[i][0], context[i]);
        }
        return this.markBondVarsInScope(ast, scope);
    }
    markBondVarsInScope(ast, scope) {
        if (!ast)
            return;
        if (ast.type === "var") {
            if (ast.bondVarId)
                return ast;
            ast.bondVarId = scope.get(ast.name)?.[2];
        }
        else if (ast.type === "L" || ast.type === "P" || ast.type === "W" || ast.type === "S") {
            if (ast.bondVarId)
                return ast;
            this.getBondVarId(ast);
            if (ast.name === "_")
                ast.name = "*" + ast.bondVarId;
            this.markBondVarsInScope(ast.nodes[0], scope);
            const previous = scope.get(ast.name);
            scope.set(ast.name, [ast.name, ast.nodes[0], ast.bondVarId]);
            this.markBondVarsInScope(ast.nodes[1], scope);
            if (previous)
                scope.set(ast.name, previous);
            else
                scope.delete(ast.name);
        }
        else if (ast.nodes?.length) {
            for (const node of ast.nodes)
                this.markBondVarsInScope(node, scope);
        }
        return ast;
    }
    // we didnt mark bondvar's with id, need do it
    getBondVarId(ast) {
        if (ast.bondVarId)
            return ast.bondVarId;
        ast.bondVarId = this.state.bondVarId++;
        return ast.bondVarId;
    }
    isBondVarIdEqual(m, n) {
        return isPositiveBondVarId(m) && m === n;
    }
    // return whether ast has changed 
    // if bondvarId == -1, it will exact match name, e.g. inferval
    replaceVar(ast, name, bondvarId, dst, context) {
        if (name === "_")
            return false;
        if (ast.checked)
            this.replaceVar(ast.checked, name, bondvarId, dst, context);
        if (ast.type === "var") {
            // x[y->_] -> x
            // naive approach: if (ast.name !== name) return false; this cannot deal with alpha conversion
            if (bondvarId === -1 ? ast.name !== name : !this.isBondVarIdEqual(ast.bondVarId, bondvarId))
                return false;
            // x[x->_] -> _
            Core.assign(ast, dst);
            if (dst.checked)
                ast.checked = Core.clone(dst.checked);
            return true;
        }
        else if (ast.type === "L" || ast.type === "P" || ast.type === "W" || ast.type === "S") {
            // replace node[0] type first : #rp(Lx:A,...) -> Lx:#rp(A), ...
            const head = this.replaceVar(ast.nodes[0], name, bondvarId, dst, context);
            // (Lx.x)[x->_] = (Lx.x) not changed
            // if (ast.name === name) return head;// bounded
            return this.replaceVar(ast.nodes[1], name, bondvarId, dst, context) || head;
        }
        else if (ast.nodes?.length === 2) {
            const a = this.replaceVar(ast.nodes[0], name, bondvarId, dst, context);
            const b = ast.nodes[1] ? this.replaceVar(ast.nodes[1], name, bondvarId, dst, context) : false;
            return a || b;
        }
        return false;
    }
    semanticKernel = new SemanticNbeKernel();
    semanticTypeChecker = new SemanticNbeTypeChecker(this.semanticKernel);
    state = {
        sysTypes: {
            "U@": wrapVar("U@:"),
            "U@:": wrapVar("U@:"),
            "@max": parser.parse("U@->U@->U@"),
            "@succ": parser.parse("U@->U@"),
        },
        bondVarId: 1,
        sysDefs: {},
        userDefs: {},
        defTypes: {},
        computeRules: {},
        errormsg: [],
        time: 0
    };
    semanticTypeCheckRecursiveActive = false;
    syncSemanticDefinitions() {
        const merged = new Map();
        for (const [name, definition] of Object.entries(this.state.sysDefs))
            merged.set(name, definition);
        for (const [name, definition] of Object.entries(this.state.userDefs))
            merged.set(name, definition);
        const count = this.semanticKernel.replaceDefinitions(merged);
        this.syncSemanticTypes();
        return count;
    }
    syncSemanticTypes() {
        this.semanticTypeChecker.replaceConstantTypes(Object.entries(this.state.sysTypes));
        for (const [name, rawCache] of Object.entries(this.state.defTypes)) {
            if (this.state.sysTypes[name])
                continue;
            this.syncSemanticDefinitionType(name, rawCache);
        }
        return this.semanticTypeChecker.constantTypeCount;
    }
    /**
     * Elaborate built-in constant types with the immutable checker.  System
     * declarations intentionally use `_` for universe levels and initially do
     * not carry binder ids; leaving those holes in the constant table makes a
     * later alias (for example `trunc` or `LEM`) look like an unresolved user
     * metavariable.  Run this after all raw system types are visible, then let
     * the engine retry definitions whose dependencies were not ready yet.
     *
     * The method is deliberately best-effort: declarations that need a later
     * dependency remain raw and can be retried on a later fixed-point pass.
     */
    elaborateSemanticSystemTypes(maxPasses = 4) {
        // Keep already compiled definition schemes (notably `not`, `pr0`, and
        // `Pushout`) in the table while replacing the raw system type entries.
        // Replacing with sysTypes alone would erase those schemes and make a
        // perfectly valid declaration report `unknown-constant`.
        this.syncSemanticTypes();
        const elaborated = new Set();
        let changed = 0;
        for (let pass = 0; pass < maxPasses; pass++) {
            let passChanged = 0;
            for (const [name, rawType] of Object.entries(this.state.sysTypes)) {
                if (elaborated.has(name))
                    continue;
                const result = this.semanticTypeChecker.trySynthesize(Core.clone(rawType), [], {
                    elaborateMetas: true,
                    generalizeMetas: true,
                    annotateTerm: true,
                    maxSteps: Math.max(Core.semanticTypeSynthesisMaxSteps * 4, 65_536)
                });
                if (result.status !== "success" || !result.term)
                    continue;
                const type = Core.clone(result.term);
                this.state.sysTypes[name] = type;
                this.semanticTypeChecker.setConstantType(name, type);
                elaborated.add(name);
                passChanged++;
            }
            changed += passChanged;
            if (!passChanged)
                break;
        }
        return changed;
    }
    syncSemanticComputeRules() {
        return this.semanticKernel.replaceComputeRules(this.state.computeRules);
    }
    setSystemType(name, type) {
        if (type)
            this.state.sysTypes[name] = type;
        else
            delete this.state.sysTypes[name];
        this.syncSemanticConstantType(name);
    }
    setSystemDefinition(name, definition) {
        if (definition)
            this.state.sysDefs[name] = definition;
        else
            delete this.state.sysDefs[name];
        this.syncSemanticDefinition(name);
    }
    clearDefinitionCache(name) {
        delete this.state.defTypes[name];
        this.syncSemanticConstantType(name);
        this.syncSemanticDefinition(name);
    }
    hasDefinitionCache(name) {
        return !!this.inspectDefinitionCache(this.state.defTypes[name]);
    }
    registerSystemDefinition(name, definition, context = []) {
        const source = this.desugar(Core.clone(definition), true);
        this.setSystemDefinition(name, source);
        try {
            Core.timeoutOccured = false;
            this.state.errormsg = [];
            this.state.time = Date.now();
            this.state.bondVarId = 1;
            this.semanticTypeCheckRecursiveActive = false;
            const preparedContext = context.length ? Core.cloneContext(context) : [];
            for (let index = preparedContext.length - 1; index >= 0; index--) {
                const [, type, id] = preparedContext[index];
                if (!id)
                    preparedContext[index][2] = this.state.bondVarId++;
                else if (Number.isFinite(id) && id >= this.state.bondVarId)
                    this.state.bondVarId = id + 1;
                preparedContext[index][1] = this.markBondVars(this.desugar(type, false), preparedContext.slice(index));
            }
            const filled = this.markBondVars(this.desugar(Core.clone(definition), false), preparedContext);
            let generalizedMetas;
            let elaboratedDefinition;
            const cachedType = this.trySemanticTypeSynthesis(filled, preparedContext, {
                allowHoles: true,
                elaborateMetas: true,
                generalizeMetas: true,
                requireElaboratedTerm: true,
                captureGeneralizedMetas: metas => { generalizedMetas = metas; },
                captureElaboratedTerm: term => { elaboratedDefinition = term; }
            });
            if (!cachedType)
                throw new Error(`Unsupported semantic system definition: ${name}`);
            // Keep the explicit elaboration in the kernel while `filled`
            // remains compact for presentation.  For `eq := @eq _ _`, the
            // display term is just `eq`, whereas the kernel term retains the
            // hidden arguments and fresh binder ids needed for later alpha-
            // safe expansion.
            if (elaboratedDefinition) {
                const elaboratedHead = this.flattenApplyList(elaboratedDefinition)[0];
                const collapsesToSelf = elaboratedHead?.type === "var"
                    && !elaboratedHead.bondVarId
                    && elaboratedHead.name === name;
                // Presentation compaction may fold `@name ?implicit...` back
                // to the public alias `name`. Installing that as the kernel
                // definition would create `name := name` and make delta
                // reduction loop forever. Keep the explicit source already
                // registered above when elaboration collapses this far.
                if (!collapsesToSelf) {
                    const portableDefinition = Core.clone(elaboratedDefinition);
                    const generalizedNames = new Set(generalizedMetas?.map(meta => meta.name) ?? []);
                    const restorePortableHoles = (node) => {
                        if (node.type === "var" && generalizedNames.has(node.name)) {
                            Core.assign(node, wrapVar("_"), true);
                            return;
                        }
                        for (const child of node.nodes ?? [])
                            restorePortableHoles(child);
                    };
                    restorePortableHoles(portableDefinition);
                    this.setSystemDefinition(name, portableDefinition);
                }
            }
            this.restoreDefinitionCache(name, this.createSemanticDefinitionCacheSnapshot(cachedType, this.state.bondVarId, generalizedMetas));
            return Core.clone(filled);
        }
        catch (error) {
            this.clearDefinitionCache(name);
            throw error;
        }
    }
    /** Attach a user definition, optionally retaining its just-validated cache. */
    setUserDefinition(name, definition, preserveDefinitionCache = false) {
        if (definition) {
            if (this.state.userDefs[name] !== definition && !preserveDefinitionCache) {
                delete this.state.defTypes[name];
            }
            this.state.userDefs[name] = definition;
        }
        else {
            delete this.state.userDefs[name];
            delete this.state.defTypes[name];
        }
        this.syncSemanticDefinition(name);
        this.syncSemanticConstantType(name);
    }
    clearUserDefinitions() {
        const names = Object.keys(this.state.userDefs);
        this.state.userDefs = {};
        for (const name of names) {
            delete this.state.defTypes[name];
            this.syncSemanticDefinition(name);
            this.syncSemanticConstantType(name);
        }
    }
    syncSemanticDefinition(name) {
        const definition = this.state.userDefs[name] ?? this.state.sysDefs[name];
        if (!definition) {
            this.semanticKernel.deleteDefinition(name);
            return;
        }
        const hasInferenceMetas = collectInferenceMetaNames(definition).size > 0;
        const hasTrustedTypeCache = !!this.inspectDefinitionCache(this.state.defTypes[name]);
        // Definitions carrying generalized metas are executable only after
        // their validated type scheme has been restored. Recompile on cache
        // transitions because the source fingerprint itself is unchanged.
        if (hasInferenceMetas)
            this.semanticKernel.deleteDefinition(name);
        this.semanticKernel.setDefinition(name, definition, {
            rigidMetas: hasInferenceMetas && hasTrustedTypeCache
        });
    }
    syncSemanticConstantType(name) {
        const systemType = this.state.sysTypes[name];
        if (systemType) {
            this.semanticTypeChecker.setConstantType(name, systemType);
            return;
        }
        this.syncSemanticDefinitionType(name, this.state.defTypes[name]);
    }
    syncSemanticDefinitionType(name, rawCache) {
        const cache = this.inspectDefinitionCache(rawCache);
        if (!cache) {
            this.semanticTypeChecker.setConstantType(name);
            return;
        }
        this.semanticTypeChecker.setConstantSchemeSnapshot(name, cache.semantic);
    }
    inspectDefinitionCache(rawCache) {
        if (isSemanticDefinitionCacheSnapshot(rawCache)) {
            return {
                type: rawCache.type,
                semantic: rawCache
            };
        }
        return null;
    }
    isBareGeneralizedDefinitionReference(ast) {
        if (ast?.type !== "var" || ast.bondVarId)
            return false;
        const cache = this.inspectDefinitionCache(this.state.defTypes[ast.name]);
        return !!cache?.semantic?.metas.length;
    }
    serializeDefinitionCache(name) {
        const cache = this.inspectDefinitionCache(this.state.defTypes[name]);
        if (cache?.semantic)
            return cloneSemanticDefinitionCache(cache.semantic);
        return null;
    }
    createSemanticDefinitionCacheSnapshot(cachedType, bondVarId, generalizedMetas = []) {
        return {
            kind: "nbe",
            type: Core.clone(cachedType),
            metas: generalizedMetas.map(meta => ({
                name: meta.name,
                expectedType: Core.clone(meta.expectedType)
            })),
            bondVarId
        };
    }
    restoreDefinitionCache(name, cache) {
        if (!cache)
            return;
        if (isSemanticDefinitionCacheSnapshot(cache)) {
            this.state.defTypes[name] = cloneSemanticDefinitionCache(cache);
            this.syncSemanticConstantType(name);
            this.syncSemanticDefinition(name);
            return;
        }
        const migrated = migrateLegacyDefinitionCache(cache);
        if (!migrated) {
            this.clearDefinitionCache(name);
            return;
        }
        // Validate the portable scheme with the same compiler used at every
        // semantic use site. A malformed/stale cache must be treated as
        // absent so the owning Engine can recover it from the definition
        // source; retaining an unusable `kind: "nbe"` entry would make the
        // constant appear defined while remaining unavailable to NbE.
        if (!this.semanticTypeChecker.setConstantSchemeSnapshot(name, migrated)) {
            this.clearDefinitionCache(name);
            return;
        }
        this.state.defTypes[name] = migrated;
        this.syncSemanticConstantType(name);
        this.syncSemanticDefinition(name);
    }
    clearState() {
        this.clearSemanticState();
    }
    clearSemanticState() {
        this.state.errormsg = [];
        this.state.bondVarId = 1;
    }
    error(ast, msg, stop) {
        this.state.errormsg.unshift({ ast, msg });
        if (!this.silentErrors) {
            const source = parser.stringify(ast);
            console.log(source ?? ast?.type ?? TR("表达式丢失"), msg);
        }
        ast.err = msg;
        if (stop)
            throw msg;
    }
    /** Run a speculative check without printing its expected failure. */
    withSilentErrors(callback) {
        const previousErrors = this.state.errormsg;
        const previousTimeout = Core.timeoutOccured;
        this.silentErrors++;
        try {
            return callback();
        }
        finally {
            this.silentErrors--;
            this.state.errormsg = previousErrors;
            Core.timeoutOccured = previousTimeout;
        }
    }
    checkDefinition(ast, context) {
        let prepared;
        // Preserve generalized inference variables before the validation pass
        // resolves them for display (for example U?6 must not collapse to U0).
        this.checkType(ast, context, false, (beforeInferResolutionAst, generalizedMetas = []) => {
            const sourceDefinition = beforeInferResolutionAst.nodes[1];
            // The UI and persistent session intentionally store definitions
            // without per-node checked trees. Return that compact form
            // directly instead of cloning a large transient type tree only
            // for the receiver to discard it immediately.
            const filledDefinition = Core.clone(sourceDefinition);
            const cachedType = Core.clone(sourceDefinition.type === ":"
                ? sourceDefinition.nodes[1]
                : sourceDefinition.checked);
            prepared = {
                filledDefinition,
                definitionCache: this.createSemanticDefinitionCacheSnapshot(cachedType, this.state.bondVarId, generalizedMetas)
            };
        });
        if (!prepared)
            throw TR("类型检查未返回定义结果");
        return prepared;
    }
    checkType(ast, context, allowModify, beforeInferResolution, allowUnsolvedTermMetas = false, requireSemantic = false, preservePresentation = true) {
        const semanticPresentation = preservePresentation && (!allowModify
            || (!requireSemantic && hasExplicitAtOccurrence(ast)))
            ? Core.clone(ast)
            : undefined;
        let semanticAssertionSource;
        if (!allowModify || requireSemantic) {
            const sourceRoot = semanticPresentation ?? ast;
            const sourceTarget = sourceRoot.type === ":"
                ? sourceRoot
                : sourceRoot.type === ":=" && sourceRoot.nodes?.[1]?.type === ":"
                    ? sourceRoot.nodes[1]
                    : undefined;
            semanticAssertionSource = sourceTarget
                ? semanticPresentation ? sourceTarget : Core.clone(sourceTarget)
                : undefined;
        }
        if (semanticPresentation)
            this.captureDisplaySurface(ast, semanticPresentation);
        Core.timeoutOccured = false;
        this.state.errormsg = [];
        this.state.time = Date.now();
        this.state.bondVarId = 1;
        this.semanticTypeCheckRecursiveActive = Core.semanticTypeCheckRecursive
            || Object.keys(this.state.userDefs).length
                >= Core.semanticTypeCheckRecursiveMinDefinitions;
        // mark if context is not marked
        if (context.length)
            context = Core.cloneContext(context);
        for (let i = context.length - 1; i >= 0; i--) {
            const [e, t, id] = context[i];
            if (!id)
                context[i][2] = this.state.bondVarId++;
            else if (Number.isFinite(id) && id >= this.state.bondVarId)
                this.state.bondVarId = id + 1;
            context[i][1] = this.markBondVars(this.desugar(t, false), context.slice(i));
        }
        ast = this.markBondVars(this.desugar(ast, allowModify), context);
        const semanticAssertionTarget = !allowModify || requireSemantic
            ? ast.type === ":"
                ? ast
                : ast.type === ":=" && ast.nodes?.[1]?.type === ":"
                    ? ast.nodes[1]
                    : undefined
            : undefined;
        if (semanticAssertionTarget) {
            const semanticAssertion = this.trySemanticTypeAssertion(semanticAssertionTarget, context, !beforeInferResolution, allowUnsolvedTermMetas
                || hasSemanticElaborationHole(semanticAssertionTarget.nodes[0]), semanticAssertionSource);
            if (isNbeTypeFailure(semanticAssertion)) {
                this.reportSemanticFailure(semanticAssertionTarget, semanticAssertion);
            }
            else if (semanticAssertion === false) {
                this.error(ast, TR("类型断言失败"), true);
            }
            else if (semanticAssertion) {
                if (semanticAssertionTarget !== ast) {
                    ast.nodes[0].checked = semanticAssertion.checked;
                    ast.checked = semanticAssertion.checked;
                }
                if (beforeInferResolution) {
                    beforeInferResolution(ast, semanticAssertion.generalizedMetas);
                }
                Core.semanticTypeCheckFastPathHits++;
                // Definition registration stores its kernel-ready term in the
                // callback above, then restores the user's surface syntax for
                // display. Only the returned type needs semantic finalization;
                // walking and ensugaring the entire proof would be discarded
                // immediately by restoreSemanticPresentation.
                if (beforeInferResolution && semanticPresentation && ast.checked) {
                    this.finalizeSemanticResult(ast.checked, context);
                }
                else {
                    this.finalizeSemanticResult(ast, context);
                }
                if (semanticPresentation) {
                    this.restoreSemanticPresentation(ast, semanticPresentation);
                }
                if (this.state.errormsg.length)
                    throw this.state.errormsg[0].msg;
                return ast.checked;
            }
        }
        if (ast.type === "===") {
            const semanticEquality = this.trySemanticDefinitionalEquality(ast, context);
            if (isNbeTypeFailure(semanticEquality)) {
                this.reportSemanticFailure(ast, semanticEquality);
            }
            else if (semanticEquality === false) {
                const unresolvedDefinitions = this.semanticErrorUnresolvedDefinitions(ast);
                const unresolvedSuffix = unresolvedDefinitions.length
                    ? ` [${unresolvedDefinitions.join(", ")}: _]`
                    : "";
                this.error(ast, TR("定义相等断言失败") + ": "
                    + this.printSemanticErrorAst(ast.nodes[0]) + " ≠ "
                    + this.printSemanticErrorAst(ast.nodes[1])
                    + unresolvedSuffix, true);
            }
            else if (semanticEquality) {
                Core.semanticTypeCheckFastPathHits++;
                this.finalizeSemanticResult(ast, context);
                if (semanticPresentation) {
                    this.restoreSemanticPresentation(ast, semanticPresentation);
                }
                if (this.state.errormsg.length)
                    throw this.state.errormsg[0].msg;
                return ast.checked;
            }
        }
        if (allowModify && ast.type === "whnf"
            && this.trySemanticProofAssistantNormalize(ast.nodes[0], context)) {
            this.finalizeSemanticResult(ast.nodes[0], context);
            if (this.state.errormsg.length)
                throw this.state.errormsg[0].msg;
            return ast.nodes[0];
        }
        let semanticTarget;
        if (!allowModify) {
            if (ast.type === ":=" && ast.nodes?.[1]?.type !== ":") {
                semanticTarget = ast.nodes[1];
            }
            else if (ast.type !== ":" && ast.type !== ":=" && ast.type !== "===" && ast.type !== "whnf") {
                semanticTarget = ast;
            }
        }
        if (semanticTarget) {
            const semanticDefinition = ast.type === ":=";
            const semanticElaboration = semanticDefinition
                || hasSemanticElaborationHole(semanticTarget);
            let generalizedMetas;
            let semanticFailure;
            const semanticType = this.trySemanticTypeSynthesis(semanticTarget, context, {
                allowHoles: semanticElaboration,
                elaborateMetas: semanticElaboration,
                generalizeMetas: semanticDefinition
                    && !!beforeInferResolution
                    && !hasSemanticElaborationHole(semanticTarget),
                allowUnsolvedTermMetas: hasSemanticElaborationHole(semanticTarget),
                annotateTerm: !beforeInferResolution,
                requireElaboratedTerm: semanticElaboration,
                captureGeneralizedMetas: metas => { generalizedMetas = metas; },
                captureFailure: failure => { semanticFailure = failure; }
            });
            if (semanticType) {
                if (semanticTarget !== ast) {
                    ast.nodes[0].checked = semanticType;
                    ast.checked = semanticType;
                }
                if (beforeInferResolution) {
                    beforeInferResolution(ast, generalizedMetas);
                }
                Core.semanticTypeCheckFastPathHits++;
                if (beforeInferResolution && semanticPresentation && ast.checked) {
                    this.finalizeSemanticResult(ast.checked, context);
                }
                else {
                    this.finalizeSemanticResult(ast, context);
                }
                if (semanticPresentation) {
                    this.restoreSemanticPresentation(ast, semanticPresentation);
                }
                if (this.state.errormsg.length)
                    throw this.state.errormsg[0].msg;
                return ast.checked;
            }
            if (semanticFailure
                && !(semanticFailure.code === "unknown-constant"
                    && this.hasSemanticDefinitionTypeGap(semanticTarget))) {
                this.reportSemanticFailure(semanticTarget, semanticFailure);
            }
        }
        // The semantic checker is the kernel. Keep its internal status codes
        // behind the Core boundary so UI callers always receive a stable,
        // translated diagnostic.
        this.error(ast, TR("类型推断暂不支持该表达式"), true);
        throw new Error("unreachable semantic unsupported syntax");
    }
    finalizeSemanticResult(ast, context) {
        const alphaConversionIds = new Set;
        const visit = (node, nodeContext) => {
            const boundType = node.type === "L" || node.type === "P"
                || node.type === "W" || node.type === "S";
            if (boundType && node.name?.[0] === "*") {
                alphaConversionIds.add(node.bondVarId);
            }
            if (node.nodes?.[0])
                visit(node.nodes[0], nodeContext);
            if (node.nodes?.[1]) {
                visit(node.nodes[1], boundType
                    ? assignContext([node.name, node.nodes[0], node.bondVarId], nodeContext)
                    : nodeContext);
            }
            if (node.type === "var" && node.bondVarId !== Infinity) {
                const index = !node.bondVarId ? Infinity : findContextIndexByBondVarId(nodeContext, node.bondVarId, (left, right) => this.isBondVarIdEqual(left, right));
                if (index === -1) {
                    console.warn("Bound Var Leakage of id " + node.bondVarId, nodeContext);
                }
                else {
                    const bounded = findContextEntriesBeforeByName(nodeContext, index === Infinity ? node.name : nodeContext[index][0], index);
                    for (const [, , id] of bounded) {
                        if (id)
                            alphaConversionIds.add(id);
                    }
                    if (isFinite(index))
                        node.name = nodeContext[index][0];
                }
            }
            if (node.checked)
                visit(node.checked, nodeContext);
            if (!node.origin || node["desugared"])
                this.ensugar(node);
        };
        visit(ast, context);
        this.doAlphaConversionByIds(ast, context, alphaConversionIds);
    }
    static getFreeVars(ast, res = new Set, scope = new Set) {
        if (ast.type === "var" && !scope.has(ast.name)) {
            res.add(ast.name);
        }
        else if (ast.type === "L" || ast.type === "P" || ast.type === "W" || ast.type === "S") {
            this.getFreeVars(ast.nodes[0], res, scope);
            const alreadyBound = scope.has(ast.name);
            scope.add(ast.name);
            this.getFreeVars(ast.nodes[1], res, scope);
            if (!alreadyBound)
                scope.delete(ast.name);
        }
        else if (ast.nodes?.length) {
            for (const node of ast.nodes)
                this.getFreeVars(node, res, scope);
        }
        return res;
    }
    static getAllVars(ast, res = new Set) {
        if (ast.type === "var" || ast.type === "L" || ast.type === "P" || ast.type === "W" || ast.type === "S") {
            res.add(ast.name);
        }
        if (ast.nodes?.length) {
            this.getAllVars(ast.nodes[0], res);
            if (ast.nodes[1])
                this.getAllVars(ast.nodes[1], res);
        }
        return res;
    }
    static getNewName(refName, excludeSet) {
        let n = refName;
        while (excludeSet.has(n)) {
            n += "'";
        }
        return n;
    }
    doAlphaConversionByIds(ast, context, ids) {
        if ((ast.type === "L" || ast.type === "P" || ast.type === "W" || ast.type === "S") && ids.has(ast.bondVarId) && (ast.origin !== true || ast.name[0] === "*")) {
            // Lx1.Lx2. x1 Lx'.x'
            const excluded = new Set(context.map(e => e[0]));
            const k = wrapVar(Core.getNewName(ast.name[0] === "*" ? "x" : (ast.name + "'"), Core.getAllVars(ast, excluded)));
            k.checked = ast.nodes[0];
            k.bondVarId = ast.bondVarId;
            this.replaceVar(ast.nodes[1], "?", ast.bondVarId, k);
            ast.name = k.name;
            ast.origin = true;
            // ids.delete(ast.bondVarId);
        }
        if (ast.nodes?.[0])
            this.doAlphaConversionByIds(ast.nodes[0], context, ids);
        if (ast.nodes?.[1])
            this.doAlphaConversionByIds(ast.nodes[1], context, ids);
        delete ast.bondVarId;
        if (ast.checked)
            this.doAlphaConversionByIds(ast.checked, context, ids);
    }
    applySemanticTerm(target, source) {
        target.type = source.type;
        target.name = source.name;
        target.bondVarId = source.bondVarId;
        target.displayExplicitAt = source.displayExplicitAt;
        target.checked = source.checked ? Core.clone(source.checked, true) : null;
        if (!source.nodes) {
            target.nodes = undefined;
            return;
        }
        if (!target.nodes || target.nodes.length !== source.nodes.length) {
            target.nodes = source.nodes.map(node => Core.clone(node, true));
            return;
        }
        for (let index = 0; index < source.nodes.length; index++) {
            this.applySemanticTerm(target.nodes[index], source.nodes[index]);
        }
    }
    restoreSemanticPresentation(target, surface) {
        const resolvedHole = surface.type === "var"
            && (surface.name === "_" || surface.name?.startsWith("?"))
            && !(target.type === "var"
                && (target.name === "_" || target.name?.startsWith("?")))
            ? Core.clone(target, true)
            : undefined;
        const targetType = target.type;
        const checked = target.checked;
        const targetNodes = target.nodes;
        const surfaceNodes = surface.nodes;
        target.type = surface.type;
        target.name = surface.name;
        target.bondVarId = surface.bondVarId;
        target.displayExplicitAt = surface.displayExplicitAt;
        target.checked = checked;
        delete target.origin;
        delete target["desugared"];
        if (!surfaceNodes) {
            target.nodes = undefined;
            if (resolvedHole)
                target.checked = {
                    type: ":",
                    name: "",
                    nodes: [resolvedHole, Core.clone(resolvedHole.checked ?? wrapVar("_"), true)]
                };
            return;
        }
        if (targetNodes
            && targetType === surface.type
            && targetNodes.length === surfaceNodes.length) {
            target.nodes = targetNodes;
            for (let index = 0; index < surfaceNodes.length; index++) {
                this.restoreSemanticPresentation(targetNodes[index], surfaceNodes[index]);
            }
            return;
        }
        target.nodes = surfaceNodes.map(node => Core.clone(node, true));
    }
    compactSemanticOutputType(ast) {
        const compact = Core.clone(ast, true);
        const implicitAliasArities = new Map(this.opaque);
        const stack = [[compact, false]];
        while (stack.length) {
            const [node, visited] = stack.pop();
            if (visited) {
                if (node.type !== "apply")
                    continue;
                const application = this.flattenApplyList(node);
                const head = application[0];
                if (head.type !== "var" || head.bondVarId || head.name?.[0] !== "@")
                    continue;
                const alias = head.name.slice(1);
                const prefixLength = implicitAliasArities.get(alias);
                if (!prefixLength || application.length < prefixLength)
                    continue;
                Core.assign(node, wrapApply(wrapVar(alias), ...application.slice(prefixLength)), true);
                continue;
            }
            stack.push([node, true]);
            for (let index = (node.nodes?.length ?? 0) - 1; index >= 0; index--) {
                stack.push([node.nodes[index], false]);
            }
        }
        return compact;
    }
    collectSemanticSourceTypeMetas(context) {
        const scopes = new Map();
        for (let index = 0; index < context.length; index++) {
            const type = context[index][1];
            if (type?.type !== "var" || !/^\?[^:]+$/.test(type.name))
                continue;
            // Contexts are stored innermost-first. A binder's type may only
            // mention the outer entries after it, which is exactly the
            // creation scope the legacy InferTable used to retain.
            const occurrenceScope = new Set(context.slice(index + 1)
                .map(([, , id]) => id)
                .filter(isPositiveBondVarId));
            const allowed = scopes.get(type.name);
            if (!allowed) {
                scopes.set(type.name, occurrenceScope);
                continue;
            }
            // Repeated occurrences share one metavariable, so retain only the
            // binders available at every occurrence.
            for (const id of allowed) {
                if (!occurrenceScope.has(id))
                    allowed.delete(id);
            }
        }
        return Array.from(scopes, ([name, allowedBondVarIds]) => ({
            name,
            role: "type",
            allowedBondVarIds: Array.from(allowedBondVarIds)
        }));
    }
    commitSemanticSourceMetaConstraints(context, constraints) {
        if (!constraints?.length)
            return true;
        const sourceMetas = new Map(this.collectSemanticSourceTypeMetas(context)
            .map(meta => [meta.name, meta]));
        const prepared = [];
        const names = new Set();
        for (const constraint of constraints) {
            if (!/^\?[^:]+$/.test(constraint.name) || names.has(constraint.name)
                || hasSemanticElaborationHole(constraint.value))
                return false;
            const sourceMeta = sourceMetas.get(constraint.name);
            if (!sourceMeta)
                return false;
            const allowedIds = new Set(sourceMeta.allowedBondVarIds);
            const visit = (ast, bound = new Set()) => {
                if (!ast || typeof ast !== "object")
                    return false;
                if (ast.type === "var") {
                    if (ast.name === "_" || ast.name?.startsWith("?"))
                        return false;
                    if (isPositiveBondVarId(ast.bondVarId)
                        && !bound.has(ast.bondVarId)
                        && !allowedIds.has(ast.bondVarId))
                        return false;
                    return true;
                }
                const binder = ast.type === "L" || ast.type === "P"
                    || ast.type === "S" || ast.type === "W";
                if (ast.nodes?.[0] && !visit(ast.nodes[0], bound))
                    return false;
                if (ast.nodes?.[1]) {
                    const bodyBound = binder && isPositiveBondVarId(ast.bondVarId)
                        ? new Set(bound).add(ast.bondVarId)
                        : bound;
                    if (!visit(ast.nodes[1], bodyBound))
                        return false;
                }
                return true;
            };
            if (!visit(constraint.value))
                return false;
            names.add(constraint.name);
            prepared.push(constraint);
        }
        // Commit only after every constraint has passed scope validation.
        // The proof goal owns this context, so replacing its type metavariable
        // gives subsequent semantic checks the same refinement without a
        // mutable global unification table.
        for (const constraint of prepared) {
            for (const [, type] of context) {
                if (type?.type === "var" && type.name === constraint.name) {
                    Core.assign(type, Core.clone(constraint.value), true);
                }
            }
        }
        return true;
    }
    trySemanticTypeAssertion(ast, context, annotateTerm, allowUnsolvedTermMetas, sourceAssertion) {
        if (ast.type !== ":")
            return;
        const term = Core.clone(ast.nodes?.[0]);
        const expected = Core.clone(ast.nodes?.[1]);
        const schematicMetaNames = collectInferenceMetaNames(expected, collectInferenceMetaNames(term));
        const sourceTerm = sourceAssertion?.type === ":"
            ? sourceAssertion.nodes?.[0]
            : undefined;
        const sourceExpected = sourceAssertion?.type === ":"
            ? sourceAssertion.nodes?.[1]
            : undefined;
        const sourceMaxNodes = Core.semanticTypeAssertionMaxNodes;
        const sourceFits = (!sourceTerm || fitsSemanticNbeBudget(sourceTerm, sourceMaxNodes, false, context, true, schematicMetaNames)) && (!sourceExpected || fitsSemanticNbeBudget(sourceExpected, sourceMaxNodes, false, context, true, schematicMetaNames));
        if (!sourceFits) {
            return (sourceTerm && exceedsSemanticNbeNodeBudget(sourceTerm, sourceMaxNodes))
                || (sourceExpected && exceedsSemanticNbeNodeBudget(sourceExpected, sourceMaxNodes))
                ? { status: "unsupported", code: "budget-exhausted" }
                : undefined;
        }
        const termMaxNodes = semanticAssertionKernelNodeBudget(sourceTerm, term, sourceMaxNodes);
        const expectedMaxNodes = semanticAssertionKernelNodeBudget(sourceExpected, expected, sourceMaxNodes);
        const kernelFits = fitsSemanticNbeBudget(term, termMaxNodes, false, context, true, schematicMetaNames) && fitsSemanticNbeBudget(expected, expectedMaxNodes, false, context, true, schematicMetaNames);
        if (!kernelFits) {
            return exceedsSemanticNbeNodeBudget(term, termMaxNodes)
                || exceedsSemanticNbeNodeBudget(expected, expectedMaxNodes)
                ? { status: "unsupported", code: "budget-exhausted" }
                : undefined;
        }
        Core.semanticTypeCheckAttempts++;
        let nextSemanticBondVarId = Math.max(this.state.bondVarId, ...context.map(([, , id]) => Number.isFinite(id) ? id + 1 : 0));
        const options = {
            deadline: this.state.time ? this.state.time + Core.timeout : undefined,
            maxSteps: Core.semanticTypeAssertionMaxSteps,
            elaborateMetas: true,
            annotateTerm,
            allowUnsolvedTermMetas,
            allowNamedSchematicMetas: true,
            allowGeneratedSchematicMetas: true,
            preserveKernelType: true,
            sourceMetas: this.collectSemanticSourceTypeMetas(context),
            freshBondVarId: () => nextSemanticBondVarId++
        };
        let checked = this.semanticTypeChecker.tryCheck(term, expected, context, options);
        if (checked.status === "unsupported") {
            // A dependent function assertion such as
            // `f : (Pi _:_, Goal)` needs the expected-type hole to be solved
            // from f's synthesized type. The ordinary checker quite rightly
            // refuses to finalize that conversion while the hole is rigid;
            // compare the two types in the shared NbE equality solver instead.
            const synthesized = this.semanticTypeChecker.trySynthesize(term, context, options);
            if (synthesized.status === "success") {
                const equality = this.semanticTypeChecker.tryDefinitionalEquality(synthesized.type, expected, context, options);
                if (equality.status === "success") {
                    checked = {
                        status: "success",
                        type: equality.type,
                        ...(synthesized.term ? { term: synthesized.term } : {}),
                        ...(equality.rightTerm
                            ? { expectedTerm: equality.rightTerm }
                            : {}),
                        ...(equality.generalizedMetas?.length
                            ? { generalizedMetas: equality.generalizedMetas }
                            : {}),
                        ...(equality.schematicMetaNames?.length
                            ? { schematicMetaNames: equality.schematicMetaNames }
                            : {}),
                        ...(synthesized.sourceMetaConstraints?.length
                            ? { sourceMetaConstraints: synthesized.sourceMetaConstraints }
                            : equality.sourceMetaConstraints?.length
                                ? { sourceMetaConstraints: equality.sourceMetaConstraints }
                                : {})
                    };
                }
                else if (equality.status === "invalid") {
                    return false;
                }
                else if (equality.code === "budget-exhausted") {
                    return equality;
                }
            }
            else if (synthesized.code === "budget-exhausted") {
                return synthesized;
            }
        }
        if (checked.status !== "success") {
            if (checked.code === "budget-exhausted")
                return checked;
            return checked.status === "invalid" ? false : undefined;
        }
        const returnedSchematicMetaNames = new Set(checked.schematicMetaNames ?? []);
        if (!fitsSemanticNbeBudget(checked.type, expectedMaxNodes, false, context, false, returnedSchematicMetaNames)) {
            return exceedsSemanticNbeNodeBudget(checked.type, expectedMaxNodes) ? { status: "unsupported", code: "budget-exhausted" } : undefined;
        }
        if (!this.commitSemanticSourceMetaConstraints(context, checked.sourceMetaConstraints))
            return;
        Core.semanticTypeCheckHits++;
        if (checked.expectedTerm)
            this.applySemanticTerm(ast.nodes[1], checked.expectedTerm);
        if (checked.term)
            this.applySemanticTerm(ast.nodes[0], checked.term);
        const returnedIds = new Set();
        collectAstBondVarIds(checked.expectedTerm, returnedIds);
        collectAstBondVarIds(checked.type, returnedIds);
        let nextReturnedId = 0;
        for (const id of returnedIds)
            nextReturnedId = Math.max(nextReturnedId, id + 1);
        this.state.bondVarId = Math.max(nextSemanticBondVarId, nextReturnedId);
        ast.checked = ast.nodes[1];
        return {
            checked: ast.checked,
            ...(checked.generalizedMetas?.length
                ? { generalizedMetas: checked.generalizedMetas }
                : {})
        };
    }
    trySemanticDefinitionalEquality(ast, context) {
        if (ast.type !== "===")
            return;
        const leftSource = Core.clone(ast.nodes?.[0]);
        const rightSource = Core.clone(ast.nodes?.[1]);
        const schematicMetaNames = collectInferenceMetaNames(rightSource, collectInferenceMetaNames(leftSource));
        if (!fitsSemanticNbeBudget(leftSource, Core.semanticTypeAssertionMaxNodes, false, context, true, schematicMetaNames) || !fitsSemanticNbeBudget(rightSource, Core.semanticTypeAssertionMaxNodes, false, context, true, schematicMetaNames)) {
            return exceedsSemanticNbeNodeBudget(leftSource, Core.semanticTypeAssertionMaxNodes)
                || exceedsSemanticNbeNodeBudget(rightSource, Core.semanticTypeAssertionMaxNodes)
                ? { status: "unsupported", code: "budget-exhausted" }
                : undefined;
        }
        Core.semanticTypeCheckAttempts++;
        let nextSemanticBondVarId = Math.max(this.state.bondVarId, ...context.map(([, , id]) => Number.isFinite(id) ? id + 1 : 0));
        const options = {
            deadline: this.state.time ? this.state.time + Core.timeout : undefined,
            maxSteps: Core.semanticTypeAssertionMaxSteps,
            elaborateMetas: true,
            annotateTerm: true,
            allowNamedSchematicMetas: true,
            allowGeneratedSchematicMetas: true,
            preserveKernelType: true,
            sourceMetas: this.collectSemanticSourceTypeMetas(context),
            freshBondVarId: () => nextSemanticBondVarId++
        };
        const equality = this.semanticTypeChecker.tryDefinitionalEquality(leftSource, rightSource, context, options);
        if (equality.status !== "success") {
            if (equality.code === "budget-exhausted")
                return equality;
            // A restored definition cache may be usable before every
            // dependency has a semantic type cache. The owner can rebuild
            // those dependency types, so absence is not proof of inequality.
            const recoverableTypeGap = equality.status === "invalid"
                && equality.code === "unknown-constant"
                && this.hasSemanticDefinitionTypeGap(leftSource, rightSource);
            return equality.status === "invalid" && !recoverableTypeGap
                ? false
                : undefined;
        }
        const compactType = this.compactSemanticOutputType(equality.type);
        const returnedSchematicMetaNames = new Set(equality.schematicMetaNames ?? []);
        if (!fitsSemanticNbeBudget(compactType, Core.semanticTypeCheckMaxOutputNodes, false, context, false, returnedSchematicMetaNames)) {
            return exceedsSemanticNbeNodeBudget(compactType, Core.semanticTypeCheckMaxOutputNodes) ? { status: "unsupported", code: "budget-exhausted" } : undefined;
        }
        if (!this.commitSemanticSourceMetaConstraints(context, equality.sourceMetaConstraints))
            return;
        Core.semanticTypeCheckHits++;
        if (equality.leftTerm)
            this.applySemanticTerm(ast.nodes[0], equality.leftTerm);
        if (equality.rightTerm)
            this.applySemanticTerm(ast.nodes[1], equality.rightTerm);
        this.state.bondVarId = Math.max(this.state.bondVarId, nextSemanticBondVarId);
        ast.checked = compactType;
        return ast.checked;
    }
    /** Directional type-pattern matching for #t gates. Candidate ?metas are
     * local to this read-only NbE request. */
    semanticTypePatternMatch(candidate, target, context = []) {
        const candidateSource = this.desugar(Core.clone(candidate), false);
        const targetSource = this.desugar(Core.clone(target), false);
        let nextId = Math.max(1, ...context.map(([, , id]) => isPositiveBondVarId(id) ? id + 1 : 1));
        const preparedCandidate = prepareSemanticTypePattern(candidateSource, context, nextId, true);
        nextId = preparedCandidate.nextId;
        const preparedTarget = prepareSemanticTypePattern(targetSource, context, nextId, false);
        nextId = preparedTarget.nextId;
        if (!fitsSemanticNbeBudget(candidateSource, Core.semanticTypeAssertionMaxNodes, false, context, false, new Set(preparedCandidate.sourceMetas.map(meta => meta.name))) || !fitsSemanticNbeBudget(targetSource, Core.semanticTypeAssertionMaxNodes, false, context))
            return false;
        const result = this.semanticTypeChecker.tryDefinitionalEquality(candidateSource, targetSource, context, {
            maxSteps: Core.semanticTypeAssertionMaxSteps,
            deadline: Date.now() + Core.timeout,
            elaborateMetas: true,
            preserveKernelType: true,
            sourceMetas: preparedCandidate.sourceMetas,
            freshBondVarId: () => nextId++
        });
        return result.status === "success";
    }
    hasSemanticDefinitionTypeGap(...roots) {
        const visited = new WeakSet();
        const stack = [...roots];
        while (stack.length) {
            const node = stack.pop();
            if (!node || typeof node !== "object" || visited.has(node))
                continue;
            visited.add(node);
            if (node.type === "var" && !node.bondVarId
                && this.semanticKernel.getDefinitionSource(node.name)
                && !this.semanticTypeChecker.hasConstantType(node.name)) {
                return true;
            }
            for (const child of node.nodes ?? [])
                stack.push(child);
        }
        return false;
    }
    /**
     * Proof-assistant substitution can retain an obsolete positive binder ID
     * below a cloned binder. Repair only those orphaned occurrences on a
     * throwaway AST; id-less same-name constants must remain free.
     */
    prepareSemanticProofAssistantNormalizeAst(ast, context) {
        const prepared = Core.clone(ast);
        const contextScope = context
            .filter(([, , id]) => isPositiveBondVarId(id))
            .map(([name, , id]) => ({ name, sourceId: id, id }));
        const visit = (node, scope) => {
            if (!node || typeof node !== "object")
                return;
            if (node.type === "var") {
                if (!isPositiveBondVarId(node.bondVarId)
                    || scope.some(binding => binding.id === node.bondVarId))
                    return;
                const replacement = scope.find(binding => binding.name === node.name);
                if (replacement)
                    node.bondVarId = replacement.id;
                return;
            }
            const binder = node.type === "L" || node.type === "P"
                || node.type === "S" || node.type === "W";
            if (!binder) {
                for (const child of node.nodes ?? [])
                    visit(child, scope);
                return;
            }
            visit(node.nodes?.[0], scope);
            const bodyScope = isPositiveBondVarId(node.bondVarId)
                ? [{ name: node.name, sourceId: node.bondVarId, id: node.bondVarId }, ...scope]
                : scope;
            visit(node.nodes?.[1], bodyScope);
        };
        visit(prepared, contextScope);
        return prepared;
    }
    trySemanticProofAssistantNormalize(ast, context) {
        const semanticAst = this.prepareSemanticProofAssistantNormalizeAst(ast, context);
        if (!fitsSemanticNbeBudget(semanticAst, Core.semanticTypeAssertionMaxNodes, false, context))
            return false;
        Core.semanticWhnfAttempts++;
        let nextSemanticBondVarId = Math.max(this.state.bondVarId, ...context.map(([, , id]) => Number.isFinite(id) ? id + 1 : 0));
        const normalized = this.semanticKernel.tryNormalize(semanticAst, context, {
            deadline: this.state.time ? this.state.time + Core.timeout : undefined,
            maxSteps: Core.semanticTypeAssertionMaxSteps,
            unfoldDefinitions: false,
            freshBondVarId: () => nextSemanticBondVarId++
        });
        if (!normalized)
            return false;
        Core.semanticWhnfHits++;
        this.state.bondVarId = nextSemanticBondVarId;
        const checked = ast.checked;
        Core.assign(ast, normalized, true);
        ast.checked = checked;
        return true;
    }
    /** Normalize a proof goal after an explicit expansion without asking the
     * type synthesizer to re-prove the whole (potentially very large) goal.
     * The replacement body is already kernel-checked in its definition cache;
     * this pass performs only local beta/iota computation introduced by the
     * substitution and keeps unrelated named definitions opaque. */
    normalizeExpandedProofGoal(ast, context) {
        const deadline = Date.now() + Core.timeout;
        let nextSemanticBondVarId = Math.max(this.state.bondVarId, ...context.map(([, , id]) => Number.isFinite(id) ? id + 1 : 0));
        const visit = (node, nodeContext) => {
            if (!node || typeof node !== "object")
                return;
            if (node.type === "apply") {
                let head = node;
                while (head.type === "apply")
                    head = head.nodes?.[0];
                if (head?.type === "L") {
                    const normalized = this.semanticKernel.tryWhnf(node, nodeContext, {
                        deadline,
                        maxSteps: Core.semanticTypeAssertionMaxSteps,
                        unfoldDefinitions: false,
                        freshBondVarId: () => nextSemanticBondVarId++
                    });
                    if (normalized)
                        Core.assign(node, normalized, true);
                }
            }
            const binder = node.type === "L" || node.type === "P"
                || node.type === "S" || node.type === "W";
            if (node.nodes?.[0])
                visit(node.nodes[0], nodeContext);
            if (node.nodes?.[1])
                visit(node.nodes[1], binder
                    ? assignContext([node.name, node.nodes[0], node.bondVarId], nodeContext)
                    : nodeContext);
        };
        visit(ast, context);
        this.state.bondVarId = Math.max(this.state.bondVarId, nextSemanticBondVarId);
        this.finalizeSemanticResult(ast, context);
        return ast;
    }
    trySemanticTypeSynthesis(ast, context, options = {}) {
        const allowHoles = options.allowHoles ?? false;
        const semanticAst = Core.clone(ast);
        const requestedElaboration = options.elaborateMetas ?? false;
        // A bare reference to a polymorphic definition has no use-site
        // arguments that could solve its cached scheme metas. Returning the
        // safely generalized type is still a complete synthesis result. Keep
        // applications and user-written holes strict.
        const generalizeMetas = !!options.generalizeMetas
            || this.isBareGeneralizedDefinitionReference(semanticAst);
        const canTryWithoutElaboration = requestedElaboration
            && fitsSemanticNbeBudget(semanticAst, Core.semanticNbEMaxNodes, false, context, false);
        const maxNodes = canTryWithoutElaboration
            ? Core.semanticNbEMaxNodes
            : requestedElaboration
                ? Core.semanticTypeElaborationMaxNodes
                : Core.semanticNbEMaxNodes;
        if (!canTryWithoutElaboration
            && !fitsSemanticNbeBudget(semanticAst, maxNodes, false, context, allowHoles)) {
            if (exceedsSemanticNbeNodeBudget(semanticAst, maxNodes)) {
                options.captureFailure?.({
                    status: "unsupported",
                    code: "budget-exhausted"
                });
            }
            return;
        }
        Core.semanticTypeCheckAttempts++;
        let nextSemanticBondVarId = Math.max(this.state.bondVarId, ...context.map(([, , id]) => Number.isFinite(id) ? id + 1 : 0));
        const checkerOptions = {
            deadline: this.state.time ? this.state.time + Core.timeout : undefined,
            maxSteps: Core.semanticTypeSynthesisMaxSteps,
            annotateTerm: options.annotateTerm ?? false,
            generalizeMetas,
            allowUnsolvedTermMetas: options.allowUnsolvedTermMetas ?? false,
            allowGeneratedSchematicMetas: true,
            preserveKernelType: true,
            sourceMetas: this.collectSemanticSourceTypeMetas(context),
            freshBondVarId: () => nextSemanticBondVarId++
        };
        // Public aliases can contain implicit holes in their definitions even
        // when the user's term is already complete. Their cached type schemes
        // are sufficient for synthesis; expanding every alias first only
        // creates a large, unrelated metavariable graph. Retry with full
        // elaboration only when the hole-free pass cannot validate the term.
        // The cheap probe may assign binder ids and elaboration metadata even
        // when it ultimately falls back. Keep the full elaboration input
        // pristine so a successful first probe cannot poison its retry.
        const initialSemanticAst = canTryWithoutElaboration
            ? Core.clone(semanticAst)
            : semanticAst;
        let semanticType = this.semanticTypeChecker.trySynthesize(initialSemanticAst, context, {
            ...checkerOptions,
            elaborateMetas: canTryWithoutElaboration ? false : requestedElaboration
        });
        const mayNeedElaborationDefinition = (canTryWithoutElaboration
            && !!options.requireElaboratedTerm)
            || (!requestedElaboration && semanticType.status !== "success");
        const hasElaborationDefinition = mayNeedElaborationDefinition
            && this.semanticTypeChecker.hasElaborationDefinitionReference(semanticAst);
        const needsElaboratedTerm = canTryWithoutElaboration
            && !!options.requireElaboratedTerm
            && hasElaborationDefinition;
        const needsDefinitionElaboration = !requestedElaboration
            && semanticType.status !== "success"
            && hasElaborationDefinition;
        if ((canTryWithoutElaboration
            && (semanticType.status !== "success" || needsElaboratedTerm))
            || needsDefinitionElaboration) {
            const elaborated = this.semanticTypeChecker.trySynthesize(semanticAst, context, {
                ...checkerOptions,
                elaborateMetas: true,
                // A complete user term can still depend on public definitions
                // whose bodies contain inference-only holes.  Reaching and
                // solving those hidden metas costs more than ordinary syntax-
                // directed synthesis, so give this rare fallback a larger but
                // still bounded budget under the same wall-clock deadline.
                maxSteps: needsDefinitionElaboration
                    ? Core.semanticTypeSynthesisMaxSteps * 4
                    : Core.semanticTypeSynthesisMaxSteps
            });
            if (elaborated.status === "success")
                semanticType = elaborated;
            else if (semanticType.status !== "success" || needsElaboratedTerm) {
                let failure = elaborated;
                if (elaborated.status !== "invalid"
                    && elaborated.code === "budget-exhausted"
                    && semanticType.status !== "success"
                    && (semanticType.status === "invalid"
                        || semanticType.code !== "budget-exhausted")) {
                    failure = semanticType;
                }
                options.captureFailure?.(failure);
                return;
            }
        }
        if (semanticType.status !== "success") {
            options.captureFailure?.(semanticType);
            return;
        }
        if (needsElaboratedTerm && !semanticType.term)
            return;
        const generalizedMetaNames = new Set(semanticType.generalizedMetas?.map(meta => meta.name) ?? []);
        for (const name of semanticType.schematicMetaNames ?? []) {
            if (name.startsWith("?"))
                generalizedMetaNames.add(name);
        }
        // The kernel returns explicit applications such as @eq/@pair.  Fold
        // only their known implicit prefixes back to the internal public
        // aliases used by legacy caches.  This keeps binder shapes and kernel
        // syntax intact while removing elaboration-only arguments.
        // Keep this pre-pass bounded: genuinely huge reifications must still
        // fail before cloning or traversing their complete output.
        if (!fitsSemanticNbeBudget(semanticType.type, Math.max(Core.semanticNbEMaxNodes, Core.semanticTypeCheckMaxOutputNodes), false, context, false, generalizedMetaNames)) {
            if (exceedsSemanticNbeNodeBudget(semanticType.type, Math.max(Core.semanticNbEMaxNodes, Core.semanticTypeCheckMaxOutputNodes))) {
                options.captureFailure?.({
                    status: "unsupported",
                    code: "budget-exhausted"
                });
            }
            return;
        }
        const compactType = this.compactSemanticOutputType(semanticType.type);
        if (!fitsSemanticNbeBudget(compactType, Core.semanticTypeCheckMaxOutputNodes, false, context, false, generalizedMetaNames)) {
            if (exceedsSemanticNbeNodeBudget(compactType, Core.semanticTypeCheckMaxOutputNodes)) {
                options.captureFailure?.({
                    status: "unsupported",
                    code: "budget-exhausted"
                });
            }
            return;
        }
        if (!this.commitSemanticSourceMetaConstraints(context, semanticType.sourceMetaConstraints))
            return;
        Core.semanticTypeCheckHits++;
        options.captureElaboratedTerm?.(semanticType.elaboratedTerm);
        if (semanticType.term)
            this.applySemanticTerm(ast, semanticType.term);
        const returnedIds = new Set();
        collectAstBondVarIds(compactType, returnedIds);
        let nextReturnedId = 0;
        for (const id of returnedIds)
            nextReturnedId = Math.max(nextReturnedId, id + 1);
        this.state.bondVarId = Math.max(nextSemanticBondVarId, nextReturnedId);
        ast.checked = compactType;
        options.captureGeneralizedMetas?.(semanticType.generalizedMetas);
        return ast.checked;
    }
    semanticTypeFailureMessage(code, ast) {
        const subject = this.printSemanticErrorAst(ast);
        switch (code) {
            case "budget-exhausted":
                return TR("类型推断资源超限") + ": " + subject;
            case "unknown-constant":
                return TR("未知的变量：") + subject;
            case "unbound-variable":
                return TR("本应约束的变量在类型推断时自由出现：") + subject;
            case "expected-universe":
                return TR("函数参数类型不合法") + ": " + subject;
            case "expected-function":
                return TR("非函数尝试作用") + ": " + subject;
            case "argument-type-mismatch":
            case "type-mismatch":
                return TR("函数作用类型不匹配") + ": " + subject;
            case "unsupported-syntax":
                return TR("类型推断暂不支持该表达式") + ": " + subject;
            case "metavariable":
                return TR("类型推断中仍有未确定的占位符") + ": " + subject;
            case "conversion-unsupported":
                return TR("类型推断无法判定类型是否相等") + ": " + subject;
            default:
                return TR("类型推断错误：") + code + ": " + subject;
        }
    }
    reportSemanticFailure(ast, failure) {
        if (failure.code === "budget-exhausted") {
            return this.reportSemanticBudgetFailure(ast);
        }
        this.error(ast, this.semanticTypeFailureMessage(failure.code, ast), true);
        throw new Error("unreachable semantic failure");
    }
    reportSemanticBudgetFailure(ast) {
        if (this.state.time && Date.now() - this.state.time >= Core.timeout) {
            Core.timeoutOccured = true;
        }
        this.error(ast, this.semanticTypeFailureMessage("budget-exhausted", ast), true);
        throw new Error("unreachable semantic budget failure");
    }
    printSemanticErrorAst(ast) {
        const surface = this.displaySurfaceNodes.get(ast);
        const printable = Core.clone(surface ?? ast);
        const visited = new WeakSet();
        const hideInferenceNames = (node) => {
            if (!node || typeof node !== "object" || visited.has(node))
                return;
            visited.add(node);
            if (node.type === "var" && !node.bondVarId && node.name?.startsWith("?")) {
                node.name = "_";
            }
            for (const child of node.nodes ?? [])
                hideInferenceNames(child);
            if (node.checked)
                hideInferenceNames(node.checked);
        };
        hideInferenceNames(printable);
        return parser.stringify(compactImplicitAliasesForDisplay(printable, this.opaque, new Set()));
    }
    semanticErrorUnresolvedDefinitions(ast) {
        const names = new Set();
        const visited = new WeakSet();
        const visit = (node) => {
            if (!node || typeof node !== "object" || visited.has(node))
                return;
            visited.add(node);
            if (node.type === "var" && !node.bondVarId) {
                const source = this.semanticKernel.getDefinitionSource(node.name);
                if (source && !this.semanticKernel.hasDefinition(node.name)
                    && collectInferenceMetaNames(source).size) {
                    names.add(node.name);
                }
            }
            for (const child of node.nodes ?? [])
                visit(child);
        };
        visit(ast);
        return [...names];
    }
    captureDisplaySurface(source, surface) {
        this.displaySurfaceNodes = new WeakMap();
        const visited = new WeakSet();
        const visit = (node, sourceNode) => {
            if (!node || !sourceNode || typeof node !== "object" || visited.has(node))
                return;
            visited.add(node);
            this.displaySurfaceNodes.set(node, sourceNode);
            const sourceNodes = sourceNode.nodes ?? [];
            const nodes = node.nodes ?? [];
            for (let index = 0; index < Math.min(nodes.length, sourceNodes.length); index++) {
                visit(nodes[index], sourceNodes[index]);
            }
            if (node.checked && sourceNode.checked)
                visit(node.checked, sourceNode.checked);
        };
        visit(source, surface);
    }
    desugar(ast, allowModify) {
        ast.origin = !allowModify;
        if (ast.type === "[[]]") {
            ast["desugared"] = Core.clone(ast);
            Core.assign(ast, wrapApply(wrapVar("@Trunc"), wrapVar("_"), ast.nodes[0]));
        }
        if (ast.type === "[]") {
            ast["desugared"] = Core.clone(ast);
            Core.assign(ast, wrapApply(wrapVar("@ctorTrunc"), wrapVar("_"), wrapVar("_"), ast.nodes[0]));
        }
        if (ast.type === "X") {
            // const nast = parser.parse("@Prod _ _ ?A (L_:?A.?B)");
            // nast.nodes[0].nodes[1] = ast.nodes[0];
            // nast.nodes[1].nodes[0] = ast.nodes[0];
            // nast.nodes[1].nodes[1] = ast.nodes[1];
            ast.type = "S";
            ast.name = "_";
            ast["desugared"] = Core.clone(ast);
            // Core.assign(ast, nast);
        }
        if (ast.type === "+") {
            const nast = parser.parse("@Sum _ _ ?A ?B");
            nast.nodes[0].nodes[1] = ast.nodes[0];
            nast.nodes[1] = ast.nodes[1];
            ast["desugared"] = Core.clone(ast);
            Core.assign(ast, nast);
        }
        if (ast.type === ",") {
            const nast = parser.parse("pair (L_:_._) ?a ?b");
            nast.nodes[0].nodes[1] = ast.nodes[0];
            nast.nodes[1] = ast.nodes[1];
            ast["desugared"] = Core.clone(ast);
            Core.assign(ast, nast);
        }
        //  else if (ast.type === "S") {
        // const nast = parser.parse("@Prod _ _ ?a ?fn");
        // nast.nodes[1] = Core.clone(ast);
        // nast.nodes[1].type = "L";
        // Core.assign(ast, nast);
        // ast["desugared"] = Core.clone(ast);
        // ast.nodes[0].nodes[1] = ast.nodes[1].nodes[0];
        // }
        if (ast.type === "->" && !this.state.disableSimpleFn) {
            ast.type = "P";
            ast.name = "_";
            ast["desugared"] = Core.clone(ast);
        }
        if (ast.type === "*") {
            ast["desugared"] = Core.clone(ast);
            Core.assign(ast, wrapApply(wrapVar("compeq"), ...ast.nodes));
        }
        if (ast.type === "=" && !this.state.disableSimpleEq) {
            ast["desugared"] = Core.clone(ast);
            Core.assign(ast, wrapApply(wrapVar("eq"), ...ast.nodes));
        }
        if (ast.type === "~=") {
            ast["desugared"] = Core.clone(ast);
            Core.assign(ast, wrapApply(wrapVar("eqv"), ...ast.nodes));
        }
        if (ast.nodes) {
            for (const n of ast.nodes)
                this.desugar(n, allowModify);
        }
        return ast;
    }
    opaque = [];
    ensugar(ast) {
        // no recursive, outter fn will do that
        if (ast.type === "P" && !this.state.disableSimpleFn) {
            if (ast.name === "_" || !this.hasBondVar(ast.nodes[1], ast.bondVarId)) {
                ast.type = "->";
                ast.name = "";
            }
        }
        if (ast.type === "S") {
            if (ast.name === "_" || !this.hasBondVar(ast.nodes[1], ast.bondVarId)) {
                ast.type = "X";
                ast.name = "";
            }
        }
        if (ast.type === "apply") {
            const ali = this.flattenApplyList(ast);
            if (ali[0].bondVarId)
                return ast;
            const args = ali.length;
            const fn = ali[0].name;
            if (ali[0].displayExplicitAt)
                return ast;
            if (fn === "compeq" && args === 3) {
                const t = ast.checked;
                if (!(ast["desugared"] && ast["desugared"]?.type !== "*")) {
                    Core.assign(ast, { type: "*", nodes: [ali[1], ali[2]], name: "" }, true);
                }
                ast.checked = t;
                return;
            }
            if (fn === "eq" && args === 3 && !this.state.disableSimpleEq) {
                const t = ast.checked;
                if (!(ast["desugared"] && ast["desugared"]?.type !== "=")) {
                    Core.assign(ast, { type: "=", nodes: [ali[1], ali[2]], name: "" }, true);
                }
                ast.checked = t;
                return;
            }
            if (fn === "eqv" && args === 3) {
                const t = ast.checked;
                if (!(ast["desugared"] && ast["desugared"]?.type !== "~=")) {
                    Core.assign(ast, { type: "~=", nodes: [ali[1], ali[2]], name: "" }, true);
                }
                ast.checked = t;
                return;
            }
            if (fn === "@Trunc" && args === 3) {
                const t = ast.checked;
                if (!(ast["desugared"] && ast["desugared"]?.type !== "[[]]")) {
                    Core.assign(ast, { type: "[[]]", nodes: [ali[2]], name: "" }, true);
                }
                ast.checked = t;
                return;
            }
            if (fn === "@ctorTrunc" && args === 4) {
                const t = ast.checked;
                if (!(ast["desugared"] && ast["desugared"]?.type !== "[]")) {
                    Core.assign(ast, { type: "[]", nodes: [ali[3]], name: "" }, true);
                }
                ast.checked = t;
                return;
            }
            if (fn === "@Prod" && args === 5) {
                const l = ali[4];
                const t = ast.checked;
                if ((ast["desugared"] && ast["desugared"]?.type !== "X") || l.type !== "L" || this.hasBondVar(l.nodes[1], l.bondVarId)) {
                    if (l.type !== "L") {
                        const nname = l.name === "x" ? "x'" : "x";
                        Core.assign(ast, wrapLambda("S", nname, ali[3], wrapApply(l, wrapVar(nname))), true);
                        this.getBondVarId(ast);
                        ast.nodes[1].nodes[1].bondVarId = ast.bondVarId;
                    }
                    else {
                        Core.assign(ast, wrapLambda("S", l.name, l.nodes[0], l.nodes[1]), true);
                        ast.bondVarId = l.bondVarId;
                    }
                }
                else {
                    Core.assign(ast, { type: "X", nodes: l.nodes, name: "" }, true);
                }
                ast.checked = t;
                return;
            }
            if (fn === "@Sum" && args === 5) {
                const t = ast.checked;
                Core.assign(ast, { type: "+", nodes: [ali[3], ali[4]], name: "" }, true);
                ast.checked = t;
                return;
            }
            for (const [k, v] of this.opaque) {
                if (ali[0].name === "@" + k && args === v) {
                    const t = ast.checked;
                    Core.assign(ast, wrapVar(k));
                    ast.checked = t;
                    continue;
                }
            }
            if (fn === "@pair" && args === 7 && ali[4].type === "L" && (ast["desugared"]?.type === "," || !this.hasBondVar(ali[4].nodes[1], ali[4].bondVarId))) {
                const t = ast.checked;
                Core.assign(ast, { type: ",", nodes: [ali[5], ali[6]], name: "" }, true);
                ast.checked = t;
                return;
            }
            if (fn === "pair" && args === 4 && ali[1].type === "L" && (ast["desugared"]?.type === "," || !this.hasBondVar(ali[1].nodes[1], ali[1].bondVarId))) {
                const t = ast.checked;
                Core.assign(ast, { type: ",", nodes: [ali[2], ali[3]], name: "" }, true);
                ast.checked = t;
                return;
            }
        }
        return ast;
    }
    hasConst(n) {
        if (n.startsWith("?"))
            return false;
        if (this.state.sysTypes[n] || this.state.sysDefs[n] || this.state.userDefs[n]) {
            return true;
        }
        if (n[0] === "@" && NatLiteral.is(n.slice(1)))
            return true;
        return !!NatLiteral.is(n);
    }
    flattenApplyList(ast) {
        const args = [];
        let head = ast;
        while (head.type === "apply") {
            args.push(head.nodes[1]);
            head = head.nodes[0];
        }
        args.reverse();
        return [head, ...args];
    }
    static exactEqual(ast1, ast2) {
        if (ast1 === ast2)
            return true;
        if (ast1.type !== ast2.type)
            return false;
        if (ast1.type === "var" && ast1.bondVarId && ast1.bondVarId !== ast2.bondVarId) {
            return false;
        }
        if (ast1.name != ast2.name)
            return false; // undefined == null but !== null
        if (ast1.nodes?.length !== ast2.nodes?.length)
            return false;
        if (ast1.nodes?.length) {
            for (let i = 0; i < ast1.nodes.length; i++) {
                if (!this.exactEqual(ast1.nodes[i], ast2.nodes[i]))
                    return false;
            }
        }
        return true;
    }
    /**
     * Definitions are stored with the binder ids from the check that created
     * them.  Those ids are only meaningful in that old lexical tree: copying
     * them into a live proof goal can make an inner binder look like a current
     * binder with the same numeric id.  Rebind a fresh clone by lexical scope
     * before inserting it into the caller.
     */
    instantiateDefinitionForExpansion(definition, context, surrounding) {
        const clone = Core.clone(definition);
        const seen = new WeakSet();
        let largestId = this.state.bondVarId - 1;
        const reserve = (node) => {
            if (!node || typeof node !== "object" || seen.has(node))
                return;
            seen.add(node);
            if (Number.isFinite(node.bondVarId) && node.bondVarId > largestId) {
                largestId = node.bondVarId;
            }
            for (const child of node.nodes ?? [])
                reserve(child);
            if (node.checked)
                reserve(node.checked);
        };
        // Existing goal/context ids remain live.  Never allocate one of them
        // for a binder copied out of a stored definition.
        reserve(surrounding);
        for (const [, type, id] of context) {
            if (Number.isFinite(id) && id > largestId)
                largestId = id;
            reserve(type);
        }
        this.state.bondVarId = Math.max(this.state.bondVarId, largestId + 1);
        const clear = (node, visited = new WeakSet()) => {
            if (!node || typeof node !== "object" || visited.has(node))
                return;
            visited.add(node);
            delete node.bondVarId;
            for (const child of node.nodes ?? [])
                clear(child, visited);
            if (node.checked)
                clear(node.checked, visited);
        };
        clear(clone);
        return this.markBondVars(clone, context);
    }
    // count: [position to expand, current position]
    expandDef(ast, context, n, count = [0, 1]) {
        let found = false;
        if (ast.type === "~=" && (n === "eqv" || (typeof n === "object" && n.has("eqv")))) {
            const expr = this.state.sysDefs["eqv"];
            if (count[0] === 0 || Math.abs(count[0]) === count[1]) {
                Core.assign(ast, wrapApply(this.instantiateDefinitionForExpansion(expr, context, ast), ...ast.nodes));
                count[1]++;
                this.expandDef(ast.nodes[0].nodes[1], context, n, count);
                this.expandDef(ast.nodes[1], context, n, count);
                return true;
            }
            else {
                count[1]++;
                found = this.expandDef(ast.nodes[0].nodes[1], context, n, count) || found;
                found = this.expandDef(ast.nodes[1], context, n, count) || found;
                return found;
            }
        }
        if (ast.type === "var" && !ast.bondVarId && (ast.name === n || (typeof n === "object" && n.has(ast.name))) && !hasContextName(context, ast.name)) {
            const expr = this.state.sysDefs[ast.name] || this.state.userDefs[ast.name];
            if (count[0] === 0 || Math.abs(count[0]) === count[1]) {
                Core.assign(ast, this.instantiateDefinitionForExpansion(expr, context, ast));
                count[1]++;
                return true;
            }
            else {
                count[1]++;
                return false;
            }
        }
        if (ast.nodes?.length) {
            if (count[0] < 0) {
                if (ast.type === "P" || ast.type === "L" || ast.type === "W" || ast.type === "S") {
                    context = assignContext([ast.name, ast.nodes[0], 0], context);
                }
                found = this.expandDef(ast.nodes[1], context, n, count) || found;
                found = this.expandDef(ast.nodes[0], context, n, count) || found;
            }
            else {
                found = this.expandDef(ast.nodes[0], context, n, count) || found;
                if (ast.type === "P" || ast.type === "L" || ast.type === "W" || ast.type === "S") {
                    context = assignContext([ast.name, ast.nodes[0], 0], context);
                }
                found = this.expandDef(ast.nodes[1], context, n, count) || found;
            }
        }
        return found;
    }
}
export class NatLiteral {
    static is(ast) {
        if (!ast)
            return false;
        return typeof ast === "string" ? ast === "0" || ast.match(/^[1-9][0-9]*$/) : ast.type === "var" && (ast.name === "0" || ast.name.match(/^[1-9][0-9]*$/));
    }
}
//# sourceMappingURL=core.js.map