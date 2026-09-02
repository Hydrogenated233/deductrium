import { TR } from "../lang.js";
import { ASTParser, AST } from "./astparser.js";
import {
    SemanticNbeTypeChecker,
    type NbeGeneralizedMeta,
    type NbeSourceMetaConstraint,
    type NbeSourceMetaInput,
    type NbeTypeErrorCode,
    type NbeTypeFailure,
    type NbeTypeSchemeMetaSnapshot,
    type NbeTypeSchemeSnapshot,
    isNbeUniverseType
} from "./nbe-checker.js";
import { SemanticNbeKernel } from "./nbe-kernel.js";
import {
    compactImplicitAliasesForDisplay,
    hasExplicitAtOccurrence
} from "./presentation.js";
import {
    findContextByName,
    findContextEntriesBeforeByName,
    findContextIndexByBondVarId,
    findContextIndexByName,
    hasContextName,
    isBinderNode,
    markScopedBondVars,
    prependContext,
    ScopeCursor,
    validBondVarId as isPositiveBondVarId,
    type Context
} from "./scoped-syntax.js";
export type { Context } from "./scoped-syntax.js";
export {
    findContextByName,
    findContextEntriesBeforeByName,
    findContextIndexByBondVarId,
    findContextIndexByName,
    hasContextName
} from "./scoped-syntax.js";
const parser = new ASTParser;

const semanticResourceBaseLimits: Readonly<{
    nbeMaxNodes: number;
    elaborationMaxNodes: number;
    synthesisMaxSteps: number;
    assertionMaxSteps: number;
    assertionMaxNodes: number;
    outputMaxNodes: number;
}> = Object.freeze({
    nbeMaxNodes: 512,
    elaborationMaxNodes: 1_024,
    synthesisMaxSteps: 8_192,
    assertionMaxSteps: 131_072,
    assertionMaxNodes: 2_048,
    outputMaxNodes: 256
});

function fitsSemanticNbeBudget(
    ast: AST,
    maxNodes: number,
    allowRigidMetas = false,
    context: Context = [],
    allowHoles = false,
    allowedMetaNames?: ReadonlySet<string>
) {
    if (!ast) return false;
    const contextIds = new Set(
        context.map(([, , id]) => id).filter(id => Number.isFinite(id) && id > 0)
    );
    const stack: [AST, boolean, Set<number>][] = [[ast, false, new Set()]];
    let count = 0;
    while (stack.length) {
        const [node, underBinder, activeIds] = stack.pop();
        if (!node || typeof node !== "object") continue;
        if (++count > maxNodes) return false;
        if (node.origin && typeof node.origin === "object") return false;
        const isAllowedMeta = node.type === "var"
            && !!node.name
            && !!allowedMetaNames?.has(node.name);
        if (node.type === "var" && ((node.name === "_" && !allowHoles)
            || (node.name?.startsWith("?")
                && !isAllowedMeta
                && (!allowRigidMetas || underBinder)))) return false;
        const isBinder = node.type === "L" || node.type === "P" || node.type === "S" || node.type === "W";
        if (node.type === "var" && node.bondVarId
            && !activeIds.has(node.bondVarId) && !contextIds.has(node.bondVarId)) return false;
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

function exceedsSemanticNbeNodeBudget(ast: AST, maxNodes: number) {
    if (!ast) return false;
    const stack = [ast];
    let count = 0;
    while (stack.length) {
        const node = stack.pop();
        if (!node || typeof node !== "object") continue;
        if (++count > maxNodes) return true;
        for (const child of node.nodes ?? []) stack.push(child);
    }
    return false;
}

function countSemanticNbeNodes(ast: AST) {
    if (!ast) return 0;
    const stack = [ast];
    let count = 0;
    while (stack.length) {
        const node = stack.pop();
        if (!node || typeof node !== "object") continue;
        count++;
        for (const child of node.nodes ?? []) stack.push(child);
    }
    return count;
}

function semanticAssertionKernelNodeBudget(
    source: AST | undefined,
    kernel: AST,
    sourceMaxNodes: number
) {
    if (!source) return sourceMaxNodes;
    // The kernel tree was produced from this exact source subtree by the
    // trusted desugarer. Keep the finite source cap and compensate only for
    // nodes introduced by that deterministic transformation.
    return sourceMaxNodes + Math.max(
        0,
        countSemanticNbeNodes(kernel) - countSemanticNbeNodes(source)
    );
}

function hasSemanticElaborationHole(ast: AST) {
    const stack = [ast];
    const seen = new WeakSet<object>();
    while (stack.length) {
        const node = stack.pop();
        if (!node || typeof node !== "object" || seen.has(node)) continue;
        seen.add(node);
        if (node.type === "var"
            && (node.name === "_" || node.name?.startsWith("?"))) return true;
        for (const child of node.nodes ?? []) stack.push(child);
    }
    return false;
}

// sugars begin

export function wrapVar(v: string): AST {
    return { type: "var", name: v };
}
function wrapU(v: string): AST {
    return { type: "apply", name: "", nodes: [wrapVar("U"), wrapVar(v)] };
}
export function wrapLambda(type: string, param: string, paramType: AST, body: AST): AST {
    return { type, name: param, nodes: [paramType, body] };
}
export function wrapApply(...terms: AST[]): AST {
    let ast = terms[0];
    for (let i = 1; i < terms.length; i++) {
        ast = { type: "apply", name: "", nodes: [ast, terms[i]] };
    }
    return ast;
}
export type Varlist = {
    [varname: string]: AST,
}
type AstCloneMemo = WeakMap<object, AST>;

/** Rebind a cloned type pattern without touching Core's mutable checker state. */
function prepareSemanticTypePattern(
    ast: AST,
    context: Context,
    firstId: number,
    collectSourceMetas: boolean
) {
    let nextId = firstId;
    const scope = new ScopeCursor();
    for (let index = context.length - 1; index >= 0; index--) {
        const [name, , sourceId] = context[index];
        if (!isPositiveBondVarId(sourceId)) continue;
        scope.push({ name, sourceId, id: sourceId });
        nextId = Math.max(nextId, sourceId + 1);
    }
    const metaScopes = new Map<string, Set<number>>();
    const visit = (node: AST): void => {
        if (!node || typeof node !== "object") return;
        if (node.type === "var") {
            if (/^\?[^:]+$/.test(node.name)) {
                if (collectSourceMetas) {
                    const occurrenceScope = new Set(scope.activeBondVarIds());
                    const allowed = metaScopes.get(node.name);
                    if (!allowed) metaScopes.set(node.name, occurrenceScope);
                    else {
                        for (const id of allowed) {
                            if (!occurrenceScope.has(id)) allowed.delete(id);
                        }
                    }
                }
                delete node.bondVarId;
                return;
            }
            const sourceId = isPositiveBondVarId(node.bondVarId) ? node.bondVarId : undefined;
            const binding = sourceId !== undefined
                ? scope.findBySourceOrId(sourceId)
                : scope.findByName(node.name);
            if (binding) node.bondVarId = binding.id;
            else delete node.bondVarId;
            return;
        }
        if (!isBinderNode(node)) {
            for (const child of node.nodes ?? []) visit(child);
            return;
        }
        visit(node.nodes?.[0]);
        const sourceId = isPositiveBondVarId(node.bondVarId) ? node.bondVarId : undefined;
        const id = nextId++;
        node.bondVarId = id;
        scope.push({ name: node.name, sourceId, id });
        visit(node.nodes?.[1]);
        scope.pop();
    };
    visit(ast);
    return {
        nextId,
        sourceMetas: Array.from(metaScopes, ([name, allowedBondVarIds]) => ({
            name,
            role: "type" as const,
            allowedBondVarIds: Array.from(allowedBondVarIds)
        }))
    };
}

/* Context indexing now lives in scoped-syntax.ts. */

/** Clone AST metadata once while preserving sharing between contexts. */
function cloneAstMemo(ast: AST, cloneChecked: boolean, memo: AstCloneMemo): AST {
    if (!ast || typeof ast !== "object") return ast;
    const previous = memo.get(ast);
    if (previous) return previous;
    const copy: AST = {
        type: ast.type,
        name: ast.name,
        checked: null,
        err: ast.err,
        bondVarId: ast.bondVarId,
        displayExplicitAt: ast.displayExplicitAt
    };
    memo.set(ast, copy);
    if (ast.nodes) copy.nodes = ast.nodes.map(node => cloneAstMemo(node, cloneChecked, memo));
    if (cloneChecked && ast.checked) copy.checked = cloneAstMemo(ast.checked, true, memo);
    return copy;
}

function collectInferenceMetaNames(ast: AST | null | undefined, result = new Set<string>()) {
    if (!ast) return result;
    const stack = [ast];
    const seen = new WeakSet<object>();
    while (stack.length) {
        const node = stack.pop();
        if (!node || typeof node !== "object" || seen.has(node)) continue;
        seen.add(node);
        if (node.type === "var" && node.name?.startsWith("?")) result.add(node.name);
        if (node.checked) stack.push(node.checked);
        for (const child of node.nodes ?? []) stack.push(child);
    }
    return result;
}

export type InferTableSnapshot = {
    list: [string, Context][],
    rel: Varlist,
    solved: string[],
    defered: [AST, AST, Context][],
    nextName: number
};
type DisjointSetSnapshot = {
    parent: [number, number][],
    size: [number, number][]
};
export type LegacyDefinitionTypeCacheSnapshot = {
    kind?: "legacy",
    type: AST,
    inferTable: InferTableSnapshot,
    bondVarRel: DisjointSetSnapshot,
    bondVarId: number
};
export type SemanticDefinitionTypeCacheSnapshot = NbeTypeSchemeSnapshot & {
    kind: "nbe",
    bondVarId: number
};
export type DefinitionTypeCacheSnapshot =
    | LegacyDefinitionTypeCacheSnapshot
    | SemanticDefinitionTypeCacheSnapshot;

function normalizeSchemeMetaName(name: string) {
    return name.replace(/^\?/, "").replace(/:+$/, "");
}

function isSemanticDefinitionCacheSnapshot(
    cache: unknown
): cache is SemanticDefinitionTypeCacheSnapshot {
    if (!cache || typeof cache !== "object") return false;
    const candidate = cache as Partial<SemanticDefinitionTypeCacheSnapshot>;
    return candidate.kind === "nbe"
        && !!candidate.type
        && typeof candidate.type.type === "string"
        && Array.isArray(candidate.metas)
        && candidate.metas.every(meta => !!meta && typeof meta.name === "string")
        && Number.isFinite(candidate.bondVarId);
}

function cloneSemanticDefinitionCache(
    cache: SemanticDefinitionTypeCacheSnapshot
): SemanticDefinitionTypeCacheSnapshot {
    const memo: AstCloneMemo = new WeakMap();
    const metas: NbeTypeSchemeMetaSnapshot[] = cache.metas.map(meta => ({
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

function migrateLegacyDefinitionCache(
    cache: LegacyDefinitionTypeCacheSnapshot
): SemanticDefinitionTypeCacheSnapshot | null {
    const schemeInput: NbeTypeSchemeSnapshot = {
        type: Core.clone(cache.type),
        metas: cache.inferTable.list.map(([rawName, context]) => {
            // Context-dependent legacy metas need the old unifier's closure
            // representation. They are not safe to flatten into a portable
            // native scheme; callers can re-infer the definition source.
            if (context.length) return null;
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
        || cache.bondVarRel.size.some(([, size]) => size > 1)) return null;
    const referenced = collectInferenceMetaNames(schemeInput.type);
    for (const meta of schemeInput.metas) {
        if (meta.expectedType) collectInferenceMetaNames(meta.expectedType, referenced);
        if (meta.preset) collectInferenceMetaNames(meta.preset, referenced);
    }
    const declared = new Set(schemeInput.metas.map(meta => normalizeSchemeMetaName(meta.name)));
    if ([...referenced].some(name => !declared.has(normalizeSchemeMetaName(name)))) return null;
    return {
        kind: "nbe",
        type: schemeInput.type,
        metas: schemeInput.metas,
        bondVarId: cache.bondVarId
    };
}

function collectAstBondVarIds(ast: AST, result: Set<number>) {
    const seen = new WeakSet<object>();
    const stack = [ast];
    while (stack.length) {
        const current = stack.pop();
        if (!current || typeof current !== "object" || seen.has(current)) continue;
        seen.add(current);
        if (Number.isFinite(current.bondVarId) && current.bondVarId > 0) {
            result.add(current.bondVarId);
        }
        if (current.checked) stack.push(current.checked);
        for (const node of current.nodes ?? []) stack.push(node);
    }
}

type State = {
    /** system prime constants and their types */
    sysTypes: Varlist;
    /** system defined constants and their values */
    sysDefs: Varlist;
    /** user defined constants and their values */
    userDefs: Varlist;
    /** cache table for check const */
    defTypes: { [name: string]: SemanticDefinitionTypeCacheSnapshot };
    /** all compute rules here, e.g. { "indnat": {pattern:["_","#C","#0","#succ","succ #n"],result:"#succ #n (indnat #C #0 #succ #n)"} } */
    computeRules: { [ctor: string]: { pattern: AST[], result: AST }[] };
    bondVarId: number;
    /** errormsg in ast tree */
    errormsg: { ast: AST, msg: string }[];
    disableSimpleFn?: boolean;
    disableSimpleEq?: boolean;
    time?: number;
}

/** A body-less system entry installed as one trusted unit.  Sandbox ordinary
 * inductive declarations lower to these entries before they reach the Core;
 * keeping the bundle shape here avoids teaching the checker about UI state. */
export type CoreSystemInductiveBundle = {
    /** The inductive type constant and its type (normally `U` or `Uu`). */
    type: readonly [name: string, type: AST];
    /** Hidden universe-polymorphic entries such as `@ind_tri`. */
    auxiliaryTypes?: readonly (readonly [name: string, type: AST])[];
    /** Constructor constants, in source order. */
    constructors: readonly (readonly [name: string, type: AST])[];
    /** The dependent eliminator constant, if one was generated. */
    eliminator?: readonly [name: string, type: AST];
    /** The non-dependent recursor constant, if one was generated. */
    recursor?: readonly [name: string, type: AST];
    /** Optional transparent aliases, kept separate from body-less types. */
    definitions?: readonly (readonly [name: string, definition: AST])[];
    /** Iota rules keyed by their head constant (`ind_tri`, for example). */
    computeRules?: Readonly<Record<string, readonly { pattern: AST[]; result: AST }[]>>;
    /** Metadata consumed by proof-assistant destruct/induction helpers. */
    metadata?: {
        /** Version 2 distinguishes uniform parameters from family indices. */
        version?: number;
        /** Ordinary inductive data or a first-order higher inductive type. */
        kind?: "inductive" | "hit1" | "hit2";
        /** Highest path dimension represented by this metadata. */
        dimension?: number;
        typeName: string;
        parameterCount?: number;
        indexCount?: number;
        indices?: readonly { name: string; type: AST }[];
        eliminatorName: string;
        /** Universe-polymorphic eliminator used when the motive is above U0. */
        fullEliminatorName?: string;
        recursorName?: string;
        /** Universe-polymorphic recursor paired with `fullEliminatorName`. */
        fullRecursorName?: string;
        constructors: readonly {
            name: string;
            argumentTypes: AST[];
            resultIndices?: AST[];
        }[];
        /**
         * Path constructors are eliminator coherence data, not point/data
         * constructors. Their constants are installed separately (normally as
         * auxiliary types), and this metadata never creates definitional
         * compute rules for them.
         */
        pathConstructors?: readonly {
            name: string;
            argumentTypes: AST[];
            left: AST;
            right: AST;
            computationName?: string;
        }[];
        twoPathConstructors?: readonly {
            name: string;
            argumentTypes: AST[];
            left: AST;
            right: AST;
            leftPath: string;
            rightPath: string;
            computationName?: string;
        }[];
    };
}

type RegisteredInductiveMetadata = NonNullable<CoreSystemInductiveBundle["metadata"]> & {
    /** Uniform arguments needed to form an inhabitant type such as `List2 A`. */
    parameters: readonly { name: string; type: AST }[];
    indices: readonly { name: string; type: AST }[];
};

type RegisteredSystemInductive = {
    names: string[];
    previousTypes: Map<string, AST | undefined>;
    previousDefinitions: Map<string, AST | undefined>;
    previousRules: Map<string, { pattern: AST[]; result: AST }[] | undefined>;
    metadata?: RegisteredInductiveMetadata;
};

function sameGeneratedAst(left: AST, right: AST): boolean {
    if (left === right) return true;
    if (!left || !right || left.type !== right.type || left.name !== right.name) return false;
    const leftNodes = left.nodes ?? [];
    const rightNodes = right.nodes ?? [];
    return leftNodes.length === rightNodes.length
        && leftNodes.every((node, index) => sameGeneratedAst(node, rightNodes[index]));
}

function generatedEqualityEndpoints(ast: AST): readonly [AST, AST] | undefined {
    if (ast.type === "=" && ast.nodes?.[0] && ast.nodes?.[1]) {
        return [ast.nodes[0], ast.nodes[1]];
    }
    const arguments_: AST[] = [];
    let head = ast;
    while (head.type === "apply" && head.nodes?.[0] && head.nodes?.[1]) {
        arguments_.push(head.nodes[1]);
        head = head.nodes[0];
    }
    arguments_.reverse();
    if (head.type !== "var" || (head.name !== "eq" && head.name !== "@eq")
        || arguments_.length < 2) return undefined;
    return [arguments_[arguments_.length - 2], arguments_[arguments_.length - 1]];
}

type DefinitionCacheInspection = {
    type: AST;
    semantic?: SemanticDefinitionTypeCacheSnapshot;
};

type SemanticTypeAssertionResult = {
    checked: AST;
    generalizedMetas?: readonly NbeGeneralizedMeta[];
};
type SemanticTypeAttempt<T> = T | false | NbeTypeFailure | undefined;

function isNbeTypeFailure(value: unknown): value is NbeTypeFailure {
    if (!value || typeof value !== "object") return false;
    const status = (value as NbeTypeFailure).status;
    return status === "invalid" || status === "unsupported";
}
/** return a cloned Context */
export function assignContext(added: [string, AST, number], oldContext: Context) {
    return prependContext(added, oldContext);
}

export class Core {
    static timeout:number = 10_000;
    static timeoutOccured:boolean;
    /** Enable recursive semantic synthesis. */
    static semanticTypeCheckRecursive = false;
    /** Automatically use recursive synthesis once a large theorem library is loaded. */
    static semanticTypeCheckRecursiveMinDefinitions = 48;
    static semanticResourceScale = 1;
    static readonly semanticResourceScaleMin = 1;
    static readonly semanticResourceScaleMax = 64;
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

    static setSemanticResourceScale(value: unknown) {
        const numeric = Number(value);
        const scale = Number.isFinite(numeric)
            ? Math.min(
                Core.semanticResourceScaleMax,
                Math.max(Core.semanticResourceScaleMin, Math.floor(numeric))
            )
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
    private displaySurfaceNodes = new WeakMap<object, AST>();
    private silentErrors = 0;
    static assign(ast: AST, value: AST, moveSemantic?: boolean) {
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
    static match(ast: AST, pattern: AST, regexp: RegExp, res: { [variable: string]: AST } = {}) {
        if (pattern.type === "var" && pattern.name.match(regexp)) {
            res[pattern.name] ??= ast;
            if (!this.exactEqual(ast, res[pattern.name])) return null;
            return res;
        }
        if (NatLiteral.is(ast) && pattern.nodes?.[0].name === "succ") {
            if (ast.name !== "0") return this.match(
                wrapVar(String(BigInt(ast.name) - 1n)), pattern.nodes[1], regexp, res
            );
        }
        if (ast.type !== pattern.type) return null;
        if (ast.nodes?.length !== pattern.nodes?.length) return null;
        if (ast.nodes?.length) {
            for (let i = 0; i < ast.nodes.length; i++) {
                if (!this.match(ast.nodes[i], pattern.nodes[i], regexp, res)) return null;
            }
        }
        if (ast.name !== pattern.name) return null;
        return res;
    }
    static clone(ast: AST, cloneChecked?: boolean): AST {
        const checked = (cloneChecked && ast.checked) ? this.clone(ast.checked) : null;
        const newast: AST = {
            type: ast.type, name: ast.name, checked, err: ast.err, bondVarId: ast.bondVarId,
            displayExplicitAt: ast.displayExplicitAt
        };
        if (ast.nodes) {
            newast.nodes = ast.nodes.map(p => this.clone(p, cloneChecked));
        }
        return newast;
    }
    static replaceByMatch(ast: AST, res: Varlist, regexp: RegExp): boolean {
        if (!res) throw TR("未匹配");
        if (!ast) return; // here not panic because aftercheck need it
        if (ast.type === "var" && ast.name.match(regexp)) {
            if (!res[ast.name]) return false;
            this.assign(ast, this.clone(res[ast.name]));
            return true;
        } else if (ast.nodes?.length) {
            let modified = false;
            for (const n of ast.nodes) {
                if (this.replaceByMatch(n, res, regexp)) modified = true;
            }
            return modified;
        }
    }
    static cloneContext(c: Context): Context {
        return c.map(e => [e[0], e[1] ? this.clone(e[1]) : null, e[2]]);
    }
    hasBondVar(ast: AST, id: number) {
        if (!ast) return false;
        if (ast.type === "var") {
            if (ast.name === "_" && ast.checked?.type === ":") {
                return this.hasBondVar(ast.checked.nodes[0], id);
            }
            return this.isBondVarIdEqual(ast.bondVarId, id);
        } else if (ast.nodes?.length) {
            return this.hasBondVar(ast.nodes[0], id) || this.hasBondVar(ast.nodes[1], id);
        }
    }
    // mark bonvar ids for an ast
    markBondVars(ast: AST, context: Context) {
        return markScopedBondVars(ast, context, () => this.state.bondVarId++);
    }
    // we didnt mark bondvar's with id, need do it
    getBondVarId(ast: AST) {
        if (ast.bondVarId) return ast.bondVarId;
        ast.bondVarId = this.state.bondVarId++;
        return ast.bondVarId;
    }
    isBondVarIdEqual(m: number, n: number) {
        return isPositiveBondVarId(m) && m === n;
    }
    // return whether ast has changed 
    // if bondvarId == -1, it will exact match name, e.g. inferval
    replaceVar(ast: AST, name: string, bondvarId: number, dst: AST, context?: Context): boolean {
        if (name === "_") return false;
        if (ast.checked) this.replaceVar(ast.checked, name, bondvarId, dst, context);
        if (ast.type === "var") {
            // x[y->_] -> x
            // naive approach: if (ast.name !== name) return false; this cannot deal with alpha conversion
            if (bondvarId === -1 ? ast.name !== name : !this.isBondVarIdEqual(ast.bondVarId, bondvarId)) return false;
            // x[x->_] -> _
            Core.assign(ast, dst); if (dst.checked) ast.checked = Core.clone(dst.checked); return true;
        } else if (ast.type === "L" || ast.type === "P" || ast.type === "W" || ast.type === "S") {
            // replace node[0] type first : #rp(Lx:A,...) -> Lx:#rp(A), ...
            const head = this.replaceVar(ast.nodes[0], name, bondvarId, dst, context);
            // (Lx.x)[x->_] = (Lx.x) not changed
            // if (ast.name === name) return head;// bounded
            return this.replaceVar(ast.nodes[1], name, bondvarId, dst, context) || head;
        } else if (ast.nodes?.length === 2) {
            const a = this.replaceVar(ast.nodes[0], name, bondvarId, dst, context);
            const b = ast.nodes[1] ? this.replaceVar(ast.nodes[1], name, bondvarId, dst, context) : false;
            return a || b;
        }
        return false;
    }
    readonly semanticKernel = new SemanticNbeKernel();
    readonly semanticTypeChecker = new SemanticNbeTypeChecker(this.semanticKernel);
    private readonly registeredSystemInductives = new Map<string, RegisteredSystemInductive>();
    private readonly inductiveMetadata = new Map<string, RegisteredInductiveMetadata>();
    state: State = {
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
    private semanticTypeCheckRecursiveActive = false;
    syncSemanticDefinitions() {
        const merged = new Map<string, AST>();
        for (const [name, definition] of Object.entries(this.state.sysDefs)) merged.set(name, definition);
        for (const [name, definition] of Object.entries(this.state.userDefs)) merged.set(name, definition);
        const count = this.semanticKernel.replaceDefinitions(merged, {
            rigidHoleDefinitions: new Set(Object.keys(this.state.userDefs))
        });
        this.syncSemanticTypes();
        return count;
    }
    syncSemanticTypes() {
        this.semanticTypeChecker.replaceConstantTypes(Object.entries(this.state.sysTypes));
        for (const [name, rawCache] of Object.entries(this.state.defTypes)) {
            if (this.state.sysTypes[name]) continue;
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
        const elaborated = new Set<string>();
        let changed = 0;
        for (let pass = 0; pass < maxPasses; pass++) {
            let passChanged = 0;
            for (const [name, rawType] of Object.entries(this.state.sysTypes)) {
                if (elaborated.has(name)) continue;
                const result = this.semanticTypeChecker.trySynthesize(
                    Core.clone(rawType),
                    [],
                    {
                        elaborateMetas: true,
                        generalizeMetas: true,
                        annotateTerm: true,
                        maxSteps: Math.max(
                            Core.semanticTypeSynthesisMaxSteps * 4,
                            65_536
                        )
                    }
                );
                if (result.status !== "success" || !result.term) continue;
                const type = Core.clone(result.term);
                this.state.sysTypes[name] = type;
                this.semanticTypeChecker.setConstantType(name, type);
                elaborated.add(name);
                passChanged++;
            }
            changed += passChanged;
            if (!passChanged) break;
        }
        return changed;
    }
    syncSemanticComputeRules() {
        return this.semanticKernel.replaceComputeRules(this.state.computeRules);
    }
    /**
     * Install a trusted ordinary-inductive signature as one transaction.
     *
     * The kernel does not need a separate inductive declaration language: a
     * type, constructor types, an eliminator type, and its iota equations are
     * all ordinary system entries.  Keeping their registration together is
     * important for the sandbox, however, because installing only the type
     * would leave constructors/eliminator unresolved and installing rules
     * before their constants exist would compile an unusable rule table.
     */
    registerSystemInductive(bundle: CoreSystemInductiveBundle) {
        if (!bundle?.type?.[0] || !bundle.type[1]) {
            throw new Error("归纳类型 bundle 缺少类型条目");
        }
        const entries: (readonly [string, AST])[] = [
            bundle.type,
            ...(bundle.auxiliaryTypes ?? []),
            ...(bundle.constructors ?? []),
            ...(bundle.eliminator ? [bundle.eliminator] : []),
            ...(bundle.recursor ? [bundle.recursor] : [])
        ];
        const definitions = [...(bundle.definitions ?? [])];
        const names = new Set<string>();
        for (const [name, type] of entries) {
            if (!name || !type || names.has(name)) {
                throw new Error(`归纳类型 bundle 名称冲突：${name || ""}`);
            }
            names.add(name);
        }
        for (const [name, definition] of definitions) {
            if (!name || !definition || names.has(name)) {
                throw new Error(`归纳类型 bundle 名称冲突：${name || ""}`);
            }
            names.add(name);
        }
        if (bundle.metadata?.typeName && bundle.metadata.typeName !== bundle.type[0]) {
            throw new Error(
                `归纳类型 metadata 名称与 bundle 不一致：${bundle.metadata.typeName} != ${bundle.type[0]}`
            );
        }
        const bundlePointConstructorNames = bundle.constructors.map(([name]) => name);
        const metadataPointConstructorNames = (bundle.metadata?.constructors ?? [])
            .map(ctor => ctor.name);
        const pointConstructorNames = new Set([
            ...bundlePointConstructorNames,
            ...metadataPointConstructorNames
        ]);
        const pathConstructorNames = new Set<string>();
        for (const path of bundle.metadata?.pathConstructors ?? []) {
            if (!path.name || pathConstructorNames.has(path.name)) {
                throw new Error(`路径构造子 metadata 名称冲突：${path.name || ""}`);
            }
            if (pointConstructorNames.has(path.name)) {
                throw new Error(`路径构造子不能作为点构造子注册：${path.name}`);
            }
            pathConstructorNames.add(path.name);
        }
        const twoPathConstructorNames = new Set<string>();
        for (const path of bundle.metadata?.twoPathConstructors ?? []) {
            if (!path.name || twoPathConstructorNames.has(path.name)) {
                throw new Error(`二阶路径构造子 metadata 名称冲突：${path.name || ""}`);
            }
            if (pointConstructorNames.has(path.name) || pathConstructorNames.has(path.name)) {
                throw new Error(`二阶路径构造子不能与一阶构造子同名：${path.name}`);
            }
            twoPathConstructorNames.add(path.name);
        }
        if (bundle.metadata?.kind === "hit1" || bundle.metadata?.kind === "hit2") {
            const hitDimension = bundle.metadata.kind === "hit2" ? 2 : 1;
            if (bundle.metadata.dimension !== hitDimension) {
                throw new Error(`HIT metadata 维度必须为 ${hitDimension}：${bundle.metadata.dimension ?? ""}`);
            }
            if (!bundle.metadata.pathConstructors?.length) {
                throw new Error("HIT metadata 至少需要一个一阶路径构造子");
            }
            if (bundle.metadata.kind === "hit2" && !bundle.metadata.twoPathConstructors?.length) {
                throw new Error("二维 HIT metadata 至少需要一个二阶路径构造子");
            }
            if (bundle.metadata.kind === "hit1" && bundle.metadata.twoPathConstructors?.length) {
                throw new Error("一阶 HIT metadata 不能包含二阶路径构造子");
            }
            if (bundlePointConstructorNames.length !== metadataPointConstructorNames.length
                || bundlePointConstructorNames.some((name, index) =>
                    metadataPointConstructorNames[index] !== name
                )) {
                throw new Error("一阶 HIT metadata 点构造子与 bundle 不一致");
            }
        }
        // A trusted bundle must never silently overwrite a system/user entry.
        // Sandbox validation normally catches this earlier, but keeping the
        // check at the Core boundary prevents stale declarations after a
        // repeated load or a worker retry.
        for (const name of names) {
            if (this.hasConst(name)) {
                throw new Error(`归纳类型 bundle 名称冲突：${name}`);
            }
        }

        const normalizedEntries = entries.map(([name, type]) => [
            name,
            this.desugar(Core.clone(type), true)
        ] as const);
        const normalizedRules: {
            [head: string]: { pattern: AST[]; result: AST }[]
        } = {};
        for (const [head, rules] of Object.entries(bundle.computeRules ?? {})) {
            if (!head || !Array.isArray(rules)) continue;
            normalizedRules[head] = rules
                .filter(rule => !!rule?.pattern?.length && !!rule.result)
                .map(rule => ({
                    pattern: rule.pattern.map(pattern => this.desugar(Core.clone(pattern), true)),
                    result: this.desugar(Core.clone(rule.result), true)
                }));
        }
        for (const path of [
            ...(bundle.metadata?.pathConstructors ?? []),
            ...(bundle.metadata?.twoPathConstructors ?? [])
        ]) {
            for (const head of new Set([
                path.name,
                path.computationName,
                `apd_${path.name}`,
                `@apd_${path.name}`,
                `ap_${path.name}`,
                `@ap_${path.name}`
            ])) {
                if (head && normalizedRules[head]?.length) {
                    throw new Error(`路径构造子不能注册为定义计算规则：${head}`);
                }
            }
        }

        let familyType = normalizedEntries[0][1];
        const familyBinders: { name: string; type: AST }[] = [];
        while ((familyType.type === "P" || familyType.type === "->")
            && familyType.nodes?.[0] && familyType.nodes?.[1]) {
            familyBinders.push({
                name: familyType.type === "P" ? familyType.name : "",
                type: Core.clone(familyType.nodes[0])
            });
            familyType = familyType.nodes[1];
        }
        const parameterCount = bundle.metadata?.parameterCount ?? familyBinders.length;
        const indexCount = bundle.metadata?.indexCount ?? 0;
        if (parameterCount < 0 || indexCount < 0
            || parameterCount + indexCount !== familyBinders.length) {
            throw new Error(
                `归纳类型 metadata 参数/索引数量不一致：${parameterCount}+${indexCount}`
            );
        }
        const parameters = familyBinders.slice(0, parameterCount);
        const indices = familyBinders.slice(parameterCount);

        if (bundle.metadata?.kind === "hit1" || bundle.metadata?.kind === "hit2") {
            const metadata = bundle.metadata;
            if (indexCount !== 0) throw new Error("HIT metadata 暂不支持索引");

            const auxiliaryTypes = new Map<string, AST>();
            for (const [name, type] of bundle.auxiliaryTypes ?? []) {
                auxiliaryTypes.set(name, this.desugar(Core.clone(type), true));
            }
            const pointTypes = new Map<string, AST>();
            for (const [name, type] of bundle.constructors) {
                pointTypes.set(name, this.desugar(Core.clone(type), true));
            }
            const normalizedMetadataAst = (ast: AST) => this.desugar(Core.clone(ast), true);
            const consumeTelescope = (
                source: AST,
                domains: readonly AST[],
                label: string
            ) => {
                let cursor = source;
                for (let index = 0; index < domains.length; index++) {
                    if ((cursor.type !== "P" && cursor.type !== "->")
                        || !cursor.nodes?.[0] || !cursor.nodes?.[1]
                        || !sameGeneratedAst(cursor.nodes[0], domains[index])) {
                        throw new Error(`${label} telescope 与 metadata 不一致`);
                    }
                    cursor = cursor.nodes[1];
                }
                return cursor;
            };
            const requirePublicSlot = (
                label: string,
                metadataName: string | undefined,
                entry: readonly [string, AST] | undefined
            ) => {
                if (!metadataName || !entry || entry[0] !== metadataName) {
                    throw new Error(`HIT metadata ${label}槽位与 bundle 不一致`);
                }
            };
            const requireFullSlot = (
                label: string,
                metadataName: string | undefined,
                publicName: string | undefined
            ) => {
                const expectedName = publicName ? `@${publicName}` : "";
                if (!metadataName || metadataName !== expectedName
                    || !auxiliaryTypes.has(metadataName)) {
                    throw new Error(`HIT metadata ${label}槽位与 bundle 不一致`);
                }
            };

            for (let index = 0; index < metadata.constructors.length; index++) {
                const constructor = metadata.constructors[index];
                const constructorType = pointTypes.get(constructor.name);
                if (!constructorType) {
                    throw new Error(`一阶 HIT metadata 点构造子槽位不存在：${constructor.name}`);
                }
                const expectedDomains = [
                    ...parameters.map(parameter => parameter.type),
                    ...constructor.argumentTypes.map(normalizedMetadataAst)
                ];
                const result = consumeTelescope(
                    constructorType,
                    expectedDomains,
                    `一阶 HIT 点构造子 ${constructor.name}`
                );
                const expectedResult = wrapApply(
                    wrapVar(metadata.typeName),
                    ...parameters.map(parameter => wrapVar(parameter.name)),
                    ...(constructor.resultIndices ?? []).map(normalizedMetadataAst)
                );
                if (!sameGeneratedAst(result, expectedResult)) {
                    throw new Error(`一阶 HIT 点构造子 ${constructor.name} 结论与 metadata 不一致`);
                }
            }

            for (const path of metadata.pathConstructors ?? []) {
                const pathType = auxiliaryTypes.get(path.name);
                if (!pathType) {
                    throw new Error(`一阶 HIT metadata 路径构造子不存在：${path.name}`);
                }
                const conclusion = consumeTelescope(pathType, [
                    ...parameters.map(parameter => parameter.type),
                    ...path.argumentTypes.map(normalizedMetadataAst)
                ], `一阶 HIT 路径构造子 ${path.name}`);
                const endpoints = generatedEqualityEndpoints(conclusion);
                if (!endpoints
                    || !sameGeneratedAst(endpoints[0], normalizedMetadataAst(path.left))
                    || !sameGeneratedAst(endpoints[1], normalizedMetadataAst(path.right))) {
                    throw new Error(`一阶 HIT 路径构造子 ${path.name} 端点与 metadata 不一致`);
                }

                const computationNames = [
                    `apd_${path.name}`,
                    `@apd_${path.name}`,
                    `ap_${path.name}`,
                    `@ap_${path.name}`
                ];
                if (path.computationName !== computationNames[0]) {
                    throw new Error(`一阶 HIT metadata 计算定理不存在：${path.computationName ?? ""}`);
                }
                for (const computationName of computationNames) {
                    const computationType = auxiliaryTypes.get(computationName);
                    if (!computationType) {
                        if (computationName === path.computationName) {
                            throw new Error(`一阶 HIT metadata 计算定理不存在：${computationName}`);
                        }
                        throw new Error(`一阶 HIT metadata 路径计算项槽位不存在：${computationName}`);
                    }
                    let conclusion = computationType;
                    while ((conclusion.type === "P" || conclusion.type === "->")
                        && conclusion.nodes?.[1]) conclusion = conclusion.nodes[1];
                    if (!generatedEqualityEndpoints(conclusion)) {
                        throw new Error(`一阶 HIT 路径计算项 ${computationName} 不是等式命题`);
                    }
                }
            }

            for (const path of metadata.twoPathConstructors ?? []) {
                const pathType = auxiliaryTypes.get(path.name);
                if (!pathType) {
                    throw new Error(`二维 HIT metadata 二阶路径构造子不存在：${path.name}`);
                }
                const conclusion = consumeTelescope(pathType, [
                    ...parameters.map(parameter => parameter.type),
                    ...path.argumentTypes.map(normalizedMetadataAst)
                ], `二维 HIT 二阶路径构造子 ${path.name}`);
                const endpoints = generatedEqualityEndpoints(conclusion);
                if (!endpoints
                    || !sameGeneratedAst(endpoints[0], normalizedMetadataAst(path.left))
                    || !sameGeneratedAst(endpoints[1], normalizedMetadataAst(path.right))) {
                    throw new Error(`二维 HIT 二阶路径构造子 ${path.name} 端点与 metadata 不一致`);
                }
                if (!pathConstructorNames.has(path.leftPath)
                    || !pathConstructorNames.has(path.rightPath)) {
                    throw new Error(`二维 HIT 二阶路径构造子 ${path.name} 的一阶路径引用不存在`);
                }
                const computationNames = [
                    `apd_${path.name}`,
                    `@apd_${path.name}`,
                    `ap_${path.name}`,
                    `@ap_${path.name}`
                ];
                if (path.computationName !== computationNames[0]) {
                    throw new Error(`二维 HIT metadata 计算定理不存在：${path.computationName ?? ""}`);
                }
                for (const computationName of computationNames) {
                    const computationType = auxiliaryTypes.get(computationName);
                    if (!computationType) {
                        if (computationName === path.computationName) {
                            throw new Error(`二维 HIT metadata 计算定理不存在：${computationName}`);
                        }
                        throw new Error(`二维 HIT 二阶路径计算项槽位不存在：${computationName}`);
                    }
                    let conclusion = computationType;
                    while ((conclusion.type === "P" || conclusion.type === "->")
                        && conclusion.nodes?.[1]) conclusion = conclusion.nodes[1];
                    if (!generatedEqualityEndpoints(conclusion)) {
                        throw new Error(`二维 HIT 二阶路径计算项 ${computationName} 不是等式命题`);
                    }
                }
            }

            requirePublicSlot("公开消去器", metadata.eliminatorName, bundle.eliminator);
            requireFullSlot("完整消去器", metadata.fullEliminatorName, metadata.eliminatorName);
            requirePublicSlot("公开递归器", metadata.recursorName, bundle.recursor);
            requireFullSlot("完整递归器", metadata.fullRecursorName, metadata.recursorName);
        }

        const previousTypes = new Map<string, AST | undefined>();
        for (const [name] of normalizedEntries) previousTypes.set(name, this.state.sysTypes[name]);
        const normalizedDefinitions = definitions.map(([name, definition]) => [
            name,
            this.desugar(Core.clone(definition), true)
        ] as const);
        const previousDefinitions = new Map<string, AST | undefined>();
        for (const [name] of normalizedDefinitions) previousDefinitions.set(name, this.state.sysDefs[name]);
        const previousRules = new Map<string, { pattern: AST[]; result: AST }[] | undefined>();
        for (const head of Object.keys(normalizedRules)) {
            previousRules.set(head, this.state.computeRules[head]);
        }
        try {
            for (const [name, type] of normalizedEntries) this.state.sysTypes[name] = type;
            for (const [name, definition] of normalizedDefinitions) this.state.sysDefs[name] = definition;
            for (const [head, rules] of Object.entries(normalizedRules)) {
                // Preserve any pre-existing equations for a shared head. A
                // fresh ordinary inductive normally has a unique eliminator,
                // while append semantics make registration composable for
                // generated aliases.
                this.state.computeRules[head] = [
                    ...(this.state.computeRules[head] ?? []),
                    ...rules
                ];
            }
            this.syncSemanticDefinitions();
            this.syncSemanticComputeRules();
            // `setConstantType` accepts a raw system type so dependencies can
            // be installed as a mutually-referencing batch.  Validate every
            // generated type only after the whole batch is visible, but keep
            // the checks inside this transaction so an invalid constructor or
            // eliminator cannot leak partially-registered sandbox constants.
            for (const [, type] of normalizedEntries) {
                this.checkTypeFormation(type, []);
            }
        } catch (error) {
            for (const [name, previous] of previousTypes) {
                if (previous) this.state.sysTypes[name] = previous;
                else delete this.state.sysTypes[name];
            }
            for (const [name, previous] of previousDefinitions) {
                if (previous) this.state.sysDefs[name] = previous;
                else delete this.state.sysDefs[name];
            }
            for (const [head, previous] of previousRules) {
                if (previous) this.state.computeRules[head] = previous;
                else delete this.state.computeRules[head];
            }
            this.syncSemanticDefinitions();
            this.syncSemanticComputeRules();
            throw error;
        }
        const registrationName = bundle.type[0];
        const metadata = bundle.metadata
            ? {
                version: bundle.metadata.version,
                kind: bundle.metadata.kind,
                dimension: bundle.metadata.dimension,
                typeName: bundle.metadata.typeName,
                parameterCount,
                indexCount,
                eliminatorName: bundle.metadata.eliminatorName,
                fullEliminatorName: bundle.metadata.fullEliminatorName,
                recursorName: bundle.metadata.recursorName,
                fullRecursorName: bundle.metadata.fullRecursorName,
                parameters,
                indices,
                constructors: bundle.metadata.constructors.map(ctor => ({
                    name: ctor.name,
                    argumentTypes: ctor.argumentTypes.map(type => Core.clone(type)),
                    resultIndices: ctor.resultIndices?.map(index => Core.clone(index))
                })),
                pathConstructors: bundle.metadata.pathConstructors?.map(ctor => ({
                    name: ctor.name,
                    argumentTypes: ctor.argumentTypes.map(type => Core.clone(type)),
                    left: Core.clone(ctor.left),
                    right: Core.clone(ctor.right),
                    computationName: ctor.computationName
                })),
                twoPathConstructors: bundle.metadata.twoPathConstructors?.map(ctor => ({
                    name: ctor.name,
                    argumentTypes: ctor.argumentTypes.map(type => Core.clone(type)),
                    left: Core.clone(ctor.left),
                    right: Core.clone(ctor.right),
                    leftPath: ctor.leftPath,
                    rightPath: ctor.rightPath,
                    computationName: ctor.computationName
                }))
            }
            : undefined;
        this.registeredSystemInductives.set(registrationName, {
            names: [...names],
            previousTypes,
            previousDefinitions,
            previousRules,
            metadata
        });
        if (metadata) {
            this.inductiveMetadata.set(metadata.typeName, metadata);
        }
        return {
            names: normalizedEntries.map(([name]) => name),
            computeRuleCount: Object.values(normalizedRules)
                .reduce((count, rules) => count + rules.length, 0)
        };
    }
    /** Remove all dynamic bundles previously installed by a sandbox bridge. */
    clearSystemInductives() {
        for (const [typeName, registration] of this.registeredSystemInductives) {
            for (const [name, previous] of registration.previousTypes) {
                if (previous) this.state.sysTypes[name] = previous;
                else delete this.state.sysTypes[name];
            }
            for (const [name, previous] of registration.previousDefinitions) {
                if (previous) this.state.sysDefs[name] = previous;
                else delete this.state.sysDefs[name];
            }
            for (const [head, previous] of registration.previousRules) {
                if (previous) this.state.computeRules[head] = previous;
                else delete this.state.computeRules[head];
            }
            this.inductiveMetadata.delete(typeName);
        }
        this.registeredSystemInductives.clear();
        this.syncSemanticDefinitions();
        this.syncSemanticTypes();
        this.syncSemanticComputeRules();
    }
    getInductiveMetadata(typeName: string) {
        const metadata = this.inductiveMetadata.get(typeName);
        if (!metadata) return undefined;
        return {
            version: metadata.version,
            kind: metadata.kind,
            dimension: metadata.dimension,
            typeName: metadata.typeName,
            parameterCount: metadata.parameterCount,
            indexCount: metadata.indexCount,
            eliminatorName: metadata.eliminatorName,
            fullEliminatorName: metadata.fullEliminatorName,
            recursorName: metadata.recursorName,
            fullRecursorName: metadata.fullRecursorName,
            parameters: metadata.parameters.map(parameter => ({
                name: parameter.name,
                type: Core.clone(parameter.type)
            })),
            indices: metadata.indices.map(index => ({
                name: index.name,
                type: Core.clone(index.type)
            })),
            constructors: metadata.constructors.map(ctor => ({
                name: ctor.name,
                argumentTypes: ctor.argumentTypes.map(type => Core.clone(type)),
                resultIndices: ctor.resultIndices?.map(index => Core.clone(index))
            })),
            pathConstructors: metadata.pathConstructors?.map(ctor => ({
                name: ctor.name,
                argumentTypes: ctor.argumentTypes.map(type => Core.clone(type)),
                left: Core.clone(ctor.left),
                right: Core.clone(ctor.right),
                computationName: ctor.computationName
            })),
            twoPathConstructors: metadata.twoPathConstructors?.map(ctor => ({
                name: ctor.name,
                argumentTypes: ctor.argumentTypes.map(type => Core.clone(type)),
                left: Core.clone(ctor.left),
                right: Core.clone(ctor.right),
                leftPath: ctor.leftPath,
                rightPath: ctor.rightPath,
                computationName: ctor.computationName
            }))
        };
    }
    isRegisteredInductiveType(typeName: string) {
        return this.inductiveMetadata.has(typeName);
    }
    setSystemType(name: string, type?: AST) {
        if (type) this.state.sysTypes[name] = type;
        else delete this.state.sysTypes[name];
        this.syncSemanticConstantType(name);
    }
    setSystemDefinition(name: string, definition?: AST) {
        if (definition) this.state.sysDefs[name] = definition;
        else delete this.state.sysDefs[name];
        this.syncSemanticDefinition(name);
    }
    clearDefinitionCache(name: string) {
        delete this.state.defTypes[name];
        this.syncSemanticConstantType(name);
        this.syncSemanticDefinition(name);
    }
    hasDefinitionCache(name: string) {
        return !!this.inspectDefinitionCache(this.state.defTypes[name]);
    }
    registerSystemDefinition(name: string, definition: AST, context: Context = []) {
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
                if (!id) preparedContext[index][2] = this.state.bondVarId++;
                else if (Number.isFinite(id) && id >= this.state.bondVarId) this.state.bondVarId = id + 1;
                preparedContext[index][1] = this.markBondVars(
                    this.desugar(type, false),
                    preparedContext.slice(index)
                );
            }
            const filled = this.markBondVars(
                this.desugar(Core.clone(definition), false),
                preparedContext
            );
            let generalizedMetas: readonly NbeGeneralizedMeta[] | undefined;
            let elaboratedDefinition: AST | undefined;
            const cachedType = this.trySemanticTypeSynthesis(filled, preparedContext, {
                allowHoles: true,
                elaborateMetas: true,
                generalizeMetas: true,
                requireElaboratedTerm: true,
                captureGeneralizedMetas: metas => { generalizedMetas = metas; },
                captureElaboratedTerm: term => { elaboratedDefinition = term; }
            });
            if (!cachedType) throw new Error(`Unsupported semantic system definition: ${name}`);
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
                    const generalizedNames = new Set(
                        generalizedMetas?.map(meta => meta.name) ?? []
                    );
                    const restorePortableHoles = (node: AST) => {
                        if (node.type === "var" && generalizedNames.has(node.name)) {
                            Core.assign(node, wrapVar("_"), true);
                            return;
                        }
                        for (const child of node.nodes ?? []) restorePortableHoles(child);
                    };
                    restorePortableHoles(portableDefinition);
                    this.setSystemDefinition(name, portableDefinition);
                }
            }
            this.restoreDefinitionCache(name, this.createSemanticDefinitionCacheSnapshot(
                cachedType,
                this.state.bondVarId,
                generalizedMetas
            ));
            return Core.clone(filled);
        } catch (error) {
            this.clearDefinitionCache(name);
            throw error;
        }
    }
    /** Attach a user definition, optionally retaining its just-validated cache. */
    setUserDefinition(
        name: string,
        definition?: AST,
        preserveDefinitionCache = false
    ) {
        if (definition) {
            if (this.state.userDefs[name] !== definition && !preserveDefinitionCache) {
                delete this.state.defTypes[name];
            }
            this.state.userDefs[name] = definition;
        } else {
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
    private syncSemanticDefinition(name: string) {
        const definition = this.state.userDefs[name] ?? this.state.sysDefs[name];
        if (!definition) {
            this.semanticKernel.deleteDefinition(name);
            return;
        }
        // User definitions retain surface syntax for the editor (notably
        // `(a,b)` tuples and `A X B`).  The semantic kernel only understands
        // the core AST, so normalize a private clone at this boundary rather
        // than forcing the presentation copy to lose its familiar syntax.
        const semanticDefinition = this.desugar(Core.clone(definition), true);
        const hasInferenceMetas = collectInferenceMetaNames(definition).size > 0;
        const hasTrustedTypeCache = !!this.inspectDefinitionCache(this.state.defTypes[name]);
        // Definitions carrying generalized metas are executable only after
        // their validated type scheme has been restored. Recompile on cache
        // transitions because the source fingerprint itself is unchanged.
        if (hasInferenceMetas) this.semanticKernel.deleteDefinition(name);
        this.semanticKernel.setDefinition(name, semanticDefinition, {
            rigidMetas: hasInferenceMetas && hasTrustedTypeCache,
            rigidHoles: this.state.userDefs[name] !== undefined
        });
    }
    private syncSemanticConstantType(name: string) {
        const systemType = this.state.sysTypes[name];
        if (systemType) {
            this.semanticTypeChecker.setConstantType(name, systemType);
            return;
        }
        this.syncSemanticDefinitionType(name, this.state.defTypes[name]);
    }
    private syncSemanticDefinitionType(name: string, rawCache: unknown) {
        const cache = this.inspectDefinitionCache(rawCache);
        if (!cache) {
            this.semanticTypeChecker.setConstantType(name);
            return;
        }
        this.semanticTypeChecker.setConstantSchemeSnapshot(name, cache.semantic);
    }
    private inspectDefinitionCache(rawCache: unknown): DefinitionCacheInspection | null {
        if (isSemanticDefinitionCacheSnapshot(rawCache)) {
            return {
                type: rawCache.type,
                semantic: rawCache
            };
        }
        return null;
    }
    private isBareGeneralizedDefinitionReference(ast: AST) {
        if (ast?.type !== "var" || ast.bondVarId) return false;
        const cache = this.inspectDefinitionCache(this.state.defTypes[ast.name]);
        return !!cache?.semantic?.metas.length;
    }
    serializeDefinitionCache(name: string): DefinitionTypeCacheSnapshot {
        const cache = this.inspectDefinitionCache(this.state.defTypes[name]);
        if (cache?.semantic) return cloneSemanticDefinitionCache(cache.semantic);
        return null;
    }
    private createSemanticDefinitionCacheSnapshot(
        cachedType: AST,
        bondVarId: number,
        generalizedMetas: readonly NbeGeneralizedMeta[] = []
    ): DefinitionTypeCacheSnapshot {
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
    restoreDefinitionCache(name: string, cache: DefinitionTypeCacheSnapshot) {
        if (!cache) return;
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
    error(ast: AST, msg: any, stop: boolean) {
        this.state.errormsg.unshift({ ast, msg });
        if (!this.silentErrors) {
            const source = parser.stringify(ast);
            console.log(source ?? ast?.type ?? TR("表达式丢失"), msg);
        }
        ast.err = msg;
        if (stop) throw msg;
    }
    /** Run a speculative check without printing its expected failure. */
    withSilentErrors<T>(callback: () => T): T {
        const previousErrors = this.state.errormsg;
        const previousTimeout = Core.timeoutOccured;
        this.silentErrors++;
        try {
            return callback();
        } finally {
            this.silentErrors--;
            this.state.errormsg = previousErrors;
            Core.timeoutOccured = previousTimeout;
        }
    }
    checkDefinition(ast: AST, context: Context) {
        let prepared: {
            filledDefinition: AST,
            definitionCache: DefinitionTypeCacheSnapshot
        };
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
                definitionCache: this.createSemanticDefinitionCacheSnapshot(
                    cachedType,
                    this.state.bondVarId,
                    generalizedMetas
                )
            };
        });
        if (!prepared) throw TR("类型检查未返回定义结果");
        return prepared;
    }
    /**
     * Validate a declaration type, returning its fully elaborated syntax.
     * Ordinary `checkType` only synthesizes the type of an arbitrary term;
     * trusted declarations additionally require that synthesized type to be
     * a Universe and that no elaboration metavariable remains.
     */
    checkTypeFormation(ast: AST, context: Context = []) {
        const candidate = Core.clone(ast);
        const inferred = this.checkType(
            candidate,
            context,
            false,
            undefined,
            false,
            true,
            false
        );
        if (hasSemanticElaborationHole(candidate)
            || collectInferenceMetaNames(candidate).size
            || hasSemanticElaborationHole(inferred)
            || collectInferenceMetaNames(inferred).size) {
            this.error(candidate, TR("类型推断中仍有未确定的占位符"), true);
        }
        if (isNbeUniverseType(inferred)) return candidate;
        const normalized = this.semanticKernel.tryWhnf(inferred, context, {
            deadline: this.state.time ? this.state.time + Core.timeout : undefined,
            maxSteps: Core.semanticTypeSynthesisMaxSteps,
            unfoldDefinitions: true
        });
        if (!normalized || !isNbeUniverseType(normalized)) {
            this.error(candidate, TR("声明类型必须属于某个 Universe"), true);
        }
        return candidate;
    }
    checkType(
        ast: AST,
        context: Context,
        allowModify: boolean,
        beforeInferResolution?: (
            ast: AST,
            generalizedMetas?: readonly NbeGeneralizedMeta[]
        ) => void,
        allowUnsolvedTermMetas = false,
        requireSemantic = false,
        preservePresentation = true
    ) {
        const semanticPresentation = preservePresentation && (!allowModify
            || (!requireSemantic && hasExplicitAtOccurrence(ast)))
            ? Core.clone(ast)
            : undefined;
        let semanticAssertionSource: AST | undefined;
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
        if (semanticPresentation) this.captureDisplaySurface(ast, semanticPresentation);
        Core.timeoutOccured = false;
        this.state.errormsg = [];
        this.state.time = Date.now();
        this.state.bondVarId = 1;
        this.semanticTypeCheckRecursiveActive = Core.semanticTypeCheckRecursive
            || Object.keys(this.state.userDefs).length
                >= Core.semanticTypeCheckRecursiveMinDefinitions;
        // mark if context is not marked
        if (context.length) context = Core.cloneContext(context);
        for (let i = context.length - 1; i >= 0; i--) {
            const [e, t, id] = context[i];
            if (!id) context[i][2] = this.state.bondVarId++;
            else if (Number.isFinite(id) && id >= this.state.bondVarId) this.state.bondVarId = id + 1;
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
            const semanticAssertion = this.trySemanticTypeAssertion(
                semanticAssertionTarget,
                context,
                !beforeInferResolution,
                allowUnsolvedTermMetas
                    || hasSemanticElaborationHole(semanticAssertionTarget.nodes[0]),
                semanticAssertionSource
            );
            if (isNbeTypeFailure(semanticAssertion)) {
                this.reportSemanticFailure(semanticAssertionTarget, semanticAssertion);
            } else if (semanticAssertion === false) {
                this.error(ast, TR("类型断言失败"), true);
            } else if (semanticAssertion) {
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
                } else {
                    this.finalizeSemanticResult(ast, context);
                }
                if (semanticPresentation) {
                    this.restoreSemanticPresentation(ast, semanticPresentation);
                }
                if (this.state.errormsg.length) throw this.state.errormsg[0].msg;
                return ast.checked;
            }
        }

        if (ast.type === "===") {
            const semanticEquality = this.trySemanticDefinitionalEquality(ast, context);
            if (isNbeTypeFailure(semanticEquality)) {
                this.reportSemanticFailure(ast, semanticEquality);
            } else if (semanticEquality === false) {
                const unresolvedDefinitions = this.semanticErrorUnresolvedDefinitions(ast);
                const unresolvedSuffix = unresolvedDefinitions.length
                    ? ` [${unresolvedDefinitions.join(", ")}: _]`
                    : "";
                this.error(
                    ast,
                    TR("定义相等断言失败") + ": "
                    + this.printSemanticErrorAst(ast.nodes[0]) + " ≠ "
                    + this.printSemanticErrorAst(ast.nodes[1])
                    + unresolvedSuffix,
                    true
                );
            } else if (semanticEquality) {
                Core.semanticTypeCheckFastPathHits++;
                this.finalizeSemanticResult(ast, context);
                if (semanticPresentation) {
                    this.restoreSemanticPresentation(ast, semanticPresentation);
                }
                if (this.state.errormsg.length) throw this.state.errormsg[0].msg;
                return ast.checked;
            }
        }

        if (allowModify && ast.type === "whnf"
            && this.trySemanticProofAssistantNormalize(ast.nodes[0], context)) {
            this.finalizeSemanticResult(ast.nodes[0], context);
            if (this.state.errormsg.length) throw this.state.errormsg[0].msg;
            return ast.nodes[0];
        }

        let semanticTarget: AST | undefined;
        if (!allowModify) {
            if (ast.type === ":=" && ast.nodes?.[1]?.type !== ":") {
                semanticTarget = ast.nodes[1];
            } else if (ast.type !== ":" && ast.type !== ":=" && ast.type !== "===" && ast.type !== "whnf") {
                semanticTarget = ast;
            }
        }
        if (semanticTarget) {
            const semanticDefinition = ast.type === ":=";
            const semanticElaboration = semanticDefinition
                || hasSemanticElaborationHole(semanticTarget);
            let generalizedMetas: readonly NbeGeneralizedMeta[] | undefined;
            let semanticFailure: NbeTypeFailure | undefined;
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
                } else {
                    this.finalizeSemanticResult(ast, context);
                }
                if (semanticPresentation) {
                    this.restoreSemanticPresentation(ast, semanticPresentation);
                }
                if (this.state.errormsg.length) throw this.state.errormsg[0].msg;
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
    private finalizeSemanticResult(ast: AST, context: Context) {
        const alphaConversionIds = new Set<number>;
        const visit = (node: AST, nodeContext: Context) => {
            const boundType = node.type === "L" || node.type === "P"
                || node.type === "W" || node.type === "S";
            if (boundType && node.name?.[0] === "*") {
                alphaConversionIds.add(node.bondVarId);
            }
            if (node.nodes?.[0]) visit(node.nodes[0], nodeContext);
            if (node.nodes?.[1]) {
                visit(
                    node.nodes[1],
                    boundType
                        ? assignContext(
                            [node.name, node.nodes[0], node.bondVarId],
                            nodeContext
                        )
                        : nodeContext
                );
            }
            if (node.type === "var" && node.bondVarId !== Infinity) {
                const index = !node.bondVarId ? Infinity : findContextIndexByBondVarId(
                    nodeContext,
                    node.bondVarId,
                    (left, right) => this.isBondVarIdEqual(left, right)
                );
                if (index === -1) {
                    console.warn("Bound Var Leakage of id " + node.bondVarId, nodeContext);
                } else {
                    const bounded = findContextEntriesBeforeByName(
                        nodeContext,
                        index === Infinity ? node.name : nodeContext[index][0],
                        index
                    );
                    for (const [, , id] of bounded) {
                        if (id) alphaConversionIds.add(id);
                    }
                    if (isFinite(index)) node.name = nodeContext[index][0];
                }
            }
            if (node.checked) visit(node.checked, nodeContext);
            if (!node.origin || node["desugared"]) this.ensugar(node);
        };
        visit(ast, context);
        this.doAlphaConversionByIds(ast, context, alphaConversionIds);
    }
    static getFreeVars(ast: AST, res = new Set<string>, scope = new Set<string>) {
        if (ast.type === "var" && !scope.has(ast.name)) {
            res.add(ast.name);
        } else if (ast.type === "L" || ast.type === "P" || ast.type === "W" || ast.type === "S") {
            this.getFreeVars(ast.nodes[0], res, scope);
            const alreadyBound = scope.has(ast.name);
            scope.add(ast.name);
            this.getFreeVars(ast.nodes[1], res, scope);
            if (!alreadyBound) scope.delete(ast.name);
        } else if (ast.nodes?.length) {
            for (const node of ast.nodes) this.getFreeVars(node, res, scope);
        }
        return res;
    }
    static getAllVars(ast: AST, res = new Set<string>) {
        if (ast.type === "var" || ast.type === "L" || ast.type === "P" || ast.type === "W" || ast.type === "S") {
            res.add(ast.name);
        }
        if (ast.nodes?.length) {
            this.getAllVars(ast.nodes[0], res);
            if (ast.nodes[1]) this.getAllVars(ast.nodes[1], res);
        }
        return res;
    }
    static getNewName(refName: string, excludeSet: Set<string>) {
        let n = refName;
        while (excludeSet.has(n)) {
            n += "'";
        }
        return n;
    }
    doAlphaConversionByIds(ast: AST, context: Context, ids: Set<number>) {
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
        if (ast.nodes?.[0]) this.doAlphaConversionByIds(ast.nodes[0], context, ids);
        if (ast.nodes?.[1]) this.doAlphaConversionByIds(ast.nodes[1], context, ids);
        delete ast.bondVarId;
        if (ast.checked) this.doAlphaConversionByIds(ast.checked, context, ids);
    }
    private applySemanticTerm(target: AST, source: AST) {
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
    private restoreSemanticPresentation(target: AST, surface: AST) {
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
            if (resolvedHole) target.checked = {
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
    private compactSemanticOutputType(ast: AST) {
        const compact = Core.clone(ast, true);
        const implicitAliasArities = new Map(this.opaque);
        const stack: [AST, boolean][] = [[compact, false]];
        while (stack.length) {
            const [node, visited] = stack.pop();
            if (visited) {
                if (node.type !== "apply") continue;
                const application = this.flattenApplyList(node);
                const head = application[0];
                if (head.type !== "var" || head.bondVarId || head.name?.[0] !== "@") continue;
                const alias = head.name.slice(1);
                const prefixLength = implicitAliasArities.get(alias);
                if (!prefixLength || application.length < prefixLength) continue;
                Core.assign(node, wrapApply(
                    wrapVar(alias),
                    ...application.slice(prefixLength)
                ), true);
                continue;
            }
            stack.push([node, true]);
            for (let index = (node.nodes?.length ?? 0) - 1; index >= 0; index--) {
                stack.push([node.nodes[index], false]);
            }
        }
        return compact;
    }
    private collectSemanticSourceTypeMetas(context: Context): NbeSourceMetaInput[] {
        const scopes = new Map<string, Set<number>>();
        for (let index = 0; index < context.length; index++) {
            const type = context[index][1];
            if (type?.type !== "var" || !/^\?[^:]+$/.test(type.name)) continue;
            // Contexts are stored innermost-first. A binder's type may only
            // mention the outer entries after it, which is exactly the
            // creation scope the legacy InferTable used to retain.
            const occurrenceScope = new Set(
                context.slice(index + 1)
                    .map(([, , id]) => id)
                    .filter(isPositiveBondVarId)
            );
            const allowed = scopes.get(type.name);
            if (!allowed) {
                scopes.set(type.name, occurrenceScope);
                continue;
            }
            // Repeated occurrences share one metavariable, so retain only the
            // binders available at every occurrence.
            for (const id of allowed) {
                if (!occurrenceScope.has(id)) allowed.delete(id);
            }
        }
        return Array.from(scopes, ([name, allowedBondVarIds]) => ({
            name,
            role: "type" as const,
            allowedBondVarIds: Array.from(allowedBondVarIds)
        }));
    }
    private commitSemanticSourceMetaConstraints(
        context: Context,
        constraints: readonly NbeSourceMetaConstraint[] | undefined
    ) {
        if (!constraints?.length) return true;
        const sourceMetas = new Map(
            this.collectSemanticSourceTypeMetas(context)
                .map(meta => [meta.name, meta] as const)
        );
        const prepared: NbeSourceMetaConstraint[] = [];
        const names = new Set<string>();
        for (const constraint of constraints) {
            if (!/^\?[^:]+$/.test(constraint.name) || names.has(constraint.name)
                || hasSemanticElaborationHole(constraint.value)) return false;
            const sourceMeta = sourceMetas.get(constraint.name);
            if (!sourceMeta) return false;
            const allowedIds = new Set(sourceMeta.allowedBondVarIds);
            const visit = (ast: AST, bound = new Set<number>()): boolean => {
                if (!ast || typeof ast !== "object") return false;
                if (ast.type === "var") {
                    if (ast.name === "_" || ast.name?.startsWith("?")) return false;
                    if (isPositiveBondVarId(ast.bondVarId)
                        && !bound.has(ast.bondVarId)
                        && !allowedIds.has(ast.bondVarId)) return false;
                    return true;
                }
                const binder = ast.type === "L" || ast.type === "P"
                    || ast.type === "S" || ast.type === "W";
                if (ast.nodes?.[0] && !visit(ast.nodes[0], bound)) return false;
                if (ast.nodes?.[1]) {
                    const bodyBound = binder && isPositiveBondVarId(ast.bondVarId)
                        ? new Set(bound).add(ast.bondVarId)
                        : bound;
                    if (!visit(ast.nodes[1], bodyBound)) return false;
                }
                return true;
            };
            if (!visit(constraint.value)) return false;
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
    private trySemanticTypeAssertion(
        ast: AST,
        context: Context,
        annotateTerm: boolean,
        allowUnsolvedTermMetas: boolean,
        sourceAssertion?: AST
    ): SemanticTypeAttempt<SemanticTypeAssertionResult> {
        if (ast.type !== ":") return;
        const term = Core.clone(ast.nodes?.[0]);
        const expected = Core.clone(ast.nodes?.[1]);
        const schematicMetaNames = collectInferenceMetaNames(
            expected,
            collectInferenceMetaNames(term)
        );
        const sourceTerm = sourceAssertion?.type === ":"
            ? sourceAssertion.nodes?.[0]
            : undefined;
        const sourceExpected = sourceAssertion?.type === ":"
            ? sourceAssertion.nodes?.[1]
            : undefined;
        const sourceMaxNodes = Core.semanticTypeAssertionMaxNodes;
        const sourceFits = (!sourceTerm || fitsSemanticNbeBudget(
            sourceTerm,
            sourceMaxNodes,
            false,
            context,
            true,
            schematicMetaNames
        )) && (!sourceExpected || fitsSemanticNbeBudget(
            sourceExpected,
            sourceMaxNodes,
            false,
            context,
            true,
            schematicMetaNames
        ));
        if (!sourceFits) {
            return (sourceTerm && exceedsSemanticNbeNodeBudget(sourceTerm, sourceMaxNodes))
                || (sourceExpected && exceedsSemanticNbeNodeBudget(sourceExpected, sourceMaxNodes))
                ? { status: "unsupported", code: "budget-exhausted" }
                : undefined;
        }
        const termMaxNodes = semanticAssertionKernelNodeBudget(
            sourceTerm,
            term,
            sourceMaxNodes
        );
        const expectedMaxNodes = semanticAssertionKernelNodeBudget(
            sourceExpected,
            expected,
            sourceMaxNodes
        );
        const kernelFits = fitsSemanticNbeBudget(
            term,
            termMaxNodes,
            false,
            context,
            true,
            schematicMetaNames
        ) && fitsSemanticNbeBudget(
            expected,
            expectedMaxNodes,
            false,
            context,
            true,
            schematicMetaNames
        );
        if (!kernelFits) {
            return exceedsSemanticNbeNodeBudget(term, termMaxNodes)
                || exceedsSemanticNbeNodeBudget(expected, expectedMaxNodes)
                ? { status: "unsupported", code: "budget-exhausted" }
                : undefined;
        }
        Core.semanticTypeCheckAttempts++;
        let nextSemanticBondVarId = Math.max(
            this.state.bondVarId,
            ...context.map(([, , id]) => Number.isFinite(id) ? id + 1 : 0)
        );
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
            const synthesized = this.semanticTypeChecker.trySynthesize(
                term,
                context,
                options
            );
            if (synthesized.status === "success") {
                const equality = this.semanticTypeChecker.tryDefinitionalEquality(
                    synthesized.type,
                    expected,
                    context,
                    options
                );
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
                } else if (equality.status === "invalid") {
                    return false;
                } else if (equality.code === "budget-exhausted") {
                    return equality;
                }
            } else if (synthesized.code === "budget-exhausted") {
                return synthesized;
            }
        }
        if (checked.status !== "success") {
            if (checked.code === "budget-exhausted") return checked;
            // Preserve the semantic diagnostic for an unresolved constant.
            // Returning the generic `false` here turns a simple misspelling
            // (for example `divstate_zero` vs `divState_zero`) into the much
            // less actionable "类型断言失败" message at the declaration
            // boundary.  The caller can then report the actual unknown name.
            if (checked.status === "invalid" && checked.code === "unknown-constant") {
                return checked;
            }
            return checked.status === "invalid" ? false : undefined;
        }
        const returnedSchematicMetaNames = new Set(checked.schematicMetaNames ?? []);
        if (!fitsSemanticNbeBudget(
            checked.type,
            expectedMaxNodes,
            false,
            context,
            false,
            returnedSchematicMetaNames
        )) {
            return exceedsSemanticNbeNodeBudget(
                checked.type,
                expectedMaxNodes
            ) ? { status: "unsupported", code: "budget-exhausted" } : undefined;
        }
        if (!this.commitSemanticSourceMetaConstraints(
            context,
            checked.sourceMetaConstraints
        )) return;
        Core.semanticTypeCheckHits++;
        if (checked.expectedTerm) this.applySemanticTerm(ast.nodes[1], checked.expectedTerm);
        if (checked.term) this.applySemanticTerm(ast.nodes[0], checked.term);
        const returnedIds = new Set<number>();
        collectAstBondVarIds(checked.expectedTerm, returnedIds);
        collectAstBondVarIds(checked.type, returnedIds);
        let nextReturnedId = 0;
        for (const id of returnedIds) nextReturnedId = Math.max(nextReturnedId, id + 1);
        this.state.bondVarId = Math.max(nextSemanticBondVarId, nextReturnedId);
        ast.checked = ast.nodes[1];
        return {
            checked: ast.checked,
            ...(checked.generalizedMetas?.length
                ? { generalizedMetas: checked.generalizedMetas }
                : {})
        };
    }
    private trySemanticDefinitionalEquality(
        ast: AST,
        context: Context
    ): SemanticTypeAttempt<AST> {
        if (ast.type !== "===") return;
        const leftSource = Core.clone(ast.nodes?.[0]);
        const rightSource = Core.clone(ast.nodes?.[1]);
        const schematicMetaNames = collectInferenceMetaNames(
            rightSource,
            collectInferenceMetaNames(leftSource)
        );
        if (!fitsSemanticNbeBudget(
            leftSource,
            Core.semanticTypeAssertionMaxNodes,
            false,
            context,
            true,
            schematicMetaNames
        ) || !fitsSemanticNbeBudget(
            rightSource,
            Core.semanticTypeAssertionMaxNodes,
            false,
            context,
            true,
            schematicMetaNames
        )) {
            return exceedsSemanticNbeNodeBudget(leftSource, Core.semanticTypeAssertionMaxNodes)
                || exceedsSemanticNbeNodeBudget(rightSource, Core.semanticTypeAssertionMaxNodes)
                ? { status: "unsupported", code: "budget-exhausted" }
                : undefined;
        }

        Core.semanticTypeCheckAttempts++;
        let nextSemanticBondVarId = Math.max(
            this.state.bondVarId,
            ...context.map(([, , id]) => Number.isFinite(id) ? id + 1 : 0)
        );
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
        const equality = this.semanticTypeChecker.tryDefinitionalEquality(
            leftSource,
            rightSource,
            context,
            options
        );
        if (equality.status !== "success") {
            if (equality.code === "budget-exhausted") return equality;
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
        if (!fitsSemanticNbeBudget(
            compactType,
            Core.semanticTypeCheckMaxOutputNodes,
            false,
            context,
            false,
            returnedSchematicMetaNames
        )) {
            return exceedsSemanticNbeNodeBudget(
                compactType,
                Core.semanticTypeCheckMaxOutputNodes
            ) ? { status: "unsupported", code: "budget-exhausted" } : undefined;
        }
        if (!this.commitSemanticSourceMetaConstraints(
            context,
            equality.sourceMetaConstraints
        )) return;

        Core.semanticTypeCheckHits++;
        if (equality.leftTerm) this.applySemanticTerm(ast.nodes[0], equality.leftTerm);
        if (equality.rightTerm) this.applySemanticTerm(ast.nodes[1], equality.rightTerm);
        this.state.bondVarId = Math.max(this.state.bondVarId, nextSemanticBondVarId);
        ast.checked = compactType;
        return ast.checked;
    }

    /** Directional type-pattern matching for #t gates. Candidate ?metas are
     * local to this read-only NbE request. */
    semanticTypePatternMatch(candidate: AST, target: AST, context: Context = []) {
        const candidateSource = this.desugar(Core.clone(candidate), false);
        const targetSource = this.desugar(Core.clone(target), false);
        let nextId = Math.max(
            1,
            ...context.map(([, , id]) => isPositiveBondVarId(id) ? id + 1 : 1)
        );
        const preparedCandidate = prepareSemanticTypePattern(
            candidateSource,
            context,
            nextId,
            true
        );
        nextId = preparedCandidate.nextId;
        const preparedTarget = prepareSemanticTypePattern(
            targetSource,
            context,
            nextId,
            false
        );
        nextId = preparedTarget.nextId;
        // Surface notation such as `+` desugars to constants with implicit
        // universe holes. They are local elaboration details, not user metas.
        if (!fitsSemanticNbeBudget(
            candidateSource,
            Core.semanticTypeAssertionMaxNodes,
            false,
            context,
            true,
            new Set(preparedCandidate.sourceMetas.map(meta => meta.name))
        ) || !fitsSemanticNbeBudget(
            targetSource,
            Core.semanticTypeAssertionMaxNodes,
            false,
            context,
            true
        )) return false;
        const result = this.semanticTypeChecker.tryDefinitionalEquality(
            candidateSource,
            targetSource,
            context,
            {
                maxSteps: Core.semanticTypeAssertionMaxSteps,
                deadline: Date.now() + Core.timeout,
                elaborateMetas: true,
                preserveKernelType: true,
                sourceMetas: preparedCandidate.sourceMetas,
                freshBondVarId: () => nextId++
            }
        );
        return result.status === "success";
    }

    private hasSemanticDefinitionTypeGap(...roots: AST[]) {
        const visited = new WeakSet<object>();
        const stack = [...roots];
        while (stack.length) {
            const node = stack.pop();
            if (!node || typeof node !== "object" || visited.has(node)) continue;
            visited.add(node);
            if (node.type === "var" && !node.bondVarId
                && this.semanticKernel.getDefinitionSource(node.name)
                && !this.semanticTypeChecker.hasConstantType(node.name)) {
                return true;
            }
            for (const child of node.nodes ?? []) stack.push(child);
        }
        return false;
    }
    /**
     * Proof-assistant substitution can retain an obsolete positive binder ID
     * below a cloned binder. Repair only those orphaned occurrences on a
     * throwaway AST; id-less same-name constants must remain free.
     */
    private prepareSemanticProofAssistantNormalizeAst(ast: AST, context: Context) {
        const prepared = Core.clone(ast);
        const scope = new ScopeCursor();
        for (let index = context.length - 1; index >= 0; index--) {
            const [name, , id] = context[index];
            if (isPositiveBondVarId(id)) scope.push({ name, sourceId: id, id });
        }
        const visit = (node: AST): void => {
            if (!node || typeof node !== "object") return;
            if (node.type === "var") {
                if (!isPositiveBondVarId(node.bondVarId)
                    || scope.findById(node.bondVarId)) return;
                const replacement = scope.findByName(node.name);
                if (replacement) node.bondVarId = replacement.id;
                return;
            }
            if (!isBinderNode(node)) {
                for (const child of node.nodes ?? []) visit(child);
                return;
            }
            visit(node.nodes?.[0]);
            if (!isPositiveBondVarId(node.bondVarId)) {
                visit(node.nodes?.[1]);
                return;
            }
            scope.push({ name: node.name, sourceId: node.bondVarId, id: node.bondVarId });
            visit(node.nodes?.[1]);
            scope.pop();
        };
        visit(prepared);
        return prepared;
    }
    private trySemanticProofAssistantNormalize(ast: AST, context: Context) {
        const semanticAst = this.prepareSemanticProofAssistantNormalizeAst(ast, context);
        if (!fitsSemanticNbeBudget(
                semanticAst,
                Core.semanticTypeAssertionMaxNodes,
                false,
                context
            )) return false;

        Core.semanticWhnfAttempts++;
        let nextSemanticBondVarId = Math.max(
            this.state.bondVarId,
            ...context.map(([, , id]) => Number.isFinite(id) ? id + 1 : 0)
        );
        const normalized = this.semanticKernel.tryNormalize(semanticAst, context, {
            deadline: this.state.time ? this.state.time + Core.timeout : undefined,
            maxSteps: Core.semanticTypeAssertionMaxSteps,
            unfoldDefinitions: false,
            freshBondVarId: () => nextSemanticBondVarId++
        });
        if (!normalized) return false;

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
    normalizeExpandedProofGoal(ast: AST, context: Context) {
        const deadline = Date.now() + Core.timeout;
        let nextSemanticBondVarId = Math.max(
            this.state.bondVarId,
            ...context.map(([, , id]) => Number.isFinite(id) ? id + 1 : 0)
        );
        const visit = (node: AST, nodeContext: Context) => {
            if (!node || typeof node !== "object") return;
            if (node.type === "apply") {
                let head = node;
                while (head.type === "apply") head = head.nodes?.[0];
                if (head?.type === "L") {
                    const normalized = this.semanticKernel.tryWhnf(node, nodeContext, {
                        deadline,
                        maxSteps: Core.semanticTypeAssertionMaxSteps,
                        unfoldDefinitions: false,
                        freshBondVarId: () => nextSemanticBondVarId++
                    });
                    if (normalized) Core.assign(node, normalized, true);
                }
            }
            const binder = node.type === "L" || node.type === "P"
                || node.type === "S" || node.type === "W";
            if (node.nodes?.[0]) visit(node.nodes[0], nodeContext);
            if (node.nodes?.[1]) visit(
                node.nodes[1],
                binder
                    ? assignContext([node.name, node.nodes[0], node.bondVarId], nodeContext)
                    : nodeContext
            );
        };
        visit(ast, context);
        this.state.bondVarId = Math.max(this.state.bondVarId, nextSemanticBondVarId);
        this.finalizeSemanticResult(ast, context);
        return ast;
    }
    private trySemanticTypeSynthesis(
        ast: AST,
        context: Context,
        options: {
            allowHoles?: boolean;
            elaborateMetas?: boolean;
            generalizeMetas?: boolean;
            allowUnsolvedTermMetas?: boolean;
            annotateTerm?: boolean;
            requireElaboratedTerm?: boolean;
            captureGeneralizedMetas?: (
                metas: readonly NbeGeneralizedMeta[] | undefined
            ) => void;
            captureElaboratedTerm?: (term: AST | undefined) => void;
            captureFailure?: (failure: NbeTypeFailure) => void;
        } = {}
    ): AST | undefined {
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
            && fitsSemanticNbeBudget(
                semanticAst,
                Core.semanticNbEMaxNodes,
                false,
                context,
                false
            );
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
        let nextSemanticBondVarId = Math.max(
            this.state.bondVarId,
            ...context.map(([, , id]) => Number.isFinite(id) ? id + 1 : 0)
        );
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
            if (elaborated.status === "success") semanticType = elaborated;
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
        if (needsElaboratedTerm && !semanticType.term) return;
        const generalizedMetaNames = new Set(
            semanticType.generalizedMetas?.map(meta => meta.name) ?? []
        );
        for (const name of semanticType.schematicMetaNames ?? []) {
            if (name.startsWith("?")) generalizedMetaNames.add(name);
        }
        // The kernel returns explicit applications such as @eq/@pair.  Fold
        // only their known implicit prefixes back to the internal public
        // aliases used by legacy caches.  This keeps binder shapes and kernel
        // syntax intact while removing elaboration-only arguments.
        // Keep this pre-pass bounded: genuinely huge reifications must still
        // fail before cloning or traversing their complete output.
        if (!fitsSemanticNbeBudget(
            semanticType.type,
            Math.max(Core.semanticNbEMaxNodes, Core.semanticTypeCheckMaxOutputNodes),
            false,
            context,
            false,
            generalizedMetaNames
        )) {
            if (exceedsSemanticNbeNodeBudget(
                semanticType.type,
                Math.max(Core.semanticNbEMaxNodes, Core.semanticTypeCheckMaxOutputNodes)
            )) {
                options.captureFailure?.({
                    status: "unsupported",
                    code: "budget-exhausted"
                });
            }
            return;
        }
        const compactType = this.compactSemanticOutputType(semanticType.type);
        if (!fitsSemanticNbeBudget(
            compactType,
            Core.semanticTypeCheckMaxOutputNodes,
            false,
            context,
            false,
            generalizedMetaNames
        )) {
            if (exceedsSemanticNbeNodeBudget(
                compactType,
                Core.semanticTypeCheckMaxOutputNodes
            )) {
                options.captureFailure?.({
                    status: "unsupported",
                    code: "budget-exhausted"
                });
            }
            return;
        }
        if (!this.commitSemanticSourceMetaConstraints(
            context,
            semanticType.sourceMetaConstraints
        )) return;
        Core.semanticTypeCheckHits++;
        options.captureElaboratedTerm?.(semanticType.elaboratedTerm);
        if (semanticType.term) this.applySemanticTerm(ast, semanticType.term);
        const returnedIds = new Set<number>();
        collectAstBondVarIds(compactType, returnedIds);
        let nextReturnedId = 0;
        for (const id of returnedIds) nextReturnedId = Math.max(nextReturnedId, id + 1);
        this.state.bondVarId = Math.max(nextSemanticBondVarId, nextReturnedId);
        ast.checked = compactType;
        options.captureGeneralizedMetas?.(semanticType.generalizedMetas);
        return ast.checked;
    }
    private semanticTypeFailureMessage(code: NbeTypeErrorCode, ast: AST) {
        const subject = code === "unknown-constant"
            ? this.findUnknownConstantName(ast) ?? this.printSemanticErrorAst(ast)
            : this.printSemanticErrorAst(ast);
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
    /** Find the first free name that is not a registered constant. */
    private findUnknownConstantName(ast: AST, bound = new Set<string>()): string | undefined {
        if (!ast || typeof ast !== "object") return undefined;
        if (ast.type === "var") {
            if (ast.name && !ast.bondVarId && !bound.has(ast.name)
                && !ast.name.startsWith("?") && ast.name !== "_"
                && !NatLiteral.is(ast.name) && !this.hasConst(ast.name)) {
                return ast.name;
            }
            return undefined;
        }
        const first = ast.nodes?.[0];
        const domain = first ? this.findUnknownConstantName(first, bound) : undefined;
        if (domain) return domain;
        const body = ast.nodes?.[1];
        if (!body) return undefined;
        const bodyBound = new Set(bound);
        if (ast.type === "L" || ast.type === "P" || ast.type === "W" || ast.type === "S") {
            if (ast.name) bodyBound.add(ast.name);
        }
        return this.findUnknownConstantName(body, bodyBound);
    }
    private reportSemanticFailure(ast: AST, failure: NbeTypeFailure): never {
        if (failure.code === "budget-exhausted") {
            return this.reportSemanticBudgetFailure(ast);
        }
        this.error(ast, this.semanticTypeFailureMessage(failure.code, ast), true);
        throw new Error("unreachable semantic failure");
    }
    private reportSemanticBudgetFailure(ast: AST): never {
        if (this.state.time && Date.now() - this.state.time >= Core.timeout) {
            Core.timeoutOccured = true;
        }
        this.error(
            ast,
            this.semanticTypeFailureMessage("budget-exhausted", ast),
            true
        );
        throw new Error("unreachable semantic budget failure");
    }
    private printSemanticErrorAst(ast: AST) {
        const surface = this.displaySurfaceNodes.get(ast);
        const printable = Core.clone(surface ?? ast);
        const visited = new WeakSet<object>();
        const hideInferenceNames = (node: AST) => {
            if (!node || typeof node !== "object" || visited.has(node)) return;
            visited.add(node);
            if (node.type === "var" && !node.bondVarId && node.name?.startsWith("?")) {
                node.name = "_";
            }
            for (const child of node.nodes ?? []) hideInferenceNames(child);
            if (node.checked) hideInferenceNames(node.checked);
        };
        hideInferenceNames(printable);
        return parser.stringify(compactImplicitAliasesForDisplay(
            printable,
            this.opaque,
            new Set<string>()
        ));
    }

    private semanticErrorUnresolvedDefinitions(ast: AST) {
        const names = new Set<string>();
        const visited = new WeakSet<object>();
        const visit = (node: AST) => {
            if (!node || typeof node !== "object" || visited.has(node)) return;
            visited.add(node);
            if (node.type === "var" && !node.bondVarId) {
                const source = this.semanticKernel.getDefinitionSource(node.name);
                if (source && !this.semanticKernel.hasDefinition(node.name)
                    && collectInferenceMetaNames(source).size) {
                    names.add(node.name);
                }
            }
            for (const child of node.nodes ?? []) visit(child);
        };
        visit(ast);
        return [...names];
    }

    private captureDisplaySurface(source: AST, surface: AST) {
        this.displaySurfaceNodes = new WeakMap();
        const visited = new WeakSet<object>();
        const visit = (node: AST, sourceNode: AST) => {
            if (!node || !sourceNode || typeof node !== "object" || visited.has(node)) return;
            visited.add(node);
            this.displaySurfaceNodes.set(node, sourceNode);
            const sourceNodes = sourceNode.nodes ?? [];
            const nodes = node.nodes ?? [];
            for (let index = 0; index < Math.min(nodes.length, sourceNodes.length); index++) {
                visit(nodes[index], sourceNodes[index]);
            }
            if (node.checked && sourceNode.checked) visit(node.checked, sourceNode.checked);
        };
        visit(source, surface);
    }
    desugar(ast: AST, allowModify: boolean) {
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
            ast.type = "S"; ast.name = "_";
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
            ast.type = "P"; ast.name = "_";
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
            for (const n of ast.nodes) this.desugar(n, allowModify);
        }
        return ast;
    }
    opaque: [string, number][] = [];
    ensugar(ast: AST) {
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
            if (ali[0].bondVarId) return ast;
            const args = ali.length;
            const fn = ali[0].name;
            if (ali[0].displayExplicitAt) return ast;
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
                    } else {
                        Core.assign(ast, wrapLambda("S", l.name, l.nodes[0], l.nodes[1]), true);
                        ast.bondVarId = l.bondVarId;
                    }
                } else {
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
    hasConst(n: string): boolean {
        if (n.startsWith("?")) return false;
        if (this.state.sysTypes[n] || this.state.sysDefs[n] || this.state.userDefs[n]) {
            return true;
        }
        if (n[0] === "@" && NatLiteral.is(n.slice(1))) return true;
        return !!NatLiteral.is(n);
    }
    flattenApplyList(ast: AST): AST[] {
        const args: AST[] = [];
        let head = ast;
        while (head.type === "apply") {
            args.push(head.nodes[1]);
            head = head.nodes[0];
        }
        args.reverse();
        return [head, ...args];
    }
    static exactEqual(ast1: AST, ast2: AST) {
        if (ast1 === ast2) return true;
        if (ast1.type !== ast2.type) return false;
        if (ast1.type === "var" && ast1.bondVarId && ast1.bondVarId !== ast2.bondVarId) {
            return false;
        }
        if (ast1.name != ast2.name) return false; // undefined == null but !== null
        if (ast1.nodes?.length !== ast2.nodes?.length) return false;
        if (ast1.nodes?.length) {
            for (let i = 0; i < ast1.nodes.length; i++) {
                if (!this.exactEqual(ast1.nodes[i], ast2.nodes[i])) return false;
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
    private instantiateDefinitionForExpansion(definition: AST, context: Context, surrounding?: AST) {
        const clone = Core.clone(definition);
        const seen = new WeakSet<object>();
        let largestId = this.state.bondVarId - 1;
        const reserve = (node: AST) => {
            if (!node || typeof node !== "object" || seen.has(node)) return;
            seen.add(node);
            if (Number.isFinite(node.bondVarId) && node.bondVarId > largestId) {
                largestId = node.bondVarId;
            }
            for (const child of node.nodes ?? []) reserve(child);
            if (node.checked) reserve(node.checked);
        };
        // Existing goal/context ids remain live.  Never allocate one of them
        // for a binder copied out of a stored definition.
        reserve(surrounding);
        for (const [, type, id] of context) {
            if (Number.isFinite(id) && id > largestId) largestId = id;
            reserve(type);
        }
        this.state.bondVarId = Math.max(this.state.bondVarId, largestId + 1);

        const clear = (node: AST, visited = new WeakSet<object>()) => {
            if (!node || typeof node !== "object" || visited.has(node)) return;
            visited.add(node);
            delete node.bondVarId;
            for (const child of node.nodes ?? []) clear(child, visited);
            if (node.checked) clear(node.checked, visited);
        };
        clear(clone);
        return this.markBondVars(clone, context);
    }
    // count: [position to expand, current position]
    expandDef(ast: AST, context: Context, n: string | Set<string>, count = [0, 1]): boolean {

        let found = false;
        if (ast.type === "~=" && (n === "eqv" || (typeof n === "object" && n.has("eqv")))) {
            const expr = this.state.sysDefs["eqv"];
            if (count[0] === 0 || Math.abs(count[0]) === count[1]) {
                Core.assign(ast, wrapApply(
                    this.instantiateDefinitionForExpansion(expr, context, ast),
                    ...ast.nodes
                ));
                count[1]++;
                this.expandDef(ast.nodes[0].nodes[1], context, n, count);
                this.expandDef(ast.nodes[1], context, n, count);
                return true;
            } else {
                count[1]++;
                found = this.expandDef(ast.nodes[0].nodes[1], context, n, count) || found;
                found = this.expandDef(ast.nodes[1], context, n, count) || found;
                return found;
            }
        }
        if (ast.type === "var" && !ast.bondVarId && (
            ast.name === n || (typeof n === "object" && n.has(ast.name))) && !hasContextName(context, ast.name)
        ) {
            const expr = this.state.sysDefs[ast.name] || this.state.userDefs[ast.name];
            if (count[0] === 0 || Math.abs(count[0]) === count[1]) {
                Core.assign(ast, this.instantiateDefinitionForExpansion(expr, context, ast));
                count[1]++;
                return true;
            } else {
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
            } else {
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
    static is(ast: AST | string) {
        if (!ast) return false;
        return typeof ast === "string" ? ast === "0" || ast.match(/^[1-9][0-9]*$/) : ast.type === "var" && (ast.name === "0" || ast.name.match(/^[1-9][0-9]*$/));
    }
}
