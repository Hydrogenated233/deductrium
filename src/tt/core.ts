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
import {
    assertCanonicalHitPathLevels,
    createHitPathLevels,
    flattenHitPathLevels,
    highestHitPathLevel,
    hitPathConstructorCount,
    hitPathConstructorsAt,
    hitPathLevelsFromCanonicalOrLegacy,
    hitPathLevelsFromLegacy,
    legacyHitPathCollectionsFromLevels,
    type HitPathLevels
} from "./hit-path-levels.js";
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

type SemanticTypeSynthesisResourceLimits = Readonly<{
    inputMaxNodes?: number;
    synthesisMaxSteps?: number;
    outputMaxNodes?: number;
}>;

const certifiedPath3ComputationResourceLimits: SemanticTypeSynthesisResourceLimits =
    Object.freeze({
        inputMaxNodes: 4_096,
        synthesisMaxSteps: 131_072,
        outputMaxNodes: 4_096
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
        displayExplicitAt: ast.displayExplicitAt,
        nbeGeneratedMeta: ast.nbeGeneratedMeta
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

export type CoreHitPathConstructorMetadata = {
    name: string;
    argumentTypes: AST[];
    argumentNames?: string[];
    left: AST;
    right: AST;
    /** Common family indices of both point endpoints. Required for indexed hit1. */
    resultIndices?: AST[];
    computationName?: string;
};

/**
 * Canonical v8 expression language for a two-path's first-path endpoint.
 *
 * Atom arguments contain only the constructor-local telescope. Uniform HIT
 * parameters are injected by Core after independently checking the family
 * telescope. Keeping composition and inverse structured prevents a raw AST
 * from becoming trusted path-boundary metadata.
 */
export type CoreHitOnePathExpression =
    | {
        kind: "atom";
        name: string;
        arguments: AST[];
    }
    | {
        kind: "compose";
        left: CoreHitOnePathExpression;
        right: CoreHitOnePathExpression;
    }
    | {
        kind: "inverse";
        value: CoreHitOnePathExpression;
    };

export type CoreHitTwoPathConstructorMetadata = {
    name: string;
    argumentTypes: AST[];
    argumentNames?: string[];
    /** Canonical v8 endpoints. */
    leftExpression?: CoreHitOnePathExpression;
    rightExpression?: CoreHitOnePathExpression;
    /** Legacy v3-v7 atomic endpoints and redundant head names. */
    left?: AST;
    right?: AST;
    leftPath?: string;
    rightPath?: string;
    computationName?: string;
    strongComputationName?: string;
};

/**
 * Canonical v7+ expression language for a three-path endpoint.
 *
 * Atom arguments contain only the constructor-local telescope. Uniform HIT
 * parameters are injected by Core from the independently checked family type.
 * Keeping this language closed prevents arbitrary user ASTs from becoming
 * trusted higher-path structure.
 */
export type CoreHitTwoPathExpression =
    | {
        kind: "atom";
        name: string;
        arguments: AST[];
    }
    | {
        /** Reflexivity at one declared first-path constructor application. */
        kind: "refl";
        pathName: string;
        arguments: AST[];
    }
    | {
        kind: "compose";
        left: CoreHitTwoPathExpression;
        right: CoreHitTwoPathExpression;
    }
    | {
        kind: "inverse";
        value: CoreHitTwoPathExpression;
    };

export type CoreHitThreePathConstructorMetadata = {
    name: string;
    argumentTypes: AST[];
    argumentNames?: string[];
    /** Canonical v7+ endpoints. */
    leftExpression?: CoreHitTwoPathExpression;
    rightExpression?: CoreHitTwoPathExpression;
    /** Legacy v5-v6 direct-atom endpoint and redundant boundary fields. */
    left?: AST;
    right?: AST;
    leftTwoPath?: string;
    rightTwoPath?: string;
    sourcePath?: AST;
    targetPath?: AST;
    computationName?: string;
    actionComputationName?: string;
};

export type CoreHitPathLevels = HitPathLevels<
    CoreHitPathConstructorMetadata,
    CoreHitTwoPathConstructorMetadata,
    CoreHitThreePathConstructorMetadata
>;

export type CoreSystemInductiveMetadata = {
    /** Version 2 distinguishes uniform parameters from family indices. */
    version?: number;
    /** Ordinary inductive data or a higher inductive type. */
    kind?: "inductive" | "hit1" | "hit2" | "hit3";
    /** Highest path dimension represented by this metadata. */
    dimension?: number;
    /** Canonical sandbox compute-rule schema validated by Core. */
    ruleSchemaVersion?: 1;
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
        argumentNames?: string[];
        recursiveArguments?: readonly {
            index: number;
            telescope: readonly { name: string; type: AST }[];
            resultIndices: readonly AST[];
        }[];
        resultIndices?: AST[];
    }[];
    /** Canonical v8 path representation. Legacy v3-v7 metadata remains readable. */
    pathLevels?: CoreHitPathLevels;
    pathConstructors?: readonly CoreHitPathConstructorMetadata[];
    twoPathConstructors?: readonly CoreHitTwoPathConstructorMetadata[];
    threePathConstructors?: readonly CoreHitThreePathConstructorMetadata[];
};

const CORE_HIT_ONE_PATH_EXPRESSION_MAX_DEPTH = 128;
const CORE_HIT_ONE_PATH_EXPRESSION_MAX_NODES = 4_096;
const CORE_HIT_TWO_PATH_EXPRESSION_MAX_DEPTH = 128;
const CORE_HIT_TWO_PATH_EXPRESSION_MAX_NODES = 4_096;
const CORE_HIT_TWO_PATH_LEGACY_FIELDS = [
    "left",
    "right",
    "leftPath",
    "rightPath"
] as const;
const CORE_HIT_THREE_PATH_LEGACY_FIELDS = [
    "left",
    "right",
    "leftTwoPath",
    "rightTwoPath",
    "sourcePath",
    "targetPath"
] as const;

function cloneCoreHitOnePathExpression(
    value: unknown,
    label: string,
    state = { nodes: 0, ancestors: new WeakSet<object>() },
    depth = 0
): CoreHitOnePathExpression {
    if (!value || typeof value !== "object" || Array.isArray(value)) {
        throw new Error(`${label} 一阶路径表达式结构无效`);
    }
    if (depth > CORE_HIT_ONE_PATH_EXPRESSION_MAX_DEPTH) {
        throw new Error(`${label} 一阶路径表达式嵌套过深`);
    }
    if (++state.nodes > CORE_HIT_ONE_PATH_EXPRESSION_MAX_NODES) {
        throw new Error(`${label} 一阶路径表达式节点过多`);
    }
    const object = value as Record<string, unknown>;
    if (state.ancestors.has(object)) {
        throw new Error(`${label} 一阶路径表达式不能循环引用自身`);
    }
    state.ancestors.add(object);
    try {
        if (object.kind === "atom") {
            const keys = Object.keys(object);
            if (keys.some(key => !["kind", "name", "arguments"].includes(key))
                || typeof object.name !== "string" || !object.name
                || !Array.isArray(object.arguments)
                || object.arguments.some(argument => !argument || typeof argument !== "object")) {
                throw new Error(`${label} 一阶路径 atom 结构无效`);
            }
            return {
                kind: "atom",
                name: object.name,
                arguments: (object.arguments as AST[]).map(argument => Core.clone(argument))
            };
        }
        if (object.kind === "compose") {
            const keys = Object.keys(object);
            if (keys.some(key => !["kind", "left", "right"].includes(key))) {
                throw new Error(`${label} 一阶路径 compose 结构无效`);
            }
            return {
                kind: "compose",
                left: cloneCoreHitOnePathExpression(object.left, label, state, depth + 1),
                right: cloneCoreHitOnePathExpression(object.right, label, state, depth + 1)
            };
        }
        if (object.kind === "inverse") {
            const keys = Object.keys(object);
            if (keys.some(key => !["kind", "value"].includes(key))) {
                throw new Error(`${label} 一阶路径 inverse 结构无效`);
            }
            return {
                kind: "inverse",
                value: cloneCoreHitOnePathExpression(object.value, label, state, depth + 1)
            };
        }
        throw new Error(`${label} 一阶路径表达式 kind 无效：${String(object.kind ?? "<空>")}`);
    } finally {
        state.ancestors.delete(object);
    }
}

function mapCoreHitOnePathExpression(
    expression: CoreHitOnePathExpression,
    mapAst: (ast: AST) => AST
): CoreHitOnePathExpression {
    if (expression.kind === "atom") {
        return {
            kind: "atom",
            name: expression.name,
            arguments: expression.arguments.map(mapAst)
        };
    }
    if (expression.kind === "inverse") {
        return {
            kind: "inverse",
            value: mapCoreHitOnePathExpression(expression.value, mapAst)
        };
    }
    return {
        kind: "compose",
        left: mapCoreHitOnePathExpression(expression.left, mapAst),
        right: mapCoreHitOnePathExpression(expression.right, mapAst)
    };
}

function cloneCoreHitTwoPathExpression(
    value: unknown,
    label: string,
    state = { nodes: 0, ancestors: new WeakSet<object>() },
    depth = 0
): CoreHitTwoPathExpression {
    if (!value || typeof value !== "object" || Array.isArray(value)) {
        throw new Error(`${label} 二阶路径表达式结构无效`);
    }
    if (depth > CORE_HIT_TWO_PATH_EXPRESSION_MAX_DEPTH) {
        throw new Error(`${label} 二阶路径表达式嵌套过深`);
    }
    if (++state.nodes > CORE_HIT_TWO_PATH_EXPRESSION_MAX_NODES) {
        throw new Error(`${label} 二阶路径表达式节点过多`);
    }
    const object = value as Record<string, unknown>;
    if (state.ancestors.has(object)) {
        throw new Error(`${label} 二阶路径表达式不能循环引用自身`);
    }
    state.ancestors.add(object);
    try {
        if (object.kind === "atom") {
            const keys = Object.keys(object);
            if (keys.some(key => !["kind", "name", "arguments"].includes(key))
                || typeof object.name !== "string" || !object.name
                || !Array.isArray(object.arguments)
                || object.arguments.some(argument => !argument || typeof argument !== "object")) {
                throw new Error(`${label} 二阶路径 atom 结构无效`);
            }
            return {
                kind: "atom",
                name: object.name,
                arguments: (object.arguments as AST[]).map(argument => Core.clone(argument))
            };
        }
        if (object.kind === "refl") {
            const keys = Object.keys(object);
            if (keys.some(key => !["kind", "pathName", "arguments"].includes(key))
                || typeof object.pathName !== "string" || !object.pathName
                || !Array.isArray(object.arguments)
                || object.arguments.some(argument => !argument || typeof argument !== "object")) {
                throw new Error(`${label} 二阶路径 refl 结构无效`);
            }
            return {
                kind: "refl",
                pathName: object.pathName,
                arguments: (object.arguments as AST[]).map(argument => Core.clone(argument))
            };
        }
        if (object.kind === "compose") {
            const keys = Object.keys(object);
            if (keys.some(key => !["kind", "left", "right"].includes(key))) {
                throw new Error(`${label} 二阶路径 compose 结构无效`);
            }
            return {
                kind: "compose",
                left: cloneCoreHitTwoPathExpression(object.left, label, state, depth + 1),
                right: cloneCoreHitTwoPathExpression(object.right, label, state, depth + 1)
            };
        }
        if (object.kind === "inverse") {
            const keys = Object.keys(object);
            if (keys.some(key => !["kind", "value"].includes(key))) {
                throw new Error(`${label} 二阶路径 inverse 结构无效`);
            }
            return {
                kind: "inverse",
                value: cloneCoreHitTwoPathExpression(object.value, label, state, depth + 1)
            };
        }
        throw new Error(`${label} 二阶路径表达式 kind 无效：${String(object.kind ?? "<空>")}`);
    } finally {
        state.ancestors.delete(object);
    }
}

function legacyCoreHitOnePathExpression(
    endpoint: AST | undefined,
    expectedName: string | undefined,
    parameterCount: number,
    label: string
): CoreHitOnePathExpression {
    if (!endpoint || !expectedName) {
        throw new Error(`${label} legacy 二阶路径端点 metadata 不完整`);
    }
    const application = generatedApplicationParts(endpoint);
    const name = generatedFreeConstantName(application.head);
    if (!name || name !== expectedName) {
        throw new Error(
            `${label} legacy 二阶路径端点头与 metadata 不一致：`
            + `${name ?? "<非常量>"} != ${expectedName}`
        );
    }
    if (application.arguments.length < parameterCount) {
        throw new Error(`${label} legacy 二阶路径端点缺少统一参数`);
    }
    return {
        kind: "atom",
        name,
        arguments: application.arguments.slice(parameterCount).map(argument => Core.clone(argument))
    };
}

function migrateLegacyCoreHitTwoPathMetadata(
    path: CoreHitTwoPathConstructorMetadata,
    parameterCount: number
): CoreHitTwoPathConstructorMetadata {
    const label = `二维 HIT 二阶路径构造子 ${path.name}`;
    const leftExpression = legacyCoreHitOnePathExpression(
        path.left, path.leftPath, parameterCount, `${label} 左端点`
    );
    const rightExpression = legacyCoreHitOnePathExpression(
        path.right, path.rightPath, parameterCount, `${label} 右端点`
    );
    const {
        left: _left,
        right: _right,
        leftPath: _leftPath,
        rightPath: _rightPath,
        ...common
    } = path;
    return { ...common, leftExpression, rightExpression };
}

function legacyCoreHitTwoPathExpression(
    endpoint: AST | undefined,
    expectedName: string | undefined,
    parameterCount: number,
    label: string
): CoreHitTwoPathExpression {
    if (!endpoint || !expectedName) {
        throw new Error(`${label} legacy 三阶路径端点 metadata 不完整`);
    }
    const application = generatedApplicationParts(endpoint);
    const name = generatedFreeConstantName(application.head);
    if (!name || name !== expectedName) {
        throw new Error(
            `${label} legacy 三阶路径端点头与 metadata 不一致：`
            + `${name ?? "<非常量>"} != ${expectedName}`
        );
    }
    if (application.arguments.length < parameterCount) {
        throw new Error(`${label} legacy 三阶路径端点缺少统一参数`);
    }
    return {
        kind: "atom",
        name,
        arguments: application.arguments.slice(parameterCount).map(argument => Core.clone(argument))
    };
}

function migrateLegacyCoreHitThreePathMetadata(
    path: CoreHitThreePathConstructorMetadata,
    twoPathByName: ReadonlyMap<string, CoreHitTwoPathConstructorMetadata>,
    parameterCount: number
): CoreHitThreePathConstructorMetadata {
    const label = `三维 HIT 三阶路径构造子 ${path.name}`;
    const leftExpression = legacyCoreHitTwoPathExpression(
        path.left, path.leftTwoPath, parameterCount, `${label} 左端点`
    );
    const rightExpression = legacyCoreHitTwoPathExpression(
        path.right, path.rightTwoPath, parameterCount, `${label} 右端点`
    );
    if (!path.sourcePath || !path.targetPath) {
        throw new Error(`${label} legacy 边界 metadata 不完整`);
    }

    const boundaryFor = (expression: CoreHitTwoPathExpression, side: string) => {
        if (expression.kind !== "atom") throw new Error(`${label} ${side}端点不是 direct atom`);
        const referenced = twoPathByName.get(expression.name);
        if (!referenced) {
            throw new Error(`${label} ${side}端点引用不存在：${expression.name}`);
        }
        if (!referenced.left || !referenced.right) {
            throw new Error(`${label} ${side}端点引用缺少 legacy 边界 metadata`);
        }
        const argumentNames = referenced.argumentNames ?? [];
        if (argumentNames.length !== referenced.argumentTypes.length
            || expression.arguments.length !== argumentNames.length) {
            throw new Error(`${label} ${side}端点参数数量与二阶路径 metadata 不一致`);
        }
        const replacements = new Map<string, AST>();
        argumentNames.forEach((name, index) => replacements.set(name, expression.arguments[index]));
        return {
            sourcePath: substituteGeneratedFreeNames(referenced.left, replacements),
            targetPath: substituteGeneratedFreeNames(referenced.right, replacements)
        };
    };
    const leftBoundary = boundaryFor(leftExpression, "左");
    const rightBoundary = boundaryFor(rightExpression, "右");
    if (!sameGeneratedAstAlpha(leftBoundary.sourcePath, rightBoundary.sourcePath)
        || !sameGeneratedAstAlpha(leftBoundary.targetPath, rightBoundary.targetPath)) {
        throw new Error(`${label} 的 legacy 二阶路径边界不一致`);
    }
    if (!sameGeneratedAstAlpha(leftBoundary.sourcePath, path.sourcePath)
        || !sameGeneratedAstAlpha(leftBoundary.targetPath, path.targetPath)) {
        throw new Error(`${label} 的 legacy 边界 metadata 不一致`);
    }

    const {
        left: _left,
        right: _right,
        leftTwoPath: _leftTwoPath,
        rightTwoPath: _rightTwoPath,
        sourcePath: _sourcePath,
        targetPath: _targetPath,
        ...common
    } = path;
    return { ...common, leftExpression, rightExpression };
}

function reconstructCoreHitEndpointResultIndices(
    metadata: CoreSystemInductiveMetadata,
    endpoint: AST,
    label: string
) {
    const parameterCount = Number(metadata.parameterCount ?? 0);
    const indexCount = Number(metadata.indexCount ?? 0);
    const application = generatedApplicationParts(endpoint);
    const constructorName = generatedFreeConstantName(application.head) ?? "";
    const constructor = metadata.constructors.find(candidate =>
        candidate.name === constructorName
    );
    if (!constructor) {
        throw new Error(`${label} 引用了未知点构造子：${constructorName || "<非常量>"}`);
    }
    const argumentNames = constructor.argumentNames ?? [];
    if (argumentNames.length !== constructor.argumentTypes.length
        || new Set(argumentNames).size !== argumentNames.length) {
        throw new Error(`${label} 点构造子 ${constructorName} argumentNames 与 telescope 不一致`);
    }
    if (application.arguments.length !== parameterCount + argumentNames.length) {
        throw new Error(`${label} 点构造子 ${constructorName} 参数数量与 metadata 不一致`);
    }
    const constructorResultIndices = constructor.resultIndices ?? [];
    if (constructorResultIndices.length !== indexCount) {
        throw new Error(`${label} 点构造子 ${constructorName} 返回索引 metadata 不完整`);
    }
    const replacements = new Map<string, AST>();
    argumentNames.forEach((name, index) => {
        replacements.set(name, application.arguments[parameterCount + index]);
    });
    return constructorResultIndices.map(index =>
        substituteGeneratedFreeNames(index, replacements)
    );
}

function normalizeCoreSystemInductiveMetadata(
    metadata: CoreSystemInductiveMetadata
): CoreSystemInductiveMetadata {
    const isHit = metadata.kind === "hit1"
        || metadata.kind === "hit2"
        || metadata.kind === "hit3";
    if (!isHit) {
        let hasPathConstructors = false;
        if (metadata.pathLevels !== undefined) {
            assertCanonicalHitPathLevels(metadata.pathLevels);
            hasPathConstructors = hitPathConstructorCount(metadata.pathLevels) > 0;
        }
        hasPathConstructors ||= [
            metadata.pathConstructors,
            metadata.twoPathConstructors,
            metadata.threePathConstructors
        ].some(constructors => Array.isArray(constructors) && constructors.length > 0);
        if (hasPathConstructors) {
            throw new Error(
                `非 HIT metadata ${metadata.kind ?? "<空>"} 不能包含路径构造子`
            );
        }
        return metadata;
    }

    const version = Number(metadata.version ?? 0);
    if (version <= 1) return metadata;
    if (![3, 4, 5, 6, 7, 8].includes(version)) {
        throw new Error(`不支持的 HIT metadata 版本：${version || "<空>"}`);
    }
    let sourceLevels: CoreHitPathLevels;
    if (version >= 6) {
        if (!metadata.pathLevels) {
            throw new Error(`HIT metadata v${version} 缺少 canonical pathLevels`);
        }
        if (metadata.pathConstructors !== undefined
            || metadata.twoPathConstructors !== undefined
            || metadata.threePathConstructors !== undefined) {
            throw new Error(`HIT metadata v${version} 不能同时携带 legacy 路径字段`);
        }
        assertCanonicalHitPathLevels(metadata.pathLevels);
        sourceLevels = metadata.pathLevels;
    } else {
        if (metadata.pathLevels !== undefined) {
            throw new Error(`legacy HIT metadata v${version} 不能携带 pathLevels`);
        }
        sourceLevels = hitPathLevelsFromLegacy(metadata);
        assertCanonicalHitPathLevels(sourceLevels);
    }

    const indexCount = Number(metadata.indexCount ?? 0);
    const sourcePathConstructors = hitPathConstructorsAt(sourceLevels, 1);
    const pathConstructors = sourcePathConstructors.map(path => {
        if (version >= 7) {
            const allowedFields = new Set([
                "name",
                "argumentTypes",
                "argumentNames",
                "left",
                "right",
                "resultIndices",
                "computationName"
            ]);
            if (Object.keys(path).some(field => !allowedFields.has(field))) {
                throw new Error(`HIT metadata v${version} 一阶路径构造子 ${path.name} 包含未知字段`);
            }
        }
        const hasResultIndices = Array.isArray(path.resultIndices);
        if (indexCount > 0 && version >= 7 && !hasResultIndices) {
            throw new Error(`indexed hit1 路径构造子 ${path.name} 缺少 resultIndices`);
        }
        if (path.resultIndices !== undefined && !hasResultIndices) {
            throw new Error(`HIT 路径构造子 ${path.name} 的 resultIndices 结构无效`);
        }
        let resultIndices = hasResultIndices
            ? path.resultIndices!.map(index => Core.clone(index))
            : [];
        if (resultIndices.length !== indexCount) {
            if (version >= 7 || resultIndices.length) {
                throw new Error(`HIT 路径构造子 ${path.name} 的 resultIndices 数量与索引不一致`);
            }
            const leftIndices = reconstructCoreHitEndpointResultIndices(
                metadata, path.left, `legacy HIT 路径构造子 ${path.name} 左端点`
            );
            resultIndices = leftIndices;
        }
        return {
            name: path.name,
            argumentTypes: path.argumentTypes.map(type => Core.clone(type)),
            argumentNames: path.argumentNames ? [...path.argumentNames] : undefined,
            left: Core.clone(path.left),
            right: Core.clone(path.right),
            resultIndices,
            computationName: path.computationName
        };
    });
    const sourceTwoPathConstructors = hitPathConstructorsAt(sourceLevels, 2);
    const legacyTwoPathByName = new Map(
        sourceTwoPathConstructors.map(path => [path.name, path] as const)
    );
    const twoPathConstructors = sourceTwoPathConstructors.map(path => {
        if (version <= 7) {
            return migrateLegacyCoreHitTwoPathMetadata(
                path,
                Number(metadata.parameterCount ?? 0)
            );
        }
        const allowedFields = new Set([
            "name",
            "argumentTypes",
            "argumentNames",
            "leftExpression",
            "rightExpression",
            "computationName",
            "strongComputationName"
        ]);
        if (CORE_HIT_TWO_PATH_LEGACY_FIELDS.some(field =>
            Object.prototype.hasOwnProperty.call(path, field))) {
            throw new Error(`HIT metadata v8 二阶路径构造子 ${path.name} 不能携带 legacy 冗余字段`);
        }
        if (Object.keys(path).some(field => !allowedFields.has(field))) {
            throw new Error(`HIT metadata v8 二阶路径构造子 ${path.name} 包含未知字段`);
        }
        if (!path.leftExpression || !path.rightExpression) {
            throw new Error(`HIT metadata v8 二阶路径构造子 ${path.name} 缺少表达式端点`);
        }
        return {
            name: path.name,
            argumentTypes: path.argumentTypes.map(type => Core.clone(type)),
            argumentNames: path.argumentNames ? [...path.argumentNames] : undefined,
            leftExpression: cloneCoreHitOnePathExpression(
                path.leftExpression, `二阶路径构造子 ${path.name} 左端点`
            ),
            rightExpression: cloneCoreHitOnePathExpression(
                path.rightExpression, `二阶路径构造子 ${path.name} 右端点`
            ),
            computationName: path.computationName,
            strongComputationName: path.strongComputationName
        };
    });
    const sourceThreePathConstructors = hitPathConstructorsAt(sourceLevels, 3);
    const threePathConstructors = sourceThreePathConstructors.map(path => {
        if (version <= 6) {
            return migrateLegacyCoreHitThreePathMetadata(
                path,
                legacyTwoPathByName,
                Number(metadata.parameterCount ?? 0)
            );
        }
        if (CORE_HIT_THREE_PATH_LEGACY_FIELDS.some(field =>
            Object.prototype.hasOwnProperty.call(path, field))) {
            throw new Error(`HIT metadata v${version} 三阶路径构造子 ${path.name} 不能携带 legacy 冗余字段`);
        }
        if (!path.leftExpression || !path.rightExpression) {
            throw new Error(`HIT metadata v${version} 三阶路径构造子 ${path.name} 缺少表达式端点`);
        }
        return {
            ...path,
            leftExpression: cloneCoreHitTwoPathExpression(
                path.leftExpression, `三阶路径构造子 ${path.name} 左端点`
            ),
            rightExpression: cloneCoreHitTwoPathExpression(
                path.rightExpression, `三阶路径构造子 ${path.name} 右端点`
            )
        };
    });
    const pathLevels = createHitPathLevels(
        pathConstructors,
        twoPathConstructors,
        threePathConstructors
    );
    const dimension = highestHitPathLevel(pathLevels);
    const expectedKind = dimension === 3 ? "hit3" : dimension === 2 ? "hit2" : "hit1";
    if (metadata.dimension !== dimension || metadata.kind !== expectedKind) {
        throw new Error(
            `HIT metadata 摘要与 pathLevels 不一致：${metadata.kind ?? ""}/`
            + `${metadata.dimension ?? ""} != ${expectedKind}/${dimension}`
        );
    }
    if (version < 6 && version !== dimension + 2) {
        throw new Error(`legacy HIT metadata v${version} 与维度 ${dimension} 不一致`);
    }
    const {
        pathLevels: _pathLevels,
        pathConstructors: _pathConstructors,
        twoPathConstructors: _twoPathConstructors,
        threePathConstructors: _threePathConstructors,
        ...common
    } = metadata;
    return {
        ...common,
        version: 8,
        kind: expectedKind,
        dimension,
        pathLevels,
    };
}

export function cloneCoreHitPathMetadata(metadata: CoreSystemInductiveMetadata) {
    const canonical = normalizeCoreSystemInductiveMetadata(metadata);
    const sourceLevels = hitPathLevelsFromCanonicalOrLegacy(canonical);
    const pathLevels: CoreHitPathLevels = createHitPathLevels(
        hitPathConstructorsAt(sourceLevels, 1).map(ctor => ({
            name: ctor.name,
            argumentTypes: ctor.argumentTypes.map(type => Core.clone(type)),
            argumentNames: ctor.argumentNames ? [...ctor.argumentNames] : undefined,
            left: Core.clone(ctor.left),
            right: Core.clone(ctor.right),
            resultIndices: (ctor.resultIndices ?? []).map(index => Core.clone(index)),
            computationName: ctor.computationName
        })),
        hitPathConstructorsAt(sourceLevels, 2).map(ctor => ({
            name: ctor.name,
            argumentTypes: ctor.argumentTypes.map(type => Core.clone(type)),
            argumentNames: ctor.argumentNames ? [...ctor.argumentNames] : undefined,
            leftExpression: cloneCoreHitOnePathExpression(
                ctor.leftExpression,
                `二阶路径构造子 ${ctor.name} 左端点`
            ),
            rightExpression: cloneCoreHitOnePathExpression(
                ctor.rightExpression,
                `二阶路径构造子 ${ctor.name} 右端点`
            ),
            computationName: ctor.computationName,
            strongComputationName: ctor.strongComputationName
        })),
        hitPathConstructorsAt(sourceLevels, 3).map(ctor => ({
            name: ctor.name,
            argumentTypes: ctor.argumentTypes.map(type => Core.clone(type)),
            argumentNames: ctor.argumentNames ? [...ctor.argumentNames] : undefined,
            leftExpression: cloneCoreHitTwoPathExpression(
                ctor.leftExpression,
                `三阶路径构造子 ${ctor.name} 左端点`
            ),
            rightExpression: cloneCoreHitTwoPathExpression(
                ctor.rightExpression,
                `三阶路径构造子 ${ctor.name} 右端点`
            ),
            computationName: ctor.computationName,
            actionComputationName: ctor.actionComputationName
        }))
    );
    if (canonical.version === 1) {
        const legacy = legacyHitPathCollectionsFromLevels(pathLevels);
        return {
            pathConstructors: [...legacy.pathConstructors],
            twoPathConstructors: [...legacy.twoPathConstructors],
            threePathConstructors: [...legacy.threePathConstructors]
        };
    }
    return { pathLevels };
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
    metadata?: CoreSystemInductiveMetadata;
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
    certifiedLargeSystemTypes: string[];
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

type GeneratedBinderIdentity = { name: string; id?: number };

function generatedBinderPosition(ast: AST, scope: readonly GeneratedBinderIdentity[]) {
    for (let index = scope.length - 1; index >= 0; index--) {
        const binder = scope[index];
        if (ast.bondVarId && binder.id === ast.bondVarId) return scope.length - 1 - index;
        if (!ast.bondVarId && ast.name === binder.name) return scope.length - 1 - index;
    }
    return -1;
}

function sameGeneratedAstAlpha(
    left: AST,
    right: AST,
    leftScope: readonly GeneratedBinderIdentity[] = [],
    rightScope: readonly GeneratedBinderIdentity[] = []
): boolean {
    if (left === right) return true;
    if (!left || !right || left.type !== right.type) return false;
    if (left.type === "var") {
        const leftPosition = generatedBinderPosition(left, leftScope);
        const rightPosition = generatedBinderPosition(right, rightScope);
        if (leftPosition >= 0 || rightPosition >= 0) return leftPosition === rightPosition;
        return left.name === right.name;
    }
    const leftNodes = left.nodes ?? [];
    const rightNodes = right.nodes ?? [];
    if (leftNodes.length !== rightNodes.length) return false;
    if (isBinderNode(left) && isBinderNode(right) && leftNodes.length >= 2) {
        if (!sameGeneratedAstAlpha(leftNodes[0], rightNodes[0], leftScope, rightScope)) return false;
        const nextLeft = [...leftScope, { name: left.name, id: left.bondVarId }];
        const nextRight = [...rightScope, { name: right.name, id: right.bondVarId }];
        if (!sameGeneratedAstAlpha(leftNodes[1], rightNodes[1], nextLeft, nextRight)) return false;
        for (let index = 2; index < leftNodes.length; index++) {
            if (!sameGeneratedAstAlpha(leftNodes[index], rightNodes[index], leftScope, rightScope)) return false;
        }
        return true;
    }
    return left.name === right.name
        && leftNodes.every((node, index) =>
            sameGeneratedAstAlpha(node, rightNodes[index], leftScope, rightScope));
}

function substituteGeneratedFreeNames(
    ast: AST,
    replacements: ReadonlyMap<string, AST>,
    bound = new Set<string>()
): AST {
    if (ast.type === "var") {
        const replacement = !bound.has(ast.name) ? replacements.get(ast.name) : undefined;
        return replacement ? Core.clone(replacement) : Core.clone(ast);
    }
    if (isBinderNode(ast) && ast.nodes?.[0] && ast.nodes?.[1]) {
        const nextBound = new Set(bound);
        if (ast.name) nextBound.add(ast.name);
        return {
            type: ast.type,
            name: ast.name,
            bondVarId: ast.bondVarId,
            nodes: [
                substituteGeneratedFreeNames(ast.nodes[0], replacements, bound),
                substituteGeneratedFreeNames(ast.nodes[1], replacements, nextBound),
                ...ast.nodes.slice(2).map(node =>
                    substituteGeneratedFreeNames(node, replacements, bound))
            ]
        };
    }
    return {
        type: ast.type,
        name: ast.name,
        bondVarId: ast.bondVarId,
        nodes: ast.nodes?.map(node => substituteGeneratedFreeNames(node, replacements, bound))
    };
}

function generatedTelescopeArity(ast: AST) {
    let arity = 0;
    let cursor = ast;
    while ((cursor.type === "P" || cursor.type === "->")
        && cursor.nodes?.[0] && cursor.nodes?.[1]) {
        arity++;
        cursor = cursor.nodes[1];
    }
    return arity;
}

function generatedApplicationParts(ast: AST): { head: AST; arguments: AST[] } {
    const arguments_: AST[] = [];
    let head = ast;
    while (head.type === "apply" && head.nodes?.[0] && head.nodes?.[1]) {
        arguments_.push(head.nodes[1]);
        head = head.nodes[0];
    }
    arguments_.reverse();
    return { head, arguments: arguments_ };
}

function generatedFreeConstantName(ast: AST): string | undefined {
    const head = generatedApplicationParts(ast).head;
    return head.type === "var" && !head.bondVarId && head.name
        ? head.name
        : undefined;
}

function generatedContainsFreeConstant(ast: AST, name: string): boolean {
    const stack = [ast];
    const seen = new WeakSet<object>();
    while (stack.length) {
        const node = stack.pop();
        if (!node || typeof node !== "object" || seen.has(node)) continue;
        seen.add(node);
        if (node.type === "var" && !node.bondVarId && node.name === name) return true;
        for (const child of node.nodes ?? []) stack.push(child);
    }
    return false;
}

function generatedStrictRecursiveArgument(type: AST, familyName: string): boolean {
    let cursor = type;
    while ((cursor.type === "P" || cursor.type === "->")
        && cursor.nodes?.[0] && cursor.nodes?.[1]) {
        if (generatedContainsFreeConstant(cursor.nodes[0], familyName)) return false;
        cursor = cursor.nodes[1];
    }
    return generatedFreeConstantName(cursor) === familyName;
}

function validateSystemInductiveComputeRules(
    bundle: CoreSystemInductiveBundle,
    rulesByHead: Readonly<Record<string, readonly { pattern: AST[]; result: AST }[]>>,
    parameters: readonly { name: string; type: AST }[],
    indexCount: number,
    constructorTypes: ReadonlyMap<string, AST>,
    normalizeAst: (ast: AST) => AST
) {
    const parameterCount = parameters.length;
    const auxiliaryNames = new Set((bundle.auxiliaryTypes ?? []).map(([name]) => name));
    const allowedHeads = new Set<string>();
    const addEliminationHead = (entry: readonly [string, AST] | undefined) => {
        if (!entry) return;
        allowedHeads.add(entry[0]);
        const fullAlias = `@${entry[0]}`;
        if (auxiliaryNames.has(fullAlias)) allowedHeads.add(fullAlias);
    };
    addEliminationHead(bundle.eliminator);
    addEliminationHead(bundle.recursor);

    type StrictConstructorSchema = {
        name: string;
        argumentTypes: AST[];
        argumentNames: string[];
        recursiveArguments: {
            index: number;
            telescope: { name: string; type: AST }[];
            resultIndices: AST[];
        }[];
        resultIndices: AST[];
    };
    type StrictHeadProfile = {
        full: boolean;
        staticCount: number;
        totalArity: number;
        constructorBranchOffset: number;
    };
    const strictSchema = bundle.metadata?.ruleSchemaVersion === 1;
    const strictConstructors = new Map<string, StrictConstructorSchema>();
    const strictHeadProfiles = new Map<string, StrictHeadProfile>();
    if (strictSchema) {
        const metadata = bundle.metadata!;
        const constructorCount = metadata.constructors.length;
        const coherenceCount = hitPathConstructorCount(
            hitPathLevelsFromCanonicalOrLegacy(metadata)
        );
        for (const constructor of metadata.constructors) {
            if (!Array.isArray(constructor.argumentNames)
                || constructor.argumentNames.length !== constructor.argumentTypes.length
                || !Array.isArray(constructor.recursiveArguments)
                || !Array.isArray(constructor.resultIndices)
                || constructor.resultIndices.length !== indexCount) {
                throw new Error(`归纳计算规则 schema 构造子 metadata 不完整：${constructor.name}`);
            }
            const recursiveIndexes = new Set<number>();
            for (const recursive of constructor.recursiveArguments) {
                if (!Number.isInteger(recursive.index)
                    || recursive.index < 0
                    || recursive.index >= constructor.argumentTypes.length
                    || recursiveIndexes.has(recursive.index)
                    || !Array.isArray(recursive.telescope)
                    || !Array.isArray(recursive.resultIndices)
                    || recursive.resultIndices.length !== indexCount) {
                    throw new Error(`归纳计算规则 schema 递归参数 metadata 无效：${constructor.name}`);
                }
                recursiveIndexes.add(recursive.index);
            }
            strictConstructors.set(constructor.name, {
                name: constructor.name,
                argumentTypes: constructor.argumentTypes.map(normalizeAst),
                argumentNames: [...constructor.argumentNames],
                recursiveArguments: constructor.recursiveArguments.map(recursive => ({
                    index: recursive.index,
                    telescope: recursive.telescope.map(binder => ({
                        name: binder.name,
                        type: normalizeAst(binder.type)
                    })),
                    resultIndices: recursive.resultIndices.map(normalizeAst)
                })),
                resultIndices: constructor.resultIndices.map(normalizeAst)
            });
        }

        const auxiliaryTypes = new Map(
            (bundle.auxiliaryTypes ?? []).map(([name, type]) => [name, normalizeAst(type)] as const)
        );
        const profiles: { name: string | undefined; type: AST | undefined; full: boolean }[] = [
            { name: metadata.eliminatorName, type: bundle.eliminator?.[1], full: false },
            { name: metadata.fullEliminatorName, type: metadata.fullEliminatorName
                ? auxiliaryTypes.get(metadata.fullEliminatorName) : undefined, full: true },
            { name: metadata.recursorName, type: bundle.recursor?.[1], full: false },
            { name: metadata.fullRecursorName, type: metadata.fullRecursorName
                ? auxiliaryTypes.get(metadata.fullRecursorName) : undefined, full: true }
        ];
        for (const profile of profiles) {
            if (!profile.name || !profile.type || !allowedHeads.has(profile.name)) {
                throw new Error(`归纳计算规则 schema 缺少消去器槽位：${profile.name ?? ""}`);
            }
            const staticCount = (profile.full ? 1 : 0)
                + parameterCount + 1 + constructorCount + coherenceCount;
            const totalArity = staticCount + indexCount + 1;
            const normalizedType = normalizeAst(profile.type);
            if (generatedTelescopeArity(normalizedType) !== totalArity) {
                throw new Error(`归纳计算规则 ${profile.name} 参数数量与消去器类型不一致`);
            }
            strictHeadProfiles.set(profile.name, {
                full: profile.full,
                staticCount,
                totalArity,
                constructorBranchOffset: (profile.full ? 1 : 0) + parameterCount + 1
            });
        }
    }

    const constructorNames = new Set(bundle.constructors.map(([name]) => name));
    const metadataConstructors = new Map(
        (bundle.metadata?.constructors ?? []).map(constructor => [constructor.name, constructor] as const)
    );
    if (strictSchema) {
        for (const schema of strictConstructors.values()) {
            let cursor = constructorTypes.get(schema.name);
            if (!cursor) throw new Error(`归纳计算规则 schema 缺少点构造子：${schema.name}`);
            const binders: { kind: string; name: string; type: AST }[] = [];
            while ((cursor.type === "P" || cursor.type === "->")
                && cursor.nodes?.[0] && cursor.nodes?.[1]) {
                binders.push({ kind: cursor.type, name: cursor.name, type: cursor.nodes[0] });
                cursor = cursor.nodes[1];
            }
            if (binders.length !== parameterCount + schema.argumentTypes.length) {
                throw new Error(`点构造子 ${schema.name} 参数数量与计算规则 schema 不一致`);
            }
            for (let index = 0; index < parameterCount; index++) {
                const actual = binders[index];
                const expected = parameters[index];
                if (actual.kind !== "P" || actual.name !== expected.name
                    || !sameGeneratedAstAlpha(actual.type, expected.type)) {
                    throw new Error(`点构造子 ${schema.name} 未保持统一参数：${expected.name}`);
                }
            }
            for (let index = 0; index < schema.argumentTypes.length; index++) {
                const actual = binders[parameterCount + index];
                if (actual.kind !== "P" || actual.name !== schema.argumentNames[index]
                    || !sameGeneratedAstAlpha(actual.type, schema.argumentTypes[index])) {
                    throw new Error(`点构造子 ${schema.name} 第 ${index + 1} 个参数与计算规则 schema 不一致`);
                }
            }
            const expectedResult = wrapApply(
                wrapVar(bundle.type[0]),
                ...parameters.map(parameter => wrapVar(parameter.name)),
                ...schema.resultIndices.map(index => Core.clone(index))
            );
            if (!sameGeneratedAstAlpha(cursor, expectedResult)) {
                throw new Error(`点构造子 ${schema.name} 结论索引与计算规则 metadata 不一致`);
            }

            const recursiveByIndex = new Map(
                schema.recursiveArguments.map(recursive => [recursive.index, recursive] as const)
            );
            for (let index = 0; index < schema.argumentTypes.length; index++) {
                const argumentType = schema.argumentTypes[index];
                const recursive = recursiveByIndex.get(index);
                const isRecursive = generatedStrictRecursiveArgument(argumentType, bundle.type[0]);
                if (!!recursive !== isRecursive) {
                    throw new Error(`点构造子 ${schema.name} 第 ${index + 1} 个递归参数 metadata 不一致`);
                }
                if (!recursive) {
                    if (generatedContainsFreeConstant(argumentType, bundle.type[0])) {
                        throw new Error(`点构造子 ${schema.name} 含有无法证明严格正的递归参数`);
                    }
                    continue;
                }

                const actualTelescope: { name: string; type: AST }[] = [];
                let recursiveResult = argumentType;
                while ((recursiveResult.type === "P" || recursiveResult.type === "->")
                    && recursiveResult.nodes?.[0] && recursiveResult.nodes?.[1]) {
                    actualTelescope.push({
                        name: recursiveResult.type === "P" ? recursiveResult.name : "",
                        type: recursiveResult.nodes[0]
                    });
                    recursiveResult = recursiveResult.nodes[1];
                }
                if (actualTelescope.length !== recursive.telescope.length) {
                    throw new Error(`点构造子 ${schema.name} 递归 telescope 与 metadata 不一致`);
                }
                const telescopeRenames = new Map<string, AST>();
                for (let telescopeIndex = 0; telescopeIndex < actualTelescope.length; telescopeIndex++) {
                    const actual = actualTelescope[telescopeIndex];
                    const expected = recursive.telescope[telescopeIndex];
                    const actualType = substituteGeneratedFreeNames(actual.type, telescopeRenames);
                    if (!sameGeneratedAstAlpha(actualType, expected.type)) {
                        throw new Error(`点构造子 ${schema.name} 递归 telescope 类型与 metadata 不一致`);
                    }
                    if (actual.name) {
                        telescopeRenames.set(actual.name, wrapVar(expected.name));
                    }
                }
                const recursiveApplication = generatedApplicationParts(recursiveResult);
                if (generatedFreeConstantName(recursiveApplication.head) !== bundle.type[0]
                    || recursiveApplication.arguments.length !== parameterCount + indexCount) {
                    throw new Error(`点构造子 ${schema.name} 递归结果类型与 metadata 不一致`);
                }
                for (let parameterIndex = 0; parameterIndex < parameterCount; parameterIndex++) {
                    if (!sameGeneratedAstAlpha(
                        recursiveApplication.arguments[parameterIndex],
                        wrapVar(parameters[parameterIndex].name)
                    )) {
                        throw new Error(`点构造子 ${schema.name} 递归结果未保持统一参数`);
                    }
                }
                const actualIndices = recursiveApplication.arguments.slice(parameterCount)
                    .map(index => substituteGeneratedFreeNames(index, telescopeRenames));
                if (actualIndices.length !== recursive.resultIndices.length
                    || actualIndices.some((value, resultIndex) =>
                        !sameGeneratedAstAlpha(value, recursive.resultIndices[resultIndex]))) {
                    throw new Error(`点构造子 ${schema.name} 递归结果索引与 metadata 不一致`);
                }
            }
        }
    }
    const recursiveArgumentIndexes = new Map<string, Set<number>>();
    for (const constructorName of constructorNames) {
        let argumentTypes = metadataConstructors.get(constructorName)?.argumentTypes;
        if (!argumentTypes) {
            argumentTypes = [];
            let cursor = constructorTypes.get(constructorName);
            let binderIndex = 0;
            while (cursor && (cursor.type === "P" || cursor.type === "->")
                && cursor.nodes?.[0] && cursor.nodes?.[1]) {
                if (binderIndex >= parameterCount) argumentTypes.push(cursor.nodes[0]);
                binderIndex++;
                cursor = cursor.nodes[1];
            }
        }
        const indexes = new Set<number>();
        argumentTypes.forEach((type, index) => {
            if (generatedStrictRecursiveArgument(type, bundle.type[0])) indexes.add(index);
        });
        recursiveArgumentIndexes.set(constructorName, indexes);
    }
    const constructorRuleOwners = new Set<string>();
    const aritiesByHead = new Map<string, Set<number>>();
    const rulePolicies: {
        head: string;
        rule: { pattern: AST[]; result: AST };
        recursiveDataRoots: Set<string>;
    }[] = [];
    const containsAnonymousHole = (ast: AST) => {
        const stack = [ast];
        const seen = new WeakSet<object>();
        while (stack.length) {
            const node = stack.pop();
            if (!node || typeof node !== "object" || seen.has(node)) continue;
            seen.add(node);
            if (node.type === "var" && node.name === "_") return true;
            for (const child of node.nodes ?? []) stack.push(child);
        }
        return false;
    };

    for (const [head, rules] of Object.entries(rulesByHead)) {
        if (!allowedHeads.has(head)) {
            throw new Error(`归纳计算规则头只能属于本 bundle 的消去器或递归器：${head || "<空>"}`);
        }
        const arities = new Set<number>();
        aritiesByHead.set(head, arities);
        for (const rule of rules) {
            const first = rule.pattern[0];
            if (first?.type !== "var" || first.bondVarId || first.name !== head) {
                throw new Error(`归纳计算规则 ${head} 的 pattern[0] 必须等于规则头`);
            }
            const dataPattern = rule.pattern[rule.pattern.length - 1];
            const constructorName = dataPattern
                ? generatedFreeConstantName(dataPattern)
                : undefined;
            if (!constructorName || !constructorNames.has(constructorName)) {
                throw new Error(`归纳计算规则 ${head} 的最后数据模式必须由当前点构造子形成`);
            }
            const dataArguments = generatedApplicationParts(dataPattern).arguments;
            if (strictSchema) {
                const profile = strictHeadProfiles.get(head);
                const constructor = strictConstructors.get(constructorName);
                const constructorIndex = bundle.metadata!.constructors
                    .findIndex(candidate => candidate.name === constructorName);
                if (!profile || !constructor || constructorIndex < 0) {
                    throw new Error(`归纳计算规则 ${head} 缺少 canonical schema`);
                }
                const patternArguments = rule.pattern.slice(1);
                if (patternArguments.length !== profile.totalArity) {
                    throw new Error(`归纳计算规则 ${head} 参数数量与消去器类型不一致`);
                }
                if (dataArguments.length !== parameterCount + constructor.argumentNames.length) {
                    throw new Error(`归纳计算规则 ${head} 的点构造子参数数量不一致`);
                }
                const simpleCaptures = [
                    ...patternArguments.slice(0, profile.staticCount),
                    ...dataArguments.slice(parameterCount)
                ];
                if (simpleCaptures.some(capture => capture.type !== "var"
                    || capture.bondVarId || !capture.name?.startsWith("?"))) {
                    throw new Error(`归纳计算规则 ${head} 的静态参数和构造子参数必须是刚性捕获变量`);
                }
                if (new Set(simpleCaptures.map(capture => capture.name)).size !== simpleCaptures.length) {
                    throw new Error(`归纳计算规则 ${head} 的刚性捕获变量不能重复`);
                }

                const parameterStart = profile.full ? 1 : 0;
                for (let parameterIndex = 0; parameterIndex < parameterCount; parameterIndex++) {
                    if (!sameGeneratedAstAlpha(
                        dataArguments[parameterIndex],
                        patternArguments[parameterStart + parameterIndex]
                    )) {
                        throw new Error(`归纳计算规则 ${head} 未保持统一参数：${parameters[parameterIndex].name}`);
                    }
                }

                const replacements = new Map<string, AST>();
                for (let parameterIndex = 0; parameterIndex < parameterCount; parameterIndex++) {
                    replacements.set(parameters[parameterIndex].name, dataArguments[parameterIndex]);
                }
                for (let argumentIndex = 0; argumentIndex < constructor.argumentNames.length; argumentIndex++) {
                    replacements.set(
                        constructor.argumentNames[argumentIndex],
                        dataArguments[parameterCount + argumentIndex]
                    );
                }
                const expectedOuterIndices = constructor.resultIndices.map(index =>
                    substituteGeneratedFreeNames(index, replacements));
                const outerIndices = patternArguments.slice(
                    profile.staticCount,
                    profile.staticCount + indexCount
                );
                if (outerIndices.length !== expectedOuterIndices.length
                    || outerIndices.some((value, index) =>
                        !sameGeneratedAstAlpha(value, expectedOuterIndices[index]))) {
                    throw new Error(`归纳计算规则 ${head} 的外层索引与点构造子结论不一致`);
                }

                const recursiveByIndex = new Map(
                    constructor.recursiveArguments.map(recursive => [recursive.index, recursive] as const)
                );
                const methodArguments: AST[] = [];
                for (let argumentIndex = 0; argumentIndex < constructor.argumentNames.length; argumentIndex++) {
                    const argument = dataArguments[parameterCount + argumentIndex];
                    methodArguments.push(Core.clone(argument));
                    const recursive = recursiveByIndex.get(argumentIndex);
                    if (!recursive) continue;

                    const boundTelescopeNames = new Set<string>();
                    const telescope = recursive.telescope.map(binder => {
                        const type = substituteGeneratedFreeNames(
                            binder.type,
                            replacements,
                            boundTelescopeNames
                        );
                        boundTelescopeNames.add(binder.name);
                        return { name: binder.name, type };
                    });
                    const childIndices = recursive.resultIndices.map(index =>
                        substituteGeneratedFreeNames(index, replacements, boundTelescopeNames));
                    const recursiveData = wrapApply(
                        Core.clone(argument),
                        ...telescope.map(binder => wrapVar(binder.name))
                    );
                    let recursiveCall = wrapApply(
                        wrapVar(head),
                        ...patternArguments.slice(0, profile.staticCount).map(value => Core.clone(value)),
                        ...childIndices,
                        recursiveData
                    );
                    for (let telescopeIndex = telescope.length - 1; telescopeIndex >= 0; telescopeIndex--) {
                        const binder = telescope[telescopeIndex];
                        recursiveCall = {
                            type: "L",
                            name: binder.name,
                            nodes: [Core.clone(binder.type), recursiveCall]
                        };
                    }
                    methodArguments.push(recursiveCall);
                }
                const branch = patternArguments[profile.constructorBranchOffset + constructorIndex];
                const expectedResult = wrapApply(Core.clone(branch), ...methodArguments);
                if (!sameGeneratedAstAlpha(rule.result, expectedResult)) {
                    throw new Error(`归纳计算规则 ${head} 的右侧不符合构造子 ${constructorName} 的 canonical 分支`);
                }
            }
            const recursiveIndexes = recursiveArgumentIndexes.get(constructorName) ?? new Set<number>();
            const recursiveDataRoots = new Set(
                dataArguments.slice(parameterCount)
                    .filter((argument, index) => recursiveIndexes.has(index)
                        && argument.type === "var" && argument.name?.startsWith("?"))
                    .map(argument => argument.name)
            );
            const ownerKey = `${head}\u0000${constructorName}`;
            if (constructorRuleOwners.has(ownerKey)) {
                throw new Error(`归纳计算规则 ${head} 在构造子 ${constructorName} 上重叠`);
            }
            constructorRuleOwners.add(ownerKey);
            arities.add(rule.pattern.length - 1);

            const boundMetas = new Set<string>();
            for (const pattern of rule.pattern) collectInferenceMetaNames(pattern, boundMetas);
            const unboundMetas = [...collectInferenceMetaNames(rule.result)]
                .filter(name => !boundMetas.has(name));
            if (unboundMetas.length) {
                throw new Error(
                    `归纳计算规则 ${head} 的右侧引用了左侧未绑定的元变量：${unboundMetas.join("、")}`
                );
            }
            if (containsAnonymousHole(rule.result)) {
                throw new Error(`归纳计算规则 ${head} 的右侧不能包含未绑定占位符 _`);
            }
            rulePolicies.push({ head, rule, recursiveDataRoots });
        }
    }

    if (strictSchema) {
        for (const head of strictHeadProfiles.keys()) {
            const rules = rulesByHead[head];
            if (!rules || rules.length !== strictConstructors.size) {
                throw new Error(`归纳计算规则 ${head} 未完整覆盖全部点构造子`);
            }
            for (const constructorName of strictConstructors.keys()) {
                if (!constructorRuleOwners.has(`${head}\u0000${constructorName}`)) {
                    throw new Error(`归纳计算规则 ${head} 缺少点构造子 ${constructorName}`);
                }
            }
        }
    }

    for (const [head, arities] of aritiesByHead) {
        if (arities.size > 1) {
            throw new Error(`归纳计算规则 ${head} 的 pattern 参数数量不一致`);
        }
    }

    const recursiveHeads = new Set(aritiesByHead.keys());
    const rejectNonDecreasingCall = (
        ownerHead: string,
        recursiveDataRoots: ReadonlySet<string>,
        result: AST
    ) => {
        const seen = new WeakSet<object>();
        const visit = (node: AST | undefined) => {
            if (!node || typeof node !== "object" || seen.has(node)) return;
            seen.add(node);
            if (node.type === "apply") {
                const application = generatedApplicationParts(node);
                const calledHead = generatedFreeConstantName(application.head);
                const arities = calledHead && recursiveHeads.has(calledHead)
                    ? aritiesByHead.get(calledHead)
                    : undefined;
                if (calledHead && arities) {
                    if (calledHead !== ownerHead) {
                        throw new Error(`归纳计算规则 ${ownerHead} 不能递归调用其他消去器：${calledHead}`);
                    }
                    const [arity] = arities;
                    if (arity <= 0 || application.arguments.length < arity) {
                        throw new Error(`归纳计算规则 ${ownerHead} 包含部分应用的递归调用`);
                    }
                    const recursiveData = application.arguments[arity - 1];
                    const recursiveRoot = generatedFreeConstantName(recursiveData);
                    if (recursiveRoot && constructorNames.has(recursiveRoot)) {
                        throw new Error(
                            `归纳计算规则 ${ownerHead} 包含对构造项 ${recursiveRoot} 的明显非递减递归调用`
                        );
                    }
                    if (!recursiveRoot?.startsWith("?") || !recursiveDataRoots.has(recursiveRoot)) {
                        throw new Error(
                            `归纳计算规则 ${ownerHead} 的递归数据不是当前构造项的直接子项`
                        );
                    }
                    for (const argument of application.arguments) visit(argument);
                    return;
                }
                visit(application.head);
                for (const argument of application.arguments) visit(argument);
                return;
            }
            if (node.type === "var" && recursiveHeads.has(node.name)) {
                throw new Error(`归纳计算规则 ${ownerHead} 包含部分应用的递归调用`);
            }
            for (const child of node.nodes ?? []) visit(child);
        };
        visit(result);
    };
    for (const { head, rule, recursiveDataRoots } of rulePolicies) {
        rejectNonDecreasingCall(head, recursiveDataRoots, rule.result);
    }
}

function generatedEqualityEndpoints(ast: AST): readonly [AST, AST] | undefined {
    if (ast.type === "=" && ast.nodes?.[0] && ast.nodes?.[1]) {
        return [ast.nodes[0], ast.nodes[1]];
    }
    const { head, arguments: arguments_ } = generatedApplicationParts(ast);
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
    /** Large system types admitted only after Core reconstructs their canonical schema. */
    private certifiedLargeSystemTypes = new Set<string>();
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
            ast.nbeGeneratedMeta = value.nbeGeneratedMeta;
            return;
        }
        const v = moveSemantic ? value : this.clone(value);
        ast.type = v.type;
        ast.name = v.name;
        ast.nodes = v.nodes;
        ast.checked = v.checked;
        ast.bondVarId = v.bondVarId;
        ast.displayExplicitAt = v.displayExplicitAt;
        ast.nbeGeneratedMeta = v.nbeGeneratedMeta;
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
            displayExplicitAt: ast.displayExplicitAt,
            nbeGeneratedMeta: ast.nbeGeneratedMeta
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
    private validateCanonicalInductiveRuleTypes(
        bundle: CoreSystemInductiveBundle,
        normalizedEntries: readonly (readonly [string, AST])[],
        normalizedRules: Readonly<Record<string, readonly { pattern: AST[]; result: AST }[]>>,
        parameters: readonly { name: string; type: AST }[],
        indexCount: number
    ) {
        if (bundle.metadata?.ruleSchemaVersion !== 1) return;
        const metadata = bundle.metadata;
        const types = new Map(normalizedEntries);
        const constructorIndex = new Map(
            metadata.constructors.map((constructor, index) => [constructor.name, index] as const)
        );
        const constructorSchemas = new Map(
            metadata.constructors.map(constructor => [constructor.name, constructor] as const)
        );
        const coherenceCount = hitPathConstructorCount(
            hitPathLevelsFromCanonicalOrLegacy(metadata)
        );
        let captureSequence = 0;

        const instantiateBinder = (cursor: AST, argument: AST) => {
            if ((cursor.type !== "P" && cursor.type !== "->")
                || !cursor.nodes?.[0] || !cursor.nodes?.[1]) {
                throw new Error("消去器 telescope 提前结束");
            }
            return cursor.type === "P" && cursor.name
                ? substituteGeneratedFreeNames(
                    cursor.nodes[1],
                    new Map([[cursor.name, argument]])
                )
                : Core.clone(cursor.nodes[1]);
        };
        const checkAgainst = (term: AST, expected: AST, context: Context, label: string) => {
            try {
                this.withSilentErrors(() => this.checkType({
                    type: ":",
                    name: "",
                    nodes: [Core.clone(term), Core.clone(expected)]
                }, Core.cloneContext(context), false, undefined, false, true, false));
            } catch {
                throw new Error(`${label} 未通过 subject-reduction 类型检查`);
            }
        };

        for (const [head, rules] of Object.entries(normalizedRules)) {
            const headType = types.get(head);
            if (!headType) throw new Error(`计算规则 schema 缺少消去器类型：${head}`);
            const full = head.startsWith("@");
            const staticCount = (full ? 1 : 0)
                + parameters.length + 1 + metadata.constructors.length + coherenceCount;
            const totalArity = staticCount + indexCount + 1;
            const branchOffset = (full ? 1 : 0) + parameters.length + 1;

            for (const rule of rules) {
                const patternArguments = rule.pattern.slice(1);
                if (patternArguments.length !== totalArity) {
                    throw new Error(`归纳计算规则 ${head} 参数数量与消去器类型不一致`);
                }
                const dataApplication = generatedApplicationParts(patternArguments.at(-1)!);
                const dataHead = generatedFreeConstantName(dataApplication.head);
                const schema = dataHead ? constructorSchemas.get(dataHead) : undefined;
                const branchIndex = dataHead ? constructorIndex.get(dataHead) : undefined;
                if (!schema || branchIndex === undefined
                    || !schema.argumentNames || !schema.recursiveArguments) {
                    throw new Error(`归纳计算规则 ${head} 缺少构造子类型 schema`);
                }

                const context: Context = [];
                const captureReplacements = new Map<string, AST>();
                const schemaReplacements = new Map<string, AST>();
                let cursor = Core.clone(headType);
                const bindCapture = (capture: AST, type: AST) => {
                    if (capture.type !== "var" || !capture.name?.startsWith("?")) {
                        throw new Error(`归纳计算规则 ${head} 包含非变量捕获参数`);
                    }
                    let name = `_ruleCapture${captureSequence++}`;
                    while (context.some(([candidate]) => candidate === name)) name += "_";
                    // Let checkType assign ids after it has reserved binders in
                    // every context type.  Preallocating ids here can collide
                    // with dependent Pi binders while the context is marked.
                    const variable: AST = { type: "var", name, nodes: [] };
                    captureReplacements.set(capture.name, variable);
                    context.unshift([name, Core.clone(type), 0]);
                    return variable;
                };

                for (let index = 0; index < staticCount; index++) {
                    if ((cursor.type !== "P" && cursor.type !== "->")
                        || !cursor.nodes?.[0] || !cursor.nodes?.[1]) {
                        throw new Error(`归纳计算规则 ${head} 的消去器 telescope 提前结束`);
                    }
                    const variable = bindCapture(patternArguments[index], cursor.nodes[0]);
                    cursor = instantiateBinder(cursor, variable);
                }

                const parameterStart = full ? 1 : 0;
                for (let index = 0; index < parameters.length; index++) {
                    const capture = patternArguments[parameterStart + index];
                    const replacement = captureReplacements.get(capture.name);
                    if (!replacement) throw new Error(`归纳计算规则 ${head} 缺少统一参数捕获`);
                    schemaReplacements.set(parameters[index].name, replacement);
                }
                for (let index = 0; index < schema.argumentNames.length; index++) {
                    const capture = dataApplication.arguments[parameters.length + index];
                    const argumentType = substituteGeneratedFreeNames(
                        schema.argumentTypes[index],
                        schemaReplacements
                    );
                    const variable = bindCapture(capture, argumentType);
                    schemaReplacements.set(schema.argumentNames[index], variable);
                }

                for (let index = staticCount; index < totalArity; index++) {
                    if ((cursor.type !== "P" && cursor.type !== "->")
                        || !cursor.nodes?.[0] || !cursor.nodes?.[1]) {
                        throw new Error(`归纳计算规则 ${head} 的消去器 telescope 提前结束`);
                    }
                    const argument = substituteGeneratedFreeNames(
                        patternArguments[index],
                        captureReplacements
                    );
                    if (collectInferenceMetaNames(argument).size) {
                        throw new Error(`归纳计算规则 ${head} 存在未绑定的 pattern 元变量`);
                    }
                    checkAgainst(
                        argument,
                        cursor.nodes[0],
                        context,
                        `归纳计算规则 ${head} 第 ${index + 1} 个参数`
                    );
                    cursor = instantiateBinder(cursor, argument);
                }

                const rhs = substituteGeneratedFreeNames(rule.result, captureReplacements);
                if (collectInferenceMetaNames(rhs).size) {
                    throw new Error(`归纳计算规则 ${head} 右侧存在未绑定元变量`);
                }
                const expectedBranch = patternArguments[branchOffset + branchIndex];
                if (!captureReplacements.has(expectedBranch.name)) {
                    throw new Error(`归纳计算规则 ${head} 缺少对应点分支捕获`);
                }
                checkAgainst(
                    rhs,
                    cursor,
                    context,
                    `归纳计算规则 ${head} 在构造子 ${schema.name} 上的右侧`
                );
            }
        }
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
        const runtimeMetadataKind = bundle.metadata?.kind as string | undefined;
        const runtimeMetadataDimension = Number(bundle.metadata?.dimension ?? 0);
        if (runtimeMetadataDimension > 3 || runtimeMetadataKind === "hit4") {
            throw new Error(
                `Core 最高只支持三维 HIT：${runtimeMetadataKind ?? "HIT"}`
                + `${runtimeMetadataDimension ? `/${runtimeMetadataDimension}` : ""}`
            );
        }
        if (runtimeMetadataKind !== undefined
            && !["inductive", "hit1", "hit2", "hit3"].includes(runtimeMetadataKind)) {
            throw new Error(`不支持的归纳类型 metadata kind：${runtimeMetadataKind}`);
        }
        if (bundle.metadata) {
            bundle = {
                ...bundle,
                metadata: normalizeCoreSystemInductiveMetadata(bundle.metadata)
            };
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
        const metadataVersion = Number(bundle.metadata?.version);
        if (Number.isFinite(metadataVersion) && metadataVersion > 0
            && ![1, 2, 3, 4, 5, 6, 7, 8].includes(metadataVersion)) {
            throw new Error(`不支持的归纳 metadata 版本：${metadataVersion}`);
        }
        const metadataPathLevels: CoreHitPathLevels = bundle.metadata
            ? hitPathLevelsFromCanonicalOrLegacy(bundle.metadata)
            : createHitPathLevels([], [], []);
        const metadataPathEntries = hitPathConstructorsAt(metadataPathLevels, 1);
        const metadataTwoPathEntries = hitPathConstructorsAt(metadataPathLevels, 2);
        const metadataThreePathEntries = hitPathConstructorsAt(metadataPathLevels, 3);
        if ([2, 3, 4, 5, 6, 7, 8].includes(metadataVersion)
            && bundle.metadata?.ruleSchemaVersion !== 1) {
            throw new Error(`沙盒归纳 metadata v${metadataVersion} 必须使用计算规则 schema v1`);
        }
        if (bundle.metadata?.ruleSchemaVersion !== undefined
            && bundle.metadata.ruleSchemaVersion !== 1) {
            throw new Error(`不支持的归纳计算规则 schema：${bundle.metadata.ruleSchemaVersion}`);
        }
        if (bundle.metadata?.ruleSchemaVersion === 1) {
            const metadata = bundle.metadata;
            const actualConstructorNames = bundle.constructors.map(([name]) => name);
            const expectedConstructorNames = metadata.constructors.map(constructor => constructor.name);
            if (actualConstructorNames.length !== expectedConstructorNames.length
                || actualConstructorNames.some((name, index) => expectedConstructorNames[index] !== name)) {
                throw new Error("计算规则 schema 的点构造子列表与 bundle 不一致");
            }
            if (definitions.length) {
                throw new Error("计算规则 schema v1 不允许附加未声明的系统定义");
            }
            if (bundle.eliminator?.[0] !== metadata.eliminatorName
                || bundle.recursor?.[0] !== metadata.recursorName) {
                throw new Error("计算规则 schema 的消去器槽位与 bundle 不一致");
            }
            const expectedAuxiliaryNames = [
                ...metadataPathEntries.map(path => path.name),
                ...metadataTwoPathEntries.map(path => path.name),
                ...metadataThreePathEntries.map(path => path.name),
                metadata.fullEliminatorName,
                metadata.fullRecursorName,
                ...metadataPathEntries.flatMap(path => [
                    `apd_${path.name}`,
                    `@apd_${path.name}`,
                    `ap_${path.name}`,
                    `@ap_${path.name}`
                ]),
                ...metadataTwoPathEntries.flatMap(path => [
                    `apd_${path.name}`,
                    `@apd_${path.name}`,
                    `ap_${path.name}`,
                    `@ap_${path.name}`,
                    `ap2_${path.name}`,
                    `@ap2_${path.name}`
                ]),
                ...metadataThreePathEntries.flatMap(path => [
                    `apd3_${path.name}`,
                    `@apd3_${path.name}`,
                    `ap3_${path.name}`,
                    `@ap3_${path.name}`
                ])
            ];
            if (expectedAuxiliaryNames.some(name => !name)
                || new Set(expectedAuxiliaryNames).size !== expectedAuxiliaryNames.length) {
                throw new Error("计算规则 schema 的辅助常量名称无效或重复");
            }
            const actualAuxiliaryNames = (bundle.auxiliaryTypes ?? []).map(([name]) => name);
            if (actualAuxiliaryNames.length !== expectedAuxiliaryNames.length
                || actualAuxiliaryNames.some((name, index) => expectedAuxiliaryNames[index] !== name)) {
                throw new Error("计算规则 schema 的辅助常量列表与 bundle 不一致");
            }
        }
        const bundlePointConstructorNames = bundle.constructors.map(([name]) => name);
        const metadataPointConstructorNames = (bundle.metadata?.constructors ?? [])
            .map(ctor => ctor.name);
        const pointConstructorNames = new Set([
            ...bundlePointConstructorNames,
            ...metadataPointConstructorNames
        ]);
        const pathConstructorNames = new Set<string>();
        for (const path of metadataPathEntries) {
            if (!path.name || pathConstructorNames.has(path.name)) {
                throw new Error(`路径构造子 metadata 名称冲突：${path.name || ""}`);
            }
            if (pointConstructorNames.has(path.name)) {
                throw new Error(`路径构造子不能作为点构造子注册：${path.name}`);
            }
            pathConstructorNames.add(path.name);
        }
        const twoPathConstructorNames = new Set<string>();
        for (const path of metadataTwoPathEntries) {
            if (!path.name || twoPathConstructorNames.has(path.name)) {
                throw new Error(`二阶路径构造子 metadata 名称冲突：${path.name || ""}`);
            }
            if (pointConstructorNames.has(path.name) || pathConstructorNames.has(path.name)) {
                throw new Error(`二阶路径构造子不能与一阶构造子同名：${path.name}`);
            }
            twoPathConstructorNames.add(path.name);
        }
        const threePathConstructorNames = new Set<string>();
        for (const path of metadataThreePathEntries) {
            if (!path.name || threePathConstructorNames.has(path.name)) {
                throw new Error(`三阶路径构造子 metadata 名称冲突：${path.name || ""}`);
            }
            if (pointConstructorNames.has(path.name)
                || pathConstructorNames.has(path.name)
                || twoPathConstructorNames.has(path.name)) {
                throw new Error(`三阶路径构造子不能与低维构造子同名：${path.name}`);
            }
            threePathConstructorNames.add(path.name);
        }
        if (bundle.metadata?.kind === "hit1"
            || bundle.metadata?.kind === "hit2"
            || bundle.metadata?.kind === "hit3") {
            const hitDimension = bundle.metadata.kind === "hit3"
                ? 3
                : bundle.metadata.kind === "hit2" ? 2 : 1;
            if (bundle.metadata.dimension !== hitDimension) {
                throw new Error(`HIT metadata 维度必须为 ${hitDimension}：${bundle.metadata.dimension ?? ""}`);
            }
            const pathLevelDimension = highestHitPathLevel(metadataPathLevels);
            if (pathLevelDimension !== hitDimension) {
                throw new Error(
                    `HIT pathLevels 最高维度必须为 ${hitDimension}：${pathLevelDimension}`
                );
            }
            if (!metadataPathEntries.length) {
                throw new Error("HIT metadata 至少需要一个一阶路径构造子");
            }
            if (bundle.metadata.kind === "hit2" && !metadataTwoPathEntries.length) {
                throw new Error("二维 HIT metadata 至少需要一个二阶路径构造子");
            }
            if (bundle.metadata.kind === "hit3"
                && (!metadataTwoPathEntries.length || !metadataThreePathEntries.length)) {
                throw new Error("三维 HIT metadata 至少需要二阶和三阶路径构造子");
            }
            if (bundle.metadata.kind === "hit1"
                && (metadataTwoPathEntries.length || metadataThreePathEntries.length)) {
                throw new Error("一阶 HIT metadata 不能包含高阶路径构造子");
            }
            if (bundle.metadata.kind === "hit2" && metadataThreePathEntries.length) {
                throw new Error("二维 HIT metadata 不能包含三阶路径构造子");
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
            if (!head || !Array.isArray(rules)) {
                throw new Error(`归纳计算规则集合无效：${head || "<空>"}`);
            }
            normalizedRules[head] = rules.map(rule => {
                if (!rule?.pattern?.length || !rule.result
                    || rule.pattern.some(pattern => !pattern)) {
                    throw new Error(`归纳计算规则 ${head} 缺少 pattern 或 result`);
                }
                return {
                    pattern: rule.pattern.map(pattern => this.desugar(Core.clone(pattern), true)),
                    result: this.desugar(Core.clone(rule.result), true)
                };
            });
        }
        for (const path of flattenHitPathLevels(
            hitPathLevelsFromCanonicalOrLegacy(bundle.metadata ?? {})
        )) {
            for (const head of new Set([
                path.name,
                path.computationName,
                `apd_${path.name}`,
                `@apd_${path.name}`,
                `ap_${path.name}`,
                `@ap_${path.name}`,
                `ap2_${path.name}`,
                `@ap2_${path.name}`,
                `apd3_${path.name}`,
                `@apd3_${path.name}`,
                `ap3_${path.name}`,
                `@ap3_${path.name}`
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
        if (indexCount > 0 && (bundle.metadata?.kind === "hit2"
            || bundle.metadata?.kind === "hit3")) {
            throw new Error("二维和三维 HIT metadata 暂不支持索引");
        }
        const parameters = familyBinders.slice(0, parameterCount);
        const indices = familyBinders.slice(parameterCount);
        if (bundle.metadata?.ruleSchemaVersion === 1) {
            const metadataIndices = bundle.metadata.indices;
            if (!Array.isArray(metadataIndices) || metadataIndices.length !== indexCount) {
                throw new Error("归纳类型 metadata 索引 telescope 不完整");
            }
            for (let index = 0; index < indices.length; index++) {
                const actual = indices[index];
                const expected = metadataIndices[index];
                if (actual.name !== expected.name
                    || !sameGeneratedAstAlpha(
                        actual.type,
                        this.desugar(Core.clone(expected.type), true)
                    )) {
                    throw new Error(`归纳类型 metadata 第 ${index + 1} 个索引与 family telescope 不一致`);
                }
            }
        }
        const constructorTypes = new Map(
            normalizedEntries
                .filter(([name]) => bundlePointConstructorNames.includes(name))
        );
        validateSystemInductiveComputeRules(
            bundle,
            normalizedRules,
            parameters,
            indexCount,
            constructorTypes,
            ast => this.desugar(Core.clone(ast), true)
        );
        const canonicallyCertifiedTypeFormations = new Set<string>();

        if (bundle.metadata?.kind === "hit1"
            || bundle.metadata?.kind === "hit2"
            || bundle.metadata?.kind === "hit3") {
            const metadata = bundle.metadata;

            const auxiliaryTypes = new Map<string, AST>();
            for (const [name, type] of bundle.auxiliaryTypes ?? []) {
                auxiliaryTypes.set(name, this.desugar(Core.clone(type), true));
            }
            const pointTypes = new Map<string, AST>();
            for (const [name, type] of bundle.constructors) {
                pointTypes.set(name, this.desugar(Core.clone(type), true));
            }
            const normalizedMetadataAst = (ast: AST) => this.desugar(Core.clone(ast), true);
            const requireHitIndexEquality = (
                left: AST,
                right: AST,
                context: Context,
                label: string
            ) => {
                const result = this.semanticKernel.tryEqualResult(
                    left,
                    right,
                    context,
                    {
                        maxSteps: Core.semanticTypeAssertionMaxSteps,
                        deadline: Date.now() + Core.timeout
                    }
                );
                if (result === "equal") return;
                if (result === "budget-exhausted") {
                    throw new Error(`${label} 的定义相等检查资源耗尽`);
                }
                if (result === "unsupported") {
                    throw new Error(`${label} 的定义相等检查暂不支持该表达式`);
                }
                throw new Error(`${label} 不在同一索引纤维`);
            };
            const hitPointResultIndices = (point: AST, label: string) => {
                const application = generatedApplicationParts(point);
                const headName = generatedFreeConstantName(application.head) ?? "";
                const constructor = metadata.constructors.find(entry => entry.name === headName);
                if (!constructor) {
                    throw new Error(`${label} 引用了未知点端点：${headName || "<非常量>"}`);
                }
                const argumentNames = constructor.argumentNames ?? [];
                if (metadata.ruleSchemaVersion === 1
                    && (argumentNames.length !== constructor.argumentTypes.length
                        || new Set(argumentNames).size !== argumentNames.length)) {
                    throw new Error(`${label} 点端点 ${headName} argumentNames 与 telescope 不一致`);
                }
                if (application.arguments.length !== parameters.length + argumentNames.length) {
                    throw new Error(`${label} 点端点 ${headName} 参数数量与 metadata 不一致`);
                }
                const replacements = new Map<string, AST>();
                parameters.forEach((parameter, index) => {
                    const argument = application.arguments[index];
                    if (!sameGeneratedAstAlpha(argument, wrapVar(parameter.name))) {
                        throw new Error(`${label} 点端点 ${headName} 未保持统一参数 ${parameter.name}`);
                    }
                    replacements.set(parameter.name, argument);
                });
                argumentNames.forEach((name, index) => {
                    replacements.set(name, application.arguments[parameters.length + index]);
                });
                const resultIndices = constructor.resultIndices ?? [];
                if (resultIndices.length !== indexCount) {
                    throw new Error(`${label} 点端点 ${headName} 返回索引 metadata 不完整`);
                }
                return resultIndices.map(index => normalizedMetadataAst(
                    substituteGeneratedFreeNames(index, replacements)
                ));
            };
            const hitBranchValue = (
                point: AST,
                branchNames: readonly string[],
                label: string,
                state = { nodes: 0 },
                depth = 0
            ): AST => {
                if (depth > 128) throw new Error(`${label} 点构造表达式嵌套过深`);
                if (++state.nodes > 4_096) throw new Error(`${label} 点构造表达式节点过多`);
                const application = generatedApplicationParts(point);
                const headName = generatedFreeConstantName(application.head) ?? "";
                const constructorIndex = metadata.constructors
                    .findIndex(entry => entry.name === headName);
                if (constructorIndex < 0) {
                    throw new Error(`${label} 引用了未知点端点：${headName || "<非常量>"}`);
                }
                const constructor = metadata.constructors[constructorIndex];
                if (application.arguments.length !== parameters.length + constructor.argumentTypes.length) {
                    throw new Error(`${label} 点端点 ${headName} 参数数量与 metadata 不一致`);
                }
                for (let index = 0; index < parameters.length; index++) {
                    if (!sameGeneratedAst(application.arguments[index], wrapVar(parameters[index].name))) {
                        throw new Error(`${label} 点端点 ${headName} 未保持统一参数 ${parameters[index].name}`);
                    }
                }
                const arguments_ = application.arguments
                    .slice(parameters.length)
                    .map(argument => Core.clone(argument));
                const methodArguments: AST[] = [];
                for (let index = 0; index < arguments_.length; index++) {
                    methodArguments.push(Core.clone(arguments_[index]));
                    const recursive = constructor.recursiveArguments
                        ?.find(argument => argument.index === index);
                    if (!recursive) continue;
                    if (recursive.telescope.length) {
                        throw new Error(
                            `${label} 暂不支持函数型递归点参数：${headName}.${constructor.argumentNames?.[index] ?? index}`
                        );
                    }
                    methodArguments.push(hitBranchValue(
                        arguments_[index],
                        branchNames,
                        label,
                        state,
                        depth + 1
                    ));
                }
                return wrapApply(
                    wrapVar(branchNames[constructorIndex]),
                    ...methodArguments
                );
            };
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

            for (const path of metadataPathEntries) {
                if (metadata.ruleSchemaVersion === 1
                    && (!Array.isArray(path.argumentNames)
                        || path.argumentNames.length !== path.argumentTypes.length
                        || new Set(path.argumentNames).size !== path.argumentNames.length)) {
                    throw new Error(`一阶 HIT 路径构造子 ${path.name} argumentNames 与 telescope 不一致`);
                }
                const pathResultIndices = path.resultIndices ?? [];
                if (pathResultIndices.length !== indexCount) {
                    throw new Error(`一阶 HIT 路径构造子 ${path.name} resultIndices 与索引数量不一致`);
                }
                const normalizedLeft = normalizedMetadataAst(path.left);
                const normalizedRight = normalizedMetadataAst(path.right);
                const pathIndexContext: Context = [];
                let nextPathContextId = 1;
                for (const parameter of parameters) {
                    pathIndexContext.unshift([
                        parameter.name,
                        Core.clone(parameter.type),
                        nextPathContextId++
                    ]);
                }
                const pathArgumentNames = path.argumentNames ?? [];
                for (let index = 0; index < pathArgumentNames.length; index++) {
                    pathIndexContext.unshift([
                        pathArgumentNames[index],
                        normalizedMetadataAst(path.argumentTypes[index]),
                        nextPathContextId++
                    ]);
                }
                const leftResultIndices = hitPointResultIndices(
                    normalizedLeft, `一阶 HIT 路径构造子 ${path.name} 左端点`
                );
                const rightResultIndices = hitPointResultIndices(
                    normalizedRight, `一阶 HIT 路径构造子 ${path.name} 右端点`
                );
                const normalizedResultIndices = pathResultIndices.map(normalizedMetadataAst);
                for (let index = 0; index < leftResultIndices.length; index++) {
                    requireHitIndexEquality(
                        leftResultIndices[index],
                        rightResultIndices[index],
                        pathIndexContext,
                        `一阶 HIT 路径构造子 ${path.name} 第 ${index + 1} 个端点索引`
                    );
                    requireHitIndexEquality(
                        leftResultIndices[index],
                        normalizedResultIndices[index],
                        pathIndexContext,
                        `一阶 HIT 路径构造子 ${path.name} 第 ${index + 1} 个 metadata 索引`
                    );
                }
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
                    || !sameGeneratedAst(endpoints[0], normalizedLeft)
                    || !sameGeneratedAst(endpoints[1], normalizedRight)) {
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

            if (metadata.kind === "hit1" && metadata.ruleSchemaVersion === 1) {
                type HitTelescopeBinder = { kind: "P" | "->"; name: string; type: AST };
                const readHitTelescope = (source: AST, label: string) => {
                    const binders: HitTelescopeBinder[] = [];
                    let cursor = source;
                    while ((cursor.type === "P" || cursor.type === "->")
                        && cursor.nodes?.[0] && cursor.nodes?.[1]) {
                        binders.push({
                            kind: cursor.type,
                            name: cursor.type === "P" ? cursor.name : "",
                            type: Core.clone(cursor.nodes[0])
                        });
                        cursor = cursor.nodes[1];
                    }
                    if (!binders.length) throw new Error(`${label} telescope 不完整`);
                    return { binders, body: cursor };
                };
                const wrapHitTelescope = (
                    binders: readonly HitTelescopeBinder[],
                    body: AST
                ) => {
                    let result = body;
                    for (let index = binders.length - 1; index >= 0; index--) {
                        const binder = binders[index];
                        result = {
                            type: binder.kind,
                            name: binder.name,
                            nodes: [Core.clone(binder.type), result]
                        };
                    }
                    return result;
                };
                const hitEquality = (left: AST, right: AST): AST => ({
                    type: "=",
                    name: "",
                    nodes: [left, right]
                });
                const hitFiberMotive = (
                    motiveName: string,
                    resultIndices: readonly AST[]
                ) => {
                    if (!resultIndices.length) return wrapVar(motiveName);
                    const occupied = new Set([
                        metadata.typeName,
                        motiveName,
                        ...parameters.map(parameter => parameter.name)
                    ]);
                    const stack = [...resultIndices];
                    const seen = new WeakSet<object>();
                    while (stack.length) {
                        const node = stack.pop();
                        if (!node || typeof node !== "object" || seen.has(node)) continue;
                        seen.add(node);
                        if (node.name) occupied.add(node.name);
                        for (const child of node.nodes ?? []) stack.push(child);
                    }
                    let valueName = "fiberValue";
                    while (occupied.has(valueName)) valueName += "_";
                    const value = wrapVar(valueName);
                    return {
                        type: "L",
                        name: valueName,
                        nodes: [
                            wrapApply(
                                wrapVar(metadata.typeName),
                                ...parameters.map(parameter => wrapVar(parameter.name)),
                                ...resultIndices.map(normalizedMetadataAst)
                            ),
                            wrapApply(
                                wrapVar(motiveName),
                                ...resultIndices.map(normalizedMetadataAst),
                                value
                            )
                        ]
                    } as AST;
                };
                const staticCount = (full: boolean) => (full ? 1 : 0)
                    + parameters.length + 1 + metadata.constructors.length
                    + metadataPathEntries.length;
                const pathMethodOffset = (full: boolean) => (full ? 1 : 0)
                    + parameters.length + 1 + metadata.constructors.length;

                const validateHit1EliminationTelescope = (
                    source: AST,
                    full: boolean,
                    dependent: boolean,
                    label: string
                ) => {
                    const { binders } = readHitTelescope(source, label);
                    const expectedCount = staticCount(full) + indexCount + 1;
                    if (binders.length !== expectedCount) {
                        throw new Error(`${label} telescope 长度与 indexed hit1 metadata 不一致`);
                    }
                    let offset = full ? 1 : 0;
                    for (let index = 0; index < parameters.length; index++) {
                        const binder = binders[offset + index];
                        const parameter = parameters[index];
                        if (binder.kind !== "P" || binder.name !== parameter.name
                            || !sameGeneratedAstAlpha(binder.type, parameter.type)) {
                            throw new Error(`${label} 未保持统一参数 ${parameter.name}`);
                        }
                    }
                    offset += parameters.length;
                    const motiveName = binders[offset++].name;
                    const branchNames = binders
                        .slice(offset, offset + metadata.constructors.length)
                        .map(binder => binder.name);
                    offset += metadata.constructors.length;
                    for (let index = 0; index < metadataPathEntries.length; index++) {
                        const path = metadataPathEntries[index];
                        const argumentNames = path.argumentNames ?? [];
                        const argumentTypes = path.argumentTypes.map(normalizedMetadataAst);
                        const pathArguments = argumentNames.map(wrapVar);
                        const pathTerm = wrapApply(
                            wrapVar(path.name),
                            ...parameters.map(parameter => wrapVar(parameter.name)),
                            ...pathArguments
                        );
                        const leftBranch = hitBranchValue(
                            normalizedMetadataAst(path.left),
                            branchNames,
                            `${label} ${path.name} 左端点`
                        );
                        const rightBranch = hitBranchValue(
                            normalizedMetadataAst(path.right),
                            branchNames,
                            `${label} ${path.name} 右端点`
                        );
                        let expectedBody: AST;
                        if (dependent) {
                            const motiveAtFiber = hitFiberMotive(
                                motiveName,
                                path.resultIndices ?? []
                            );
                            expectedBody = hitEquality(
                                wrapApply(
                                    wrapVar("trans"),
                                    motiveAtFiber,
                                    pathTerm,
                                    leftBranch
                                ),
                                rightBranch
                            );
                        } else {
                            expectedBody = hitEquality(leftBranch, rightBranch);
                        }
                        const pathBinders = argumentNames.map((name, argumentIndex) => ({
                            kind: "P" as const,
                            name,
                            type: argumentTypes[argumentIndex]
                        }));
                        const expected = normalizedMetadataAst(
                            wrapHitTelescope(pathBinders, expectedBody)
                        );
                        const actual = binders[offset + index]?.type;
                        if (!actual || !sameGeneratedAstAlpha(actual, expected)) {
                            throw new Error(`${label} 一阶 coherence ${path.name} 与 metadata 不一致`);
                        }
                    }
                    return binders;
                };

                const validateHit1Computation = (
                    path: CoreHitPathConstructorMetadata,
                    source: AST,
                    head: string,
                    full: boolean,
                    dependent: boolean
                ) => {
                    const label = `${full ? "完整" : "公开"}${dependent ? "消去器" : "递归器"}`;
                    const sourceBinders = validateHit1EliminationTelescope(
                        source, full, dependent, label
                    );
                    const prefix = sourceBinders.slice(0, staticCount(full));
                    if (prefix.some(binder => binder.kind !== "P" || !binder.name)) {
                        throw new Error(`${label} 静态 telescope 必须使用具名 Π binder`);
                    }
                    const argumentNames = path.argumentNames ?? [];
                    const pathBinders: HitTelescopeBinder[] = argumentNames.map((name, index) => ({
                        kind: "P",
                        name,
                        type: normalizedMetadataAst(path.argumentTypes[index])
                    }));
                    const pathArguments = argumentNames.map(wrapVar);
                    const pathTerm = wrapApply(
                        wrapVar(path.name),
                        ...parameters.map(parameter => wrapVar(parameter.name)),
                        ...pathArguments
                    );
                    const eliminationAtFiber = wrapApply(
                        wrapVar(head),
                        ...prefix.map(binder => wrapVar(binder.name)),
                        ...(path.resultIndices ?? []).map(normalizedMetadataAst)
                    );
                    const methodName = prefix[pathMethodOffset(full)
                        + metadataPathEntries.findIndex(candidate => candidate.name === path.name)]?.name;
                    if (!methodName) {
                        throw new Error(`${label} 缺少路径方法 ${path.name}`);
                    }
                    const expected = normalizedMetadataAst(wrapHitTelescope(
                        [...prefix, ...pathBinders],
                        hitEquality(
                            wrapApply(
                                wrapVar(dependent ? "apd" : "ap"),
                                eliminationAtFiber,
                                pathTerm
                            ),
                            wrapApply(wrapVar(methodName), ...pathArguments)
                        )
                    ));
                    const computationName = `${full ? "@" : ""}${dependent ? "apd" : "ap"}_${path.name}`;
                    const actual = auxiliaryTypes.get(computationName);
                    if (!actual || !sameGeneratedAstAlpha(actual, expected)) {
                        throw new Error(`一阶 HIT 路径计算定理 ${computationName} 与 metadata 不一致`);
                    }
                };

                const publicEliminatorType = bundle.eliminator?.[1]
                    ? normalizedMetadataAst(bundle.eliminator[1])
                    : undefined;
                const fullEliminatorType = metadata.fullEliminatorName
                    ? auxiliaryTypes.get(metadata.fullEliminatorName)
                    : undefined;
                const publicRecursorType = bundle.recursor?.[1]
                    ? normalizedMetadataAst(bundle.recursor[1])
                    : undefined;
                const fullRecursorType = metadata.fullRecursorName
                    ? auxiliaryTypes.get(metadata.fullRecursorName)
                    : undefined;
                if (!publicEliminatorType || !fullEliminatorType
                    || !publicRecursorType || !fullRecursorType
                    || !metadata.fullEliminatorName || !metadata.fullRecursorName
                    || !metadata.eliminatorName || !metadata.recursorName) {
                    throw new Error("一阶 HIT 消去器/递归器槽位不完整");
                }
                for (const path of metadataPathEntries) {
                    validateHit1Computation(
                        path, publicEliminatorType, metadata.eliminatorName, false, true
                    );
                    validateHit1Computation(
                        path, fullEliminatorType, metadata.fullEliminatorName, true, true
                    );
                    validateHit1Computation(
                        path, publicRecursorType, metadata.recursorName, false, false
                    );
                    validateHit1Computation(
                        path, fullRecursorType, metadata.fullRecursorName, true, false
                    );
                }
            }

            const pathMetadataByName = new Map(
                metadataPathEntries.map(path => [path.name, path] as const)
            );
            const twoPathMetadataByName = new Map(
                metadataTwoPathEntries.map(path => [path.name, path] as const)
            );
            type EvaluatedOnePathExpression =
                | {
                    kind: "atom";
                    path: CoreHitPathConstructorMetadata;
                    arguments: AST[];
                    term: AST;
                    sourcePoint: AST;
                    targetPoint: AST;
                }
                | {
                    kind: "compose";
                    left: EvaluatedOnePathExpression;
                    right: EvaluatedOnePathExpression;
                    term: AST;
                    sourcePoint: AST;
                    targetPoint: AST;
                }
                | {
                    kind: "inverse";
                    value: EvaluatedOnePathExpression;
                    term: AST;
                    sourcePoint: AST;
                    targetPoint: AST;
                };
            const evaluateOnePathExpression = (
                expression: CoreHitOnePathExpression | undefined,
                owner: string,
                side: string,
                state = { nodes: 0, ancestors: new WeakSet<object>() },
                depth = 0
            ): EvaluatedOnePathExpression => {
                const label = `二维 HIT 二阶路径构造子 ${owner} ${side}端点`;
                if (!expression || typeof expression !== "object") {
                    throw new Error(`${label}缺少一阶路径表达式`);
                }
                if (depth > CORE_HIT_ONE_PATH_EXPRESSION_MAX_DEPTH) {
                    throw new Error(`${label}表达式嵌套过深`);
                }
                if (++state.nodes > CORE_HIT_ONE_PATH_EXPRESSION_MAX_NODES) {
                    throw new Error(`${label}表达式节点过多`);
                }
                if (state.ancestors.has(expression)) {
                    throw new Error(`${label}表达式不能循环引用自身`);
                }
                state.ancestors.add(expression);
                try {
                    if (expression.kind === "atom") {
                        const referencedPath = pathMetadataByName.get(expression.name);
                        if (!referencedPath) {
                            throw new Error(`${label}引用不存在：${expression.name}`);
                        }
                        const argumentNames = referencedPath.argumentNames ?? [];
                        if (argumentNames.length !== referencedPath.argumentTypes.length
                            || new Set(argumentNames).size !== argumentNames.length) {
                            throw new Error(
                                `二维 HIT 一阶路径 ${expression.name} argumentNames 与 telescope 不一致`
                            );
                        }
                        if (expression.arguments.length !== argumentNames.length) {
                            throw new Error(
                                `${label}参数数量与一阶路径 ${expression.name} telescope 不一致：`
                                + `需要 ${argumentNames.length} 个，实际 ${expression.arguments.length} 个`
                            );
                        }
                        const arguments_ = expression.arguments.map(normalizedMetadataAst);
                        const replacements = new Map<string, AST>();
                        parameters.forEach(parameter => {
                            replacements.set(parameter.name, wrapVar(parameter.name));
                        });
                        argumentNames.forEach((name, index) => {
                            replacements.set(name, arguments_[index]);
                        });
                        return {
                            kind: "atom",
                            path: referencedPath,
                            arguments: arguments_,
                            term: wrapApply(
                                wrapVar(expression.name),
                                ...parameters.map(parameter => wrapVar(parameter.name)),
                                ...arguments_.map(argument => Core.clone(argument))
                            ),
                            sourcePoint: substituteGeneratedFreeNames(
                                normalizedMetadataAst(referencedPath.left), replacements
                            ),
                            targetPoint: substituteGeneratedFreeNames(
                                normalizedMetadataAst(referencedPath.right), replacements
                            )
                        };
                    }
                    if (expression.kind === "compose") {
                        const left = evaluateOnePathExpression(
                            expression.left, owner, side, state, depth + 1
                        );
                        const right = evaluateOnePathExpression(
                            expression.right, owner, side, state, depth + 1
                        );
                        if (!sameGeneratedAstAlpha(left.targetPoint, right.sourcePoint)) {
                            throw new Error(`${label}组合项的中间点边界不一致`);
                        }
                        return {
                            kind: "compose",
                            left,
                            right,
                            term: wrapApply(
                                wrapVar("compeq"),
                                Core.clone(left.term),
                                Core.clone(right.term)
                            ),
                            sourcePoint: Core.clone(left.sourcePoint),
                            targetPoint: Core.clone(right.targetPoint)
                        };
                    }
                    if (expression.kind === "inverse") {
                        const value = evaluateOnePathExpression(
                            expression.value, owner, side, state, depth + 1
                        );
                        return {
                            kind: "inverse",
                            value,
                            term: wrapApply(wrapVar("inveq"), Core.clone(value.term)),
                            sourcePoint: Core.clone(value.targetPoint),
                            targetPoint: Core.clone(value.sourcePoint)
                        };
                    }
                    throw new Error(`${label}表达式 kind 无效`);
                } finally {
                    state.ancestors.delete(expression);
                }
            };
            const validateTwoPathEndpoint = (
                owner: string,
                side: string,
                endpoint: AST,
                referencedName: string
            ) => {
                const application = generatedApplicationParts(endpoint);
                const endpointHead = generatedFreeConstantName(application.head) ?? "";
                if (endpointHead !== referencedName || application.arguments.length < parameters.length) {
                    throw new Error(
                        `二维 HIT 二阶路径构造子 ${owner} ${side}端点不是已认证的一阶路径原子：`
                        + `${endpointHead || "<非常量>"}`
                    );
                }
                for (let index = 0; index < parameters.length; index++) {
                    const parameter = parameters[index];
                    if (!sameGeneratedAst(application.arguments[index], wrapVar(parameter.name))) {
                        throw new Error(
                            `二维 HIT 二阶路径构造子 ${owner} ${side}端点未保持统一参数：`
                            + parameter.name
                        );
                    }
                }
                const evaluated = evaluateOnePathExpression({
                    kind: "atom",
                    name: referencedName,
                    arguments: application.arguments
                        .slice(parameters.length)
                        .map(argument => Core.clone(argument))
                }, owner, side);
                if (!sameGeneratedAst(evaluated.term, endpoint)) {
                    throw new Error(`二维 HIT 二阶路径构造子 ${owner} ${side}端点与原子重建不一致`);
                }
                return evaluated;
            };
            const onePathRecursorMethodValue = (
                expression: EvaluatedOnePathExpression,
                methodNames: readonly string[],
                label: string
            ): AST => {
                if (expression.kind === "atom") {
                    const index = metadataPathEntries.findIndex(entry =>
                        entry.name === expression.path.name
                    );
                    if (index < 0 || !methodNames[index]) {
                        throw new Error(`${label} 引用了未知一阶路径方法：${expression.path.name}`);
                    }
                    return wrapApply(
                        wrapVar(methodNames[index]),
                        ...expression.arguments.map(argument => Core.clone(argument))
                    );
                }
                if (expression.kind === "compose") {
                    return {
                        type: "*",
                        name: "",
                        nodes: [
                            onePathRecursorMethodValue(expression.left, methodNames, label),
                            onePathRecursorMethodValue(expression.right, methodNames, label)
                        ]
                    };
                }
                return wrapApply(
                    wrapVar("inveq"),
                    onePathRecursorMethodValue(expression.value, methodNames, label)
                );
            };
            const onePathDependentMethodValue = (
                expression: EvaluatedOnePathExpression,
                motiveName: string,
                branchNames: readonly string[],
                methodNames: readonly string[],
                label: string
            ): AST => {
                if (expression.kind === "atom") {
                    const index = metadataPathEntries.findIndex(entry =>
                        entry.name === expression.path.name
                    );
                    if (index < 0 || !methodNames[index]) {
                        throw new Error(`${label} 引用了未知一阶路径方法：${expression.path.name}`);
                    }
                    return wrapApply(
                        wrapVar(methodNames[index]),
                        ...expression.arguments.map(argument => Core.clone(argument))
                    );
                }
                if (expression.kind === "compose") {
                    return wrapApply(
                        wrapVar("hit_dep1_comp"),
                        wrapVar(motiveName),
                        hitBranchValue(expression.left.sourcePoint, branchNames, label),
                        hitBranchValue(expression.left.targetPoint, branchNames, label),
                        hitBranchValue(expression.right.targetPoint, branchNames, label),
                        onePathDependentMethodValue(
                            expression.left, motiveName, branchNames, methodNames, label
                        ),
                        onePathDependentMethodValue(
                            expression.right, motiveName, branchNames, methodNames, label
                        )
                    );
                }
                return wrapApply(
                    wrapVar("hit_dep1_inv"),
                    wrapVar(motiveName),
                    hitBranchValue(expression.value.sourcePoint, branchNames, label),
                    hitBranchValue(expression.value.targetPoint, branchNames, label),
                    onePathDependentMethodValue(
                        expression.value, motiveName, branchNames, methodNames, label
                    )
                );
            };

            const evaluatedTwoPathEndpoints = new Map<string, {
                left: EvaluatedOnePathExpression;
                right: EvaluatedOnePathExpression;
            }>();
            for (const path of metadataTwoPathEntries) {
                if (metadata.ruleSchemaVersion === 1
                    && (!Array.isArray(path.argumentNames)
                        || path.argumentNames.length !== path.argumentTypes.length
                        || new Set(path.argumentNames).size !== path.argumentNames.length)) {
                    throw new Error(`二维 HIT 二阶路径构造子 ${path.name} argumentNames 与 telescope 不一致`);
                }
                const pathType = auxiliaryTypes.get(path.name);
                if (!pathType) {
                    throw new Error(`二维 HIT metadata 二阶路径构造子不存在：${path.name}`);
                }
                const conclusion = consumeTelescope(pathType, [
                    ...parameters.map(parameter => parameter.type),
                    ...path.argumentTypes.map(normalizedMetadataAst)
                ], `二维 HIT 二阶路径构造子 ${path.name}`);
                const leftEndpoint = evaluateOnePathExpression(
                    path.leftExpression, path.name, "左"
                );
                const rightEndpoint = evaluateOnePathExpression(
                    path.rightExpression, path.name, "右"
                );
                const endpoints = generatedEqualityEndpoints(conclusion);
                if (!endpoints
                    || !sameGeneratedAst(endpoints[0], leftEndpoint.term)
                    || !sameGeneratedAst(endpoints[1], rightEndpoint.term)) {
                    throw new Error(`二维 HIT 二阶路径构造子 ${path.name} 端点与 metadata 不一致`);
                }
                if (!sameGeneratedAstAlpha(leftEndpoint.sourcePoint, rightEndpoint.sourcePoint)
                    || !sameGeneratedAstAlpha(leftEndpoint.targetPoint, rightEndpoint.targetPoint)) {
                    throw new Error(`二维 HIT 二阶路径构造子 ${path.name} 的点边界不一致`);
                }
                evaluatedTwoPathEndpoints.set(path.name, {
                    left: leftEndpoint,
                    right: rightEndpoint
                });
                const computationNames = [
                    `apd_${path.name}`,
                    `@apd_${path.name}`,
                    `ap_${path.name}`,
                    `@ap_${path.name}`,
                    `ap2_${path.name}`,
                    `@ap2_${path.name}`
                ];
                if (path.computationName !== computationNames[0]) {
                    throw new Error(`二维 HIT metadata 计算定理不存在：${path.computationName ?? ""}`);
                }
                if (path.strongComputationName !== computationNames[4]) {
                    throw new Error(
                        `二维 HIT metadata 强计算定理不存在：${path.strongComputationName ?? ""}`
                    );
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

            type EvaluatedTwoPathExpression =
                | {
                    kind: "atom";
                    path: CoreHitTwoPathConstructorMetadata;
                    arguments: AST[];
                    term: AST;
                    sourceExpression: EvaluatedOnePathExpression;
                    targetExpression: EvaluatedOnePathExpression;
                    sourcePath: AST;
                    targetPath: AST;
                }
                | {
                    kind: "refl";
                    path: CoreHitPathConstructorMetadata;
                    arguments: AST[];
                    term: AST;
                    sourceExpression: EvaluatedOnePathExpression;
                    targetExpression: EvaluatedOnePathExpression;
                    sourcePath: AST;
                    targetPath: AST;
                }
                | {
                    kind: "compose";
                    left: EvaluatedTwoPathExpression;
                    right: EvaluatedTwoPathExpression;
                    term: AST;
                    sourceExpression: EvaluatedOnePathExpression;
                    targetExpression: EvaluatedOnePathExpression;
                    sourcePath: AST;
                    targetPath: AST;
                }
                | {
                    kind: "inverse";
                    value: EvaluatedTwoPathExpression;
                    term: AST;
                    sourceExpression: EvaluatedOnePathExpression;
                    targetExpression: EvaluatedOnePathExpression;
                    sourcePath: AST;
                    targetPath: AST;
                };
            const evaluateTwoPathExpression = (
                expression: CoreHitTwoPathExpression | undefined,
                owner: string,
                side: string,
                state = { nodes: 0, ancestors: new WeakSet<object>() },
                depth = 0
            ): EvaluatedTwoPathExpression => {
                const label = `三维 HIT 三阶路径构造子 ${owner} ${side}端点`;
                if (!expression || typeof expression !== "object") {
                    throw new Error(`${label}缺少二阶路径表达式`);
                }
                if (depth > CORE_HIT_TWO_PATH_EXPRESSION_MAX_DEPTH) {
                    throw new Error(`${label}表达式嵌套过深`);
                }
                if (++state.nodes > CORE_HIT_TWO_PATH_EXPRESSION_MAX_NODES) {
                    throw new Error(`${label}表达式节点过多`);
                }
                if (state.ancestors.has(expression)) {
                    throw new Error(`${label}表达式不能循环引用自身`);
                }
                state.ancestors.add(expression);
                try {
                    if (expression.kind === "atom") {
                        const referencedPath = twoPathMetadataByName.get(expression.name);
                        if (!referencedPath) {
                            throw new Error(`${label}引用不存在：${expression.name}`);
                        }
                        const argumentNames = referencedPath.argumentNames ?? [];
                        if (argumentNames.length !== referencedPath.argumentTypes.length
                            || new Set(argumentNames).size !== argumentNames.length) {
                            throw new Error(
                                `三维 HIT 二阶路径 ${expression.name} argumentNames 与 telescope 不一致`
                            );
                        }
                        if (expression.arguments.length !== argumentNames.length) {
                            throw new Error(
                                `${label}参数数量与二阶路径 ${expression.name} telescope 不一致：`
                                + `需要 ${argumentNames.length} 个，实际 ${expression.arguments.length} 个`
                            );
                        }
                        const arguments_ = expression.arguments.map(normalizedMetadataAst);
                        const replacements = new Map<string, AST>();
                        argumentNames.forEach((name, index) => {
                            replacements.set(name, arguments_[index]);
                        });
                        if (!referencedPath.leftExpression || !referencedPath.rightExpression) {
                            throw new Error(`${label}引用的二阶路径缺少已认证端点：${expression.name}`);
                        }
                        const sourceExpression = evaluateOnePathExpression(
                            mapCoreHitOnePathExpression(
                                referencedPath.leftExpression,
                                ast => substituteGeneratedFreeNames(ast, replacements)
                            ),
                            owner,
                            `${side}端点的来源`
                        );
                        const targetExpression = evaluateOnePathExpression(
                            mapCoreHitOnePathExpression(
                                referencedPath.rightExpression,
                                ast => substituteGeneratedFreeNames(ast, replacements)
                            ),
                            owner,
                            `${side}端点的目标`
                        );
                        return {
                            kind: "atom",
                            path: referencedPath,
                            arguments: arguments_,
                            term: wrapApply(
                                wrapVar(expression.name),
                                ...parameters.map(parameter => wrapVar(parameter.name)),
                                ...arguments_.map(argument => Core.clone(argument))
                            ),
                            sourceExpression,
                            targetExpression,
                            sourcePath: Core.clone(sourceExpression.term),
                            targetPath: Core.clone(targetExpression.term)
                        };
                    }
                    if (expression.kind === "refl") {
                        const referencedPath = pathMetadataByName.get(expression.pathName);
                        if (!referencedPath) {
                            throw new Error(`${label}引用的一阶路径不存在：${expression.pathName}`);
                        }
                        const argumentNames = referencedPath.argumentNames ?? [];
                        if (argumentNames.length !== referencedPath.argumentTypes.length
                            || new Set(argumentNames).size !== argumentNames.length) {
                            throw new Error(
                                `三维 HIT 一阶路径 ${expression.pathName} argumentNames 与 telescope 不一致`
                            );
                        }
                        if (expression.arguments.length !== argumentNames.length) {
                            throw new Error(
                                `${label}参数数量与一阶路径 ${expression.pathName} telescope 不一致：`
                                + `需要 ${argumentNames.length} 个，实际 ${expression.arguments.length} 个`
                            );
                        }
                        const arguments_ = expression.arguments.map(normalizedMetadataAst);
                        const pathTerm = wrapApply(
                            wrapVar(expression.pathName),
                            ...parameters.map(parameter => wrapVar(parameter.name)),
                            ...arguments_.map(argument => Core.clone(argument))
                        );
                        const evaluated = validateTwoPathEndpoint(
                            owner, `${side}端点的反身一阶路径`, pathTerm, expression.pathName
                        );
                        return {
                            kind: "refl",
                            path: referencedPath,
                            arguments: arguments_,
                            term: wrapApply(wrapVar("refl"), Core.clone(pathTerm)),
                            sourceExpression: evaluated,
                            targetExpression: evaluated,
                            sourcePath: Core.clone(pathTerm),
                            targetPath: Core.clone(pathTerm)
                        };
                    }
                    if (expression.kind === "compose") {
                        const left = evaluateTwoPathExpression(
                            expression.left, owner, side, state, depth + 1
                        );
                        const right = evaluateTwoPathExpression(
                            expression.right, owner, side, state, depth + 1
                        );
                        if (!sameGeneratedAstAlpha(left.targetPath, right.sourcePath)) {
                            throw new Error(`${label}组合项的中间一阶路径边界不一致`);
                        }
                        return {
                            kind: "compose",
                            left,
                            right,
                            term: wrapApply(
                                wrapVar("compeq"),
                                Core.clone(left.term),
                                Core.clone(right.term)
                            ),
                            sourceExpression: left.sourceExpression,
                            targetExpression: right.targetExpression,
                            sourcePath: Core.clone(left.sourcePath),
                            targetPath: Core.clone(right.targetPath)
                        };
                    }
                    if (expression.kind === "inverse") {
                        const value = evaluateTwoPathExpression(
                            expression.value, owner, side, state, depth + 1
                        );
                        return {
                            kind: "inverse",
                            value,
                            term: wrapApply(wrapVar("inveq"), Core.clone(value.term)),
                            sourceExpression: value.targetExpression,
                            targetExpression: value.sourceExpression,
                            sourcePath: Core.clone(value.targetPath),
                            targetPath: Core.clone(value.sourcePath)
                        };
                    }
                    throw new Error(`${label}表达式 kind 无效`);
                } finally {
                    state.ancestors.delete(expression);
                }
            };
            const evaluatedThreePathEndpoints = new Map<string, {
                left: EvaluatedTwoPathExpression;
                right: EvaluatedTwoPathExpression;
            }>();

            for (const path of metadataThreePathEntries) {
                if (!Array.isArray(path.argumentNames)
                    || path.argumentNames.length !== path.argumentTypes.length
                    || new Set(path.argumentNames).size !== path.argumentNames.length) {
                    throw new Error(`三维 HIT 三阶路径构造子 ${path.name} argumentNames 与 telescope 不一致`);
                }
                if (path.computationName !== `apd3_${path.name}`) {
                    throw new Error(
                        `三维 HIT dependent 计算定理不存在：${path.computationName ?? ""}`
                    );
                }
                if (path.actionComputationName !== `ap3_${path.name}`) {
                    throw new Error(
                        `三维 HIT action 计算定理不存在：${path.actionComputationName ?? ""}`
                    );
                }
                const pathType = auxiliaryTypes.get(path.name);
                if (!pathType) {
                    throw new Error(`三维 HIT metadata 三阶路径构造子不存在：${path.name}`);
                }
                const conclusion = consumeTelescope(pathType, [
                    ...parameters.map(parameter => parameter.type),
                    ...path.argumentTypes.map(normalizedMetadataAst)
                ], `三维 HIT 三阶路径构造子 ${path.name}`);
                const leftEndpoint = evaluateTwoPathExpression(
                    path.leftExpression, path.name, "左"
                );
                const rightEndpoint = evaluateTwoPathExpression(
                    path.rightExpression, path.name, "右"
                );
                const endpoints = generatedEqualityEndpoints(conclusion);
                if (!endpoints
                    || !sameGeneratedAst(endpoints[0], leftEndpoint.term)
                    || !sameGeneratedAst(endpoints[1], rightEndpoint.term)) {
                    throw new Error(`三维 HIT 三阶路径构造子 ${path.name} 端点与 metadata 不一致`);
                }
                if (!sameGeneratedAstAlpha(leftEndpoint.sourcePath, rightEndpoint.sourcePath)
                    || !sameGeneratedAstAlpha(leftEndpoint.targetPath, rightEndpoint.targetPath)) {
                    throw new Error(`三维 HIT 三阶路径构造子 ${path.name} 的二阶路径边界不一致`);
                }
                evaluatedThreePathEndpoints.set(path.name, {
                    left: leftEndpoint,
                    right: rightEndpoint
                });
                for (const computationName of [
                    `apd3_${path.name}`,
                    `@apd3_${path.name}`,
                    `ap3_${path.name}`,
                    `@ap3_${path.name}`
                ]) {
                    const computationType = auxiliaryTypes.get(computationName);
                    if (!computationType) {
                        throw new Error(`三维 HIT 计算定理槽位不存在：${computationName}`);
                    }
                    let computationConclusion = computationType;
                    while ((computationConclusion.type === "P" || computationConclusion.type === "->")
                        && computationConclusion.nodes?.[1]) {
                        computationConclusion = computationConclusion.nodes[1];
                    }
                    if (!generatedEqualityEndpoints(computationConclusion)) {
                        throw new Error(`三维 HIT 计算定理 ${computationName} 不是等式命题`);
                    }
                }
            }

            if (metadataTwoPathEntries.length) {
                const readRecursorTelescope = (source: AST, label: string) => {
                    const binders: { name: string; type: AST }[] = [];
                    let cursor = source;
                    while ((cursor.type === "P" || cursor.type === "->")
                        && cursor.nodes?.[0] && cursor.nodes?.[1]) {
                        binders.push({
                            name: cursor.type === "P" ? cursor.name : "",
                            type: Core.clone(cursor.nodes[0])
                        });
                        cursor = cursor.nodes[1];
                    }
                    if (!binders.length) throw new Error(`${label} telescope 不完整`);
                    return binders;
                };
                const strongEquality = (left: AST, right: AST): AST => ({
                    type: "=",
                    name: "",
                    nodes: [left, right]
                });
                const strongCompose = (left: AST, right: AST): AST => ({
                    type: "*",
                    name: "",
                    nodes: [left, right]
                });
                const strongLambda = (name: string, type: AST, body: AST): AST => ({
                    type: "L",
                    name,
                    nodes: [type, body]
                });
                const strongWrapPis = (
                    binders: readonly { name: string; type: AST }[],
                    body: AST
                ) => {
                    let result = body;
                    for (let index = binders.length - 1; index >= 0; index--) {
                        result = {
                            type: "P",
                            name: binders[index].name,
                            nodes: [Core.clone(binders[index].type), result]
                        };
                    }
                    return result;
                };
                const validateTwoPathCoherenceTelescope = (
                    source: AST,
                    full: boolean,
                    dependent: boolean,
                    label: string
                ) => {
                    const binders = readRecursorTelescope(source, label);
                    const expectedCount = (full ? 1 : 0)
                        + parameters.length
                        + 1
                        + metadata.constructors.length
                        + metadataPathEntries.length
                        + metadataTwoPathEntries.length
                        + metadataThreePathEntries.length
                        + 1;
                    if (binders.length !== expectedCount) {
                        throw new Error(`${label} telescope 长度与二维 metadata 不一致`);
                    }
                    let offset = full ? 1 : 0;
                    offset += parameters.length;
                    const motiveName = binders[offset++].name;
                    const branchNames = binders
                        .slice(offset, offset + metadata.constructors.length)
                        .map(binder => binder.name);
                    offset += metadata.constructors.length;
                    const pathMethodNames = binders
                        .slice(offset, offset + metadataPathEntries.length)
                        .map(binder => binder.name);
                    offset += metadataPathEntries.length;
                    const twoPathMethodOffset = offset;
                    offset += metadataTwoPathEntries.length;
                    offset += metadataThreePathEntries.length;
                    for (let index = 0; index < metadataTwoPathEntries.length; index++) {
                        const path = metadataTwoPathEntries[index];
                        const endpointData = evaluatedTwoPathEndpoints.get(path.name);
                        if (!endpointData) {
                            throw new Error(`${label} ${path.name} 缺少已认证的一阶路径表达式端点`);
                        }
                        const argumentNames = path.argumentNames ?? [];
                        const localBinders = argumentNames.map((name, argumentIndex) => ({
                            name,
                            type: normalizedMetadataAst(path.argumentTypes[argumentIndex])
                        }));
                        const leftMethod = dependent
                            ? onePathDependentMethodValue(
                                endpointData.left,
                                motiveName,
                                branchNames,
                                pathMethodNames,
                                `${label} ${path.name}`
                            )
                            : onePathRecursorMethodValue(
                                endpointData.left,
                                pathMethodNames,
                                `${label} ${path.name}`
                            );
                        const rightMethod = dependent
                            ? onePathDependentMethodValue(
                                endpointData.right,
                                motiveName,
                                branchNames,
                                pathMethodNames,
                                `${label} ${path.name}`
                            )
                            : onePathRecursorMethodValue(
                                endpointData.right,
                                pathMethodNames,
                                `${label} ${path.name}`
                            );
                        let expectedBody: AST;
                        if (dependent) {
                            const pathTerm = wrapApply(
                                wrapVar(path.name),
                                ...parameters.map(parameter => wrapVar(parameter.name)),
                                ...argumentNames.map(wrapVar)
                            );
                            const endpointValue = hitBranchValue(
                                endpointData.left.sourcePoint,
                                branchNames,
                                `${label} ${path.name}`
                            );
                            expectedBody = strongEquality(
                                leftMethod,
                                strongCompose(
                                    wrapApply(
                                        wrapVar("trans2"),
                                        wrapVar(motiveName),
                                        pathTerm,
                                        endpointValue
                                    ),
                                    rightMethod
                                )
                            );
                        } else {
                            expectedBody = strongEquality(leftMethod, rightMethod);
                        }
                        const expected = normalizedMetadataAst(
                            strongWrapPis(localBinders, expectedBody)
                        );
                        const actual = binders[twoPathMethodOffset + index]?.type;
                        if (!actual || !sameGeneratedAstAlpha(actual, expected)) {
                            throw new Error(`${label} 二阶 coherence ${path.name} 与 metadata 不一致`);
                        }
                    }
                };

                const publicEliminatorType = bundle.eliminator?.[1]
                    ? normalizedMetadataAst(bundle.eliminator[1])
                    : undefined;
                const fullEliminatorType = metadata.fullEliminatorName
                    ? auxiliaryTypes.get(metadata.fullEliminatorName)
                    : undefined;
                const publicRecursorType = bundle.recursor?.[1]
                    ? normalizedMetadataAst(bundle.recursor[1])
                    : undefined;
                const fullRecursorType = metadata.fullRecursorName
                    ? auxiliaryTypes.get(metadata.fullRecursorName)
                    : undefined;
                if (!publicEliminatorType || !fullEliminatorType
                    || !publicRecursorType || !fullRecursorType) {
                    throw new Error("二维 HIT 消去器/递归器槽位不完整");
                }
                validateTwoPathCoherenceTelescope(
                    publicEliminatorType, false, true, "公开消去器"
                );
                validateTwoPathCoherenceTelescope(
                    fullEliminatorType, true, true, "完整消去器"
                );
                validateTwoPathCoherenceTelescope(
                    publicRecursorType, false, false, "公开递归器"
                );
                validateTwoPathCoherenceTelescope(
                    fullRecursorType, true, false, "完整递归器"
                );

                const validateDependentTwoPathComputation = (
                    path: CoreHitTwoPathConstructorMetadata,
                    full: boolean
                ) => {
                    const eliminatorName = full
                        ? metadata.fullEliminatorName
                        : metadata.eliminatorName;
                    const eliminatorType = full
                        ? (metadata.fullEliminatorName
                            ? auxiliaryTypes.get(metadata.fullEliminatorName)
                            : undefined)
                        : bundle.eliminator?.[1] && normalizedMetadataAst(bundle.eliminator[1]);
                    const computationName = `${full ? "@" : ""}apd_${path.name}`;
                    const actualComputationType = auxiliaryTypes.get(computationName);
                    if (!eliminatorName || !eliminatorType || !actualComputationType) {
                        throw new Error(`二维 HIT dependent 计算定理槽位不存在：${computationName}`);
                    }
                    const binders = readRecursorTelescope(
                        eliminatorType, full ? "完整消去器" : "公开消去器"
                    );
                    let offset = full ? 1 : 0;
                    offset += parameters.length;
                    const motiveName = binders[offset++].name;
                    const branchNames = binders
                        .slice(offset, offset + metadata.constructors.length)
                        .map(binder => binder.name);
                    offset += metadata.constructors.length;
                    const pathMethodNames = binders
                        .slice(offset, offset + metadataPathEntries.length)
                        .map(binder => binder.name);
                    offset += metadataPathEntries.length;
                    const twoPathMethodNames = binders
                        .slice(offset, offset + metadataTwoPathEntries.length)
                        .map(binder => binder.name);
                    offset += metadataTwoPathEntries.length;
                    offset += metadataThreePathEntries.length;
                    if (binders.length !== offset + 1) {
                        throw new Error("二维 HIT 消去器 telescope 与 dependent 计算 metadata 不一致");
                    }
                    const prefixBinders = binders.slice(0, offset);
                    const prefixValues = prefixBinders.map(binder => wrapVar(binder.name));
                    let familyUniverse = normalizedMetadataAst(bundle.type[1]);
                    for (let index = 0; index < parameters.length; index++) {
                        if (familyUniverse.type !== "P" || !familyUniverse.nodes?.[1]) {
                            throw new Error(`二维 HIT ${metadata.typeName} 的 Universe telescope 不完整`);
                        }
                        familyUniverse = familyUniverse.nodes[1];
                    }
                    if (familyUniverse.type !== "apply"
                        || familyUniverse.nodes?.[0]?.type !== "var"
                        || familyUniverse.nodes[0].name !== "U"
                        || !familyUniverse.nodes[1]) {
                        throw new Error(`二维 HIT ${metadata.typeName} 的 Universe 缺少显式层级`);
                    }
                    const hitUniverseLevel = Core.clone(familyUniverse.nodes[1]);
                    const motiveUniverseLevel = full
                        ? Core.clone(prefixValues[0])
                        : wrapVar("@0");
                    const hitType = wrapApply(
                        wrapVar(metadata.typeName),
                        ...parameters.map(parameter => wrapVar(parameter.name))
                    );
                    const dependentHead = wrapApply(
                        wrapVar(eliminatorName),
                        ...prefixValues.map(value => Core.clone(value))
                    );
                    const expressionData = (
                        expression: EvaluatedOnePathExpression
                    ): {
                        term: AST;
                        sourcePoint: AST;
                        targetPoint: AST;
                        sourceValue: AST;
                        targetValue: AST;
                        type: AST;
                        method: AST;
                        computation: AST;
                    } => {
                        const sourceValue = hitBranchValue(
                            expression.sourcePoint, branchNames, computationName
                        );
                        const targetValue = hitBranchValue(
                            expression.targetPoint, branchNames, computationName
                        );
                        const method = onePathDependentMethodValue(
                            expression,
                            motiveName,
                            branchNames,
                            pathMethodNames,
                            computationName
                        );
                        let computation: AST;
                        if (expression.kind === "atom") {
                            computation = wrapApply(
                                wrapVar(`${full ? "@" : ""}apd_${expression.path.name}`),
                                ...prefixValues.map(value => Core.clone(value)),
                                ...expression.arguments.map(argument => Core.clone(argument))
                            );
                        } else if (expression.kind === "compose") {
                            const left = expressionData(expression.left);
                            const right = expressionData(expression.right);
                            computation = wrapApply(
                                wrapVar("@hit_apd1_corrected_comp"),
                                Core.clone(hitUniverseLevel),
                                Core.clone(motiveUniverseLevel),
                                Core.clone(hitType),
                                Core.clone(expression.left.sourcePoint),
                                Core.clone(expression.left.targetPoint),
                                Core.clone(expression.right.targetPoint),
                                Core.clone(expression.left.term),
                                Core.clone(expression.right.term),
                                wrapVar(motiveName),
                                Core.clone(dependentHead),
                                Core.clone(left.method),
                                Core.clone(right.method),
                                Core.clone(left.computation),
                                Core.clone(right.computation)
                            );
                        } else {
                            const value = expressionData(expression.value);
                            computation = wrapApply(
                                wrapVar("@hit_apd1_corrected_inv"),
                                Core.clone(hitUniverseLevel),
                                Core.clone(motiveUniverseLevel),
                                Core.clone(hitType),
                                Core.clone(expression.value.sourcePoint),
                                Core.clone(expression.value.targetPoint),
                                Core.clone(expression.value.term),
                                wrapVar(motiveName),
                                Core.clone(dependentHead),
                                Core.clone(value.method),
                                Core.clone(value.computation)
                            );
                        }
                        return {
                            term: Core.clone(expression.term),
                            sourcePoint: Core.clone(expression.sourcePoint),
                            targetPoint: Core.clone(expression.targetPoint),
                            sourceValue,
                            targetValue,
                            type: strongEquality(
                                wrapApply(
                                    wrapVar("trans"),
                                    wrapVar(motiveName),
                                    Core.clone(expression.term),
                                    Core.clone(sourceValue)
                                ),
                                Core.clone(targetValue)
                            ),
                            method,
                            computation
                        };
                    };
                    const endpointData = evaluatedTwoPathEndpoints.get(path.name);
                    if (!endpointData) {
                        throw new Error(`${computationName} 缺少已认证的一阶路径表达式端点`);
                    }
                    const left = expressionData(endpointData.left);
                    const right = expressionData(endpointData.right);
                    const argumentNames = path.argumentNames ?? [];
                    const argumentValues = argumentNames.map(wrapVar);
                    const pathTerm = wrapApply(
                        wrapVar(path.name),
                        ...parameters.map(parameter => wrapVar(parameter.name)),
                        ...argumentValues.map(argument => Core.clone(argument))
                    );
                    const pathIndex = metadataTwoPathEntries.findIndex(entry => entry.name === path.name);
                    const methodValue = wrapApply(
                        wrapVar(twoPathMethodNames[pathIndex]),
                        ...argumentValues.map(argument => Core.clone(argument))
                    );
                    const transport2Value = wrapApply(
                        wrapVar("trans2"),
                        wrapVar(motiveName),
                        Core.clone(pathTerm),
                        Core.clone(left.sourceValue)
                    );
                    const occupied = new Set([
                        ...prefixBinders.map(binder => binder.name),
                        ...argumentNames
                    ]);
                    let pathValueName = "pathValue";
                    while (occupied.has(pathValueName)) pathValueName += "_";
                    const targetWhisker = strongLambda(
                        pathValueName,
                        Core.clone(right.type),
                        strongCompose(
                            Core.clone(transport2Value),
                            wrapVar(pathValueName)
                        )
                    );
                    const correctedMethod = strongCompose(
                        strongCompose(Core.clone(left.computation), methodValue),
                        wrapApply(
                            wrapVar("inveq"),
                            wrapApply(
                                wrapVar("ap"),
                                targetWhisker,
                                Core.clone(right.computation)
                            )
                        )
                    );
                    const action = wrapApply(
                        wrapVar("apd2"),
                        Core.clone(dependentHead),
                        Core.clone(pathTerm)
                    );
                    const localBinders = argumentNames.map((name, index) => ({
                        name,
                        type: normalizedMetadataAst(path.argumentTypes[index])
                    }));
                    const expected = normalizedMetadataAst(strongWrapPis(
                        [...prefixBinders, ...localBinders],
                        strongEquality(action, correctedMethod)
                    ));
                    if (!sameGeneratedAstAlpha(actualComputationType, expected)) {
                        throw new Error(
                            `二维 HIT dependent 计算定理 ${computationName} 与 metadata 不一致`
                        );
                    }
                };

                for (const path of metadataTwoPathEntries) {
                    validateDependentTwoPathComputation(path, false);
                    validateDependentTwoPathComputation(path, true);
                }

                const validateStrongTwoPathComputation = (
                    path: CoreHitTwoPathConstructorMetadata,
                    full: boolean
                ) => {
                    const recursorName = full ? metadata.fullRecursorName : metadata.recursorName;
                    const recursorType = full
                        ? (metadata.fullRecursorName
                            ? auxiliaryTypes.get(metadata.fullRecursorName)
                            : undefined)
                        : bundle.recursor?.[1] && normalizedMetadataAst(bundle.recursor[1]);
                    const computationName = `${full ? "@" : ""}ap2_${path.name}`;
                    const actualComputationType = auxiliaryTypes.get(computationName);
                    if (!recursorName || !recursorType || !actualComputationType) {
                        throw new Error(`二维 HIT 强计算定理槽位不存在：${computationName}`);
                    }
                    const recursorBinders = readRecursorTelescope(
                        recursorType, full ? "完整递归器" : "公开递归器"
                    );
                    const pathEntries = metadataPathEntries;
                    const twoPathEntries = metadataTwoPathEntries;
                    const threePathEntries = metadataThreePathEntries;
                    let offset = full ? 1 : 0;
                    offset += parameters.length;
                    const motiveName = recursorBinders[offset++].name;
                    offset += metadata.constructors.length;
                    const pathMethodNames = recursorBinders
                        .slice(offset, offset + pathEntries.length)
                        .map(binder => binder.name);
                    offset += pathEntries.length;
                    const twoPathMethodNames = recursorBinders
                        .slice(offset, offset + twoPathEntries.length)
                        .map(binder => binder.name);
                    offset += twoPathEntries.length;
                    offset += threePathEntries.length;
                    if (recursorBinders.length !== offset + 1) {
                        throw new Error("二维 HIT 递归器 telescope 与高阶路径 metadata 不一致");
                    }
                    const prefixBinders = recursorBinders.slice(0, offset);
                    const prefixValues = prefixBinders.map(binder => wrapVar(binder.name));
                    let familyUniverse = normalizedMetadataAst(bundle.type[1]);
                    for (let index = 0; index < parameters.length; index++) {
                        if (familyUniverse.type !== "P" || !familyUniverse.nodes?.[1]) {
                            throw new Error(`二维 HIT ${metadata.typeName} 的 Universe telescope 不完整`);
                        }
                        familyUniverse = familyUniverse.nodes[1];
                    }
                    if (familyUniverse.type !== "apply"
                        || familyUniverse.nodes?.[0]?.type !== "var"
                        || familyUniverse.nodes[0].name !== "U"
                        || !familyUniverse.nodes[1]) {
                        throw new Error(`二维 HIT ${metadata.typeName} 的 Universe 缺少显式层级`);
                    }
                    const hitUniverseLevel = Core.clone(familyUniverse.nodes[1]);
                    const motiveUniverseLevel = full
                        ? Core.clone(prefixValues[0])
                        : wrapVar("@0");
                    const hitType = wrapApply(
                        wrapVar(metadata.typeName),
                        ...parameters.map(parameter => wrapVar(parameter.name))
                    );
                    const recursorHead = wrapApply(
                        wrapVar(recursorName),
                        ...prefixValues.map(value => Core.clone(value))
                    );
                    const endpointComputation = (endpoint: EvaluatedOnePathExpression): AST => {
                        if (endpoint.kind === "atom") {
                            return wrapApply(
                                wrapVar(`${full ? "@" : ""}ap_${endpoint.path.name}`),
                                ...prefixValues.map(value => Core.clone(value)),
                                ...endpoint.arguments.map(argument => Core.clone(argument))
                            );
                        }
                        if (endpoint.kind === "compose") {
                            const left = endpointComputation(endpoint.left);
                            const right = endpointComputation(endpoint.right);
                            return wrapApply(
                                wrapVar("@hit_ap1_corrected_comp"),
                                Core.clone(hitUniverseLevel),
                                Core.clone(motiveUniverseLevel),
                                Core.clone(hitType),
                                wrapVar(motiveName),
                                Core.clone(endpoint.left.sourcePoint),
                                Core.clone(endpoint.left.targetPoint),
                                Core.clone(endpoint.right.targetPoint),
                                Core.clone(endpoint.left.term),
                                Core.clone(endpoint.right.term),
                                Core.clone(recursorHead),
                                onePathRecursorMethodValue(endpoint.left, pathMethodNames, computationName),
                                onePathRecursorMethodValue(endpoint.right, pathMethodNames, computationName),
                                left,
                                right
                            );
                        }
                        const value = endpointComputation(endpoint.value);
                        return wrapApply(
                            wrapVar("@hit_ap1_corrected_inv"),
                            Core.clone(hitUniverseLevel),
                            Core.clone(motiveUniverseLevel),
                            Core.clone(hitType),
                            wrapVar(motiveName),
                            Core.clone(endpoint.value.sourcePoint),
                            Core.clone(endpoint.value.targetPoint),
                            Core.clone(endpoint.value.term),
                            Core.clone(recursorHead),
                            onePathRecursorMethodValue(endpoint.value, pathMethodNames, computationName),
                            value
                        );
                    };
                    const endpointData = evaluatedTwoPathEndpoints.get(path.name);
                    if (!endpointData) {
                        throw new Error(`${computationName} 缺少已认证的一阶路径表达式端点`);
                    }
                    const leftEndpoint = endpointData.left;
                    const rightEndpoint = endpointData.right;
                    const leftComputation = endpointComputation(leftEndpoint);
                    const rightComputation = endpointComputation(rightEndpoint);
                    const pathIndex = twoPathEntries.findIndex(entry => entry.name === path.name);
                    const argumentNames = path.argumentNames ?? [];
                    const argumentValues = argumentNames.map(wrapVar);
                    const methodValue = wrapApply(
                        wrapVar(twoPathMethodNames[pathIndex]),
                        ...argumentValues.map(argument => Core.clone(argument))
                    );
                    const correctedMethod = strongCompose(
                        strongCompose(leftComputation, methodValue),
                        wrapApply(wrapVar("inveq"), rightComputation)
                    );
                    const pathTerm = wrapApply(
                        wrapVar(path.name),
                        ...parameters.map(parameter => wrapVar(parameter.name)),
                        ...argumentValues.map(argument => Core.clone(argument))
                    );
                    const strongAction = wrapApply(
                        wrapVar("hit_ap2"),
                        recursorHead,
                        pathTerm
                    );
                    const localBinders = argumentNames.map((name, index) => ({
                        name,
                        type: normalizedMetadataAst(path.argumentTypes[index])
                    }));
                    const expected = normalizedMetadataAst(strongWrapPis(
                        [...prefixBinders, ...localBinders],
                        strongEquality(strongAction, correctedMethod)
                    ));
                    if (!sameGeneratedAstAlpha(actualComputationType, expected)) {
                        throw new Error(`二维 HIT 强计算定理 ${computationName} 与 metadata 不一致`);
                    }
                };

                for (const path of metadataTwoPathEntries) {
                    validateStrongTwoPathComputation(path, false);
                    validateStrongTwoPathComputation(path, true);
                }

                const validateThreePathActionComputation = (
                    path: CoreHitThreePathConstructorMetadata,
                    full: boolean
                ) => {
                    const recursorName = full ? metadata.fullRecursorName : metadata.recursorName;
                    const recursorType = full
                        ? (metadata.fullRecursorName
                            ? auxiliaryTypes.get(metadata.fullRecursorName)
                            : undefined)
                        : bundle.recursor?.[1] && normalizedMetadataAst(bundle.recursor[1]);
                    const computationName = `${full ? "@" : ""}ap3_${path.name}`;
                    const actualComputationType = auxiliaryTypes.get(computationName);
                    if (!recursorName || !recursorType || !actualComputationType) {
                        throw new Error(`三维 HIT action 计算定理槽位不存在：${computationName}`);
                    }
                    const recursorBinders = readRecursorTelescope(
                        recursorType, full ? "完整递归器" : "公开递归器"
                    );
                    const pathEntries = metadataPathEntries;
                    const twoPathEntries = metadataTwoPathEntries;
                    const threePathEntries = metadataThreePathEntries;
                    let offset = full ? 1 : 0;
                    offset += parameters.length;
                    const motiveName = recursorBinders[offset++].name;
                    offset += metadata.constructors.length;
                    const pathMethodNames = recursorBinders
                        .slice(offset, offset + pathEntries.length)
                        .map(binder => binder.name);
                    offset += pathEntries.length;
                    const twoPathMethodNames = recursorBinders
                        .slice(offset, offset + twoPathEntries.length)
                        .map(binder => binder.name);
                    offset += twoPathEntries.length;
                    const threePathMethodNames = recursorBinders
                        .slice(offset, offset + threePathEntries.length)
                        .map(binder => binder.name);
                    offset += threePathEntries.length;
                    if (recursorBinders.length !== offset + 1) {
                        throw new Error("三维 HIT 递归器 telescope 与 action metadata 不一致");
                    }
                    const prefixBinders = recursorBinders.slice(0, offset);
                    const prefixValues = prefixBinders.map(binder => wrapVar(binder.name));
                    let familyUniverse = normalizedMetadataAst(bundle.type[1]);
                    for (let index = 0; index < parameters.length; index++) {
                        if (familyUniverse.type !== "P" || !familyUniverse.nodes?.[1]) {
                            throw new Error(`三维 HIT ${metadata.typeName} 的 Universe telescope 不完整`);
                        }
                        familyUniverse = familyUniverse.nodes[1];
                    }
                    if (familyUniverse.type !== "apply"
                        || familyUniverse.nodes?.[0]?.type !== "var"
                        || familyUniverse.nodes[0].name !== "U"
                        || !familyUniverse.nodes[1]) {
                        throw new Error(`三维 HIT ${metadata.typeName} 的 Universe 缺少显式层级`);
                    }
                    const hitUniverseLevel = Core.clone(familyUniverse.nodes[1]);
                    const motiveUniverseLevel = full
                        ? Core.clone(prefixValues[0])
                        : wrapVar("@0");
                    const hitType = wrapApply(
                        wrapVar(metadata.typeName),
                        ...parameters.map(parameter => wrapVar(parameter.name))
                    );
                    const endpointData = evaluatedThreePathEndpoints.get(path.name);
                    if (!endpointData) {
                        throw new Error(`${computationName} 缺少已认证的表达式端点`);
                    }
                    const sourcePathExpression = endpointData.left.sourceExpression;
                    const targetPathExpression = endpointData.left.targetExpression;
                    const sourcePath = Core.clone(endpointData.left.sourcePath);
                    const targetPath = Core.clone(endpointData.left.targetPath);
                    const pointBoundary = sourcePathExpression;
                    const sourceMethod = onePathRecursorMethodValue(
                        sourcePathExpression, pathMethodNames, computationName
                    );
                    const targetMethod = onePathRecursorMethodValue(
                        targetPathExpression, pathMethodNames, computationName
                    );
                    const argumentNames = path.argumentNames ?? [];
                    const argumentValues = argumentNames.map(wrapVar);
                    const pathIndex = threePathEntries.findIndex(entry => entry.name === path.name);
                    const methodValue = wrapApply(
                        wrapVar(threePathMethodNames[pathIndex]),
                        ...argumentValues.map(argument => Core.clone(argument))
                    );
                    const occupied = new Set([
                        ...prefixBinders.map(binder => binder.name),
                        ...argumentNames
                    ]);
                    const recursorHead = wrapApply(
                        wrapVar(recursorName),
                        ...prefixValues.map(value => Core.clone(value))
                    );
                    const pathComputation = (endpoint: EvaluatedOnePathExpression): AST => {
                        if (endpoint.kind === "atom") {
                            return wrapApply(
                                wrapVar(`${full ? "@" : ""}ap_${endpoint.path.name}`),
                                ...prefixValues.map(value => Core.clone(value)),
                                ...endpoint.arguments.map(argument => Core.clone(argument))
                            );
                        }
                        if (endpoint.kind === "compose") {
                            return wrapApply(
                                wrapVar("@hit_ap1_corrected_comp"),
                                Core.clone(hitUniverseLevel),
                                Core.clone(motiveUniverseLevel),
                                Core.clone(hitType),
                                wrapVar(motiveName),
                                Core.clone(endpoint.left.sourcePoint),
                                Core.clone(endpoint.left.targetPoint),
                                Core.clone(endpoint.right.targetPoint),
                                Core.clone(endpoint.left.term),
                                Core.clone(endpoint.right.term),
                                Core.clone(recursorHead),
                                onePathRecursorMethodValue(
                                    endpoint.left, pathMethodNames, computationName
                                ),
                                onePathRecursorMethodValue(
                                    endpoint.right, pathMethodNames, computationName
                                ),
                                pathComputation(endpoint.left),
                                pathComputation(endpoint.right)
                            );
                        }
                        return wrapApply(
                            wrapVar("@hit_ap1_corrected_inv"),
                            Core.clone(hitUniverseLevel),
                            Core.clone(motiveUniverseLevel),
                            Core.clone(hitType),
                            wrapVar(motiveName),
                            Core.clone(endpoint.value.sourcePoint),
                            Core.clone(endpoint.value.targetPoint),
                            Core.clone(endpoint.value.term),
                            Core.clone(recursorHead),
                            onePathRecursorMethodValue(
                                endpoint.value, pathMethodNames, computationName
                            ),
                            pathComputation(endpoint.value)
                        );
                    };
                    const actionType = (expression: EvaluatedTwoPathExpression) => strongEquality(
                        wrapApply(wrapVar("ap"), Core.clone(recursorHead), Core.clone(expression.sourcePath)),
                        wrapApply(wrapVar("ap"), Core.clone(recursorHead), Core.clone(expression.targetPath))
                    );
                    const recursorExpressionMethod = (
                        expression: EvaluatedTwoPathExpression
                    ): AST => {
                        if (expression.kind === "atom") {
                            const endpointIndex = twoPathEntries.findIndex(entry =>
                                entry.name === expression.path.name
                            );
                            if (endpointIndex < 0) {
                                throw new Error(`${computationName} 引用了未知二阶路径：${expression.path.name}`);
                            }
                            return wrapApply(
                                wrapVar(twoPathMethodNames[endpointIndex]),
                                ...expression.arguments.map(argument => Core.clone(argument))
                            );
                        }
                        if (expression.kind === "refl") {
                            return wrapApply(
                                wrapVar("refl"),
                                onePathRecursorMethodValue(
                                    expression.sourceExpression,
                                    pathMethodNames,
                                    computationName
                                )
                            );
                        }
                        if (expression.kind === "compose") {
                            return strongCompose(
                                recursorExpressionMethod(expression.left),
                                recursorExpressionMethod(expression.right)
                            );
                        }
                        return wrapApply(
                            wrapVar("inveq"),
                            recursorExpressionMethod(expression.value)
                        );
                    };
                    const strongExpressionComputation = (
                        expression: EvaluatedTwoPathExpression
                    ): {
                        sourceMethod: AST;
                        targetMethod: AST;
                        method: AST;
                        sourceComputation: AST;
                        targetComputation: AST;
                        proof: AST;
                    } => {
                        if (expression.kind === "atom") {
                            const sourceMethod = onePathRecursorMethodValue(
                                expression.sourceExpression, pathMethodNames, computationName
                            );
                            const targetMethod = onePathRecursorMethodValue(
                                expression.targetExpression, pathMethodNames, computationName
                            );
                            return {
                                sourceMethod,
                                targetMethod,
                                method: recursorExpressionMethod(expression),
                                sourceComputation: pathComputation(expression.sourceExpression),
                                targetComputation: pathComputation(expression.targetExpression),
                                proof: wrapApply(
                                    wrapVar(`${full ? "@" : ""}ap2_${expression.path.name}`),
                                    ...prefixValues.map(value => Core.clone(value)),
                                    ...expression.arguments.map(argument => Core.clone(argument))
                                )
                            };
                        }
                        if (expression.kind === "refl") {
                            const sourceMethod = onePathRecursorMethodValue(
                                expression.sourceExpression, pathMethodNames, computationName
                            );
                            const sourceComputation = pathComputation(expression.sourceExpression);
                            return {
                                sourceMethod,
                                targetMethod: Core.clone(sourceMethod),
                                method: wrapApply(wrapVar("refl"), Core.clone(sourceMethod)),
                                sourceComputation,
                                targetComputation: Core.clone(sourceComputation),
                                proof: wrapApply(
                                    wrapVar("@hit_ap2_corrected_refl"),
                                    Core.clone(hitUniverseLevel),
                                    Core.clone(motiveUniverseLevel),
                                    Core.clone(hitType),
                                    wrapVar(motiveName),
                                    Core.clone(pointBoundary.sourcePoint),
                                    Core.clone(pointBoundary.targetPoint),
                                    Core.clone(expression.sourcePath),
                                    Core.clone(recursorHead),
                                    Core.clone(sourceMethod),
                                    Core.clone(sourceComputation)
                                )
                            };
                        }
                        if (expression.kind === "compose") {
                            const left = strongExpressionComputation(expression.left);
                            const right = strongExpressionComputation(expression.right);
                            return {
                                sourceMethod: left.sourceMethod,
                                targetMethod: right.targetMethod,
                                method: strongCompose(left.method, right.method),
                                sourceComputation: left.sourceComputation,
                                targetComputation: right.targetComputation,
                                proof: wrapApply(
                                    wrapVar("@hit_ap2_corrected_comp"),
                                    Core.clone(hitUniverseLevel),
                                    Core.clone(motiveUniverseLevel),
                                    Core.clone(hitType),
                                    wrapVar(motiveName),
                                    Core.clone(pointBoundary.sourcePoint),
                                    Core.clone(pointBoundary.targetPoint),
                                    Core.clone(expression.left.sourcePath),
                                    Core.clone(expression.left.targetPath),
                                    Core.clone(expression.right.targetPath),
                                    Core.clone(recursorHead),
                                    Core.clone(left.sourceMethod),
                                    Core.clone(left.targetMethod),
                                    Core.clone(right.targetMethod),
                                    Core.clone(expression.left.term),
                                    Core.clone(expression.right.term),
                                    Core.clone(left.sourceComputation),
                                    Core.clone(left.targetComputation),
                                    Core.clone(right.targetComputation),
                                    Core.clone(left.method),
                                    Core.clone(right.method),
                                    Core.clone(left.proof),
                                    Core.clone(right.proof)
                                )
                            };
                        }
                        const value = strongExpressionComputation(expression.value);
                        return {
                            sourceMethod: value.targetMethod,
                            targetMethod: value.sourceMethod,
                            method: wrapApply(wrapVar("inveq"), Core.clone(value.method)),
                            sourceComputation: value.targetComputation,
                            targetComputation: value.sourceComputation,
                            proof: wrapApply(
                                wrapVar("@hit_ap2_corrected_inv"),
                                Core.clone(hitUniverseLevel),
                                Core.clone(motiveUniverseLevel),
                                Core.clone(hitType),
                                wrapVar(motiveName),
                                Core.clone(pointBoundary.sourcePoint),
                                Core.clone(pointBoundary.targetPoint),
                                Core.clone(expression.value.sourcePath),
                                Core.clone(expression.value.targetPath),
                                Core.clone(recursorHead),
                                Core.clone(value.sourceMethod),
                                Core.clone(value.targetMethod),
                                Core.clone(expression.value.term),
                                Core.clone(value.sourceComputation),
                                Core.clone(value.targetComputation),
                                Core.clone(value.method),
                                Core.clone(value.proof)
                            )
                        };
                    };
                    const leftExpression = strongExpressionComputation(endpointData.left);
                    const rightExpression = strongExpressionComputation(endpointData.right);
                    let methodName = "twoPathMethod";
                    while (occupied.has(methodName)) methodName += "_";
                    const correction = strongLambda(
                        methodName,
                        strongEquality(Core.clone(sourceMethod), Core.clone(targetMethod)),
                        strongCompose(
                            strongCompose(
                                pathComputation(sourcePathExpression), wrapVar(methodName)
                            ),
                            wrapApply(
                                wrapVar("inveq"), pathComputation(targetPathExpression)
                            )
                        )
                    );
                    const correctedMethod = strongCompose(
                        strongCompose(
                            leftExpression.proof,
                            wrapApply(wrapVar("ap"), correction, methodValue)
                        ),
                        wrapApply(wrapVar("inveq"), rightExpression.proof)
                    );
                    const pathTerm = wrapApply(
                        wrapVar(path.name),
                        ...parameters.map(parameter => wrapVar(parameter.name)),
                        ...argumentValues.map(argument => Core.clone(argument))
                    );
                    const action = wrapApply(wrapVar("ap3"), recursorHead, pathTerm);
                    const localBinders = argumentNames.map((name, index) => ({
                        name,
                        type: normalizedMetadataAst(path.argumentTypes[index])
                    }));
                    const expected = normalizedMetadataAst(strongWrapPis(
                        [...prefixBinders, ...localBinders],
                        strongEquality(action, correctedMethod)
                    ));
                    if (!sameGeneratedAstAlpha(actualComputationType, expected)) {
                        throw new Error(`三维 HIT action 计算定理 ${computationName} 与 metadata 不一致`);
                    }
                    canonicallyCertifiedTypeFormations.add(computationName);
                };

                const validateThreePathDependentComputation = (
                    path: CoreHitThreePathConstructorMetadata,
                    full: boolean
                ) => {
                    const eliminatorName = full
                        ? metadata.fullEliminatorName
                        : metadata.eliminatorName;
                    const eliminatorType = full
                        ? (metadata.fullEliminatorName
                            ? auxiliaryTypes.get(metadata.fullEliminatorName)
                            : undefined)
                        : bundle.eliminator?.[1] && normalizedMetadataAst(bundle.eliminator[1]);
                    const computationName = `${full ? "@" : ""}apd3_${path.name}`;
                    const actualComputationType = auxiliaryTypes.get(computationName);
                    if (!eliminatorName || !eliminatorType || !actualComputationType) {
                        throw new Error(`三维 HIT dependent 计算定理槽位不存在：${computationName}`);
                    }

                    const eliminatorBinders = readRecursorTelescope(
                        eliminatorType,
                        full ? "完整消去器" : "公开消去器"
                    );
                    const pathEntries = metadataPathEntries;
                    const twoPathEntries = metadataTwoPathEntries;
                    const threePathEntries = metadataThreePathEntries;
                    let offset = full ? 1 : 0;
                    offset += parameters.length;
                    const motiveName = eliminatorBinders[offset++].name;
                    const branchNames = eliminatorBinders
                        .slice(offset, offset + metadata.constructors.length)
                        .map(binder => binder.name);
                    offset += metadata.constructors.length;
                    const pathMethodNames = eliminatorBinders
                        .slice(offset, offset + pathEntries.length)
                        .map(binder => binder.name);
                    offset += pathEntries.length;
                    const twoPathMethodNames = eliminatorBinders
                        .slice(offset, offset + twoPathEntries.length)
                        .map(binder => binder.name);
                    offset += twoPathEntries.length;
                    const threePathMethodNames = eliminatorBinders
                        .slice(offset, offset + threePathEntries.length)
                        .map(binder => binder.name);
                    offset += threePathEntries.length;
                    if (eliminatorBinders.length !== offset + 1) {
                        throw new Error("三维 HIT 消去器 telescope 与 dependent 计算 metadata 不一致");
                    }

                    const prefixBinders = eliminatorBinders.slice(0, offset);
                    const prefixValues = prefixBinders.map(binder => wrapVar(binder.name));
                    let familyUniverse = normalizedMetadataAst(bundle.type[1]);
                    for (let index = 0; index < parameters.length; index++) {
                        if (familyUniverse.type !== "P" || !familyUniverse.nodes?.[1]) {
                            throw new Error(`三维 HIT ${metadata.typeName} 的 Universe telescope 不完整`);
                        }
                        familyUniverse = familyUniverse.nodes[1];
                    }
                    if (familyUniverse.type !== "apply"
                        || familyUniverse.nodes?.[0]?.type !== "var"
                        || familyUniverse.nodes[0].name !== "U"
                        || !familyUniverse.nodes[1]) {
                        throw new Error(`三维 HIT ${metadata.typeName} 的 Universe 缺少显式层级`);
                    }
                    const hitUniverseLevel = Core.clone(familyUniverse.nodes[1]);
                    const motiveUniverseLevel = full
                        ? Core.clone(prefixValues[0])
                        : wrapVar("@0");
                    const hitType = wrapApply(
                        wrapVar(metadata.typeName),
                        ...parameters.map(parameter => wrapVar(parameter.name))
                    );
                    const argumentNames = path.argumentNames ?? [];
                    const argumentValues = argumentNames.map(wrapVar);
                    const localBinders = argumentNames.map((name, index) => ({
                        name,
                        type: normalizedMetadataAst(path.argumentTypes[index])
                    }));
                    const pathTerm = wrapApply(
                        wrapVar(path.name),
                        ...parameters.map(parameter => wrapVar(parameter.name)),
                        ...argumentValues.map(argument => Core.clone(argument))
                    );
                    const dependentHead = wrapApply(
                        wrapVar(eliminatorName),
                        ...prefixValues.map(value => Core.clone(value))
                    );

                    const pointBranchValue = (endpoint: AST) => hitBranchValue(
                        endpoint,
                        branchNames,
                        computationName
                    );
                    const pathData = (endpoint: EvaluatedOnePathExpression) => {
                        const pathTermValue = Core.clone(endpoint.term);
                        const leftBranch = pointBranchValue(endpoint.sourcePoint);
                        const rightBranch = pointBranchValue(endpoint.targetPoint);
                        return {
                            pathTerm: pathTermValue,
                            type: strongEquality(
                                wrapApply(
                                    wrapVar("trans"),
                                    wrapVar(motiveName),
                                    Core.clone(pathTermValue),
                                    leftBranch
                                ),
                                rightBranch
                            ),
                            sourcePoint: Core.clone(endpoint.sourcePoint),
                            targetPoint: Core.clone(endpoint.targetPoint),
                            sourceValue: leftBranch,
                            targetValue: rightBranch,
                            method: onePathDependentMethodValue(
                                endpoint,
                                motiveName,
                                branchNames,
                                pathMethodNames,
                                computationName
                            )
                        };
                    };
                    const endpointData = evaluatedThreePathEndpoints.get(path.name);
                    if (!endpointData) {
                        throw new Error(`${computationName} 缺少已认证的表达式端点`);
                    }
                    const sourcePathExpression = endpointData.left.sourceExpression;
                    const targetPathExpression = endpointData.left.targetExpression;
                    const sourcePath = Core.clone(endpointData.left.sourcePath);
                    const targetPath = Core.clone(endpointData.left.targetPath);
                    const sourcePathData = pathData(sourcePathExpression);
                    const targetPathData = pathData(targetPathExpression);
                    const sourceMethod = sourcePathData.method;
                    const targetMethod = targetPathData.method;
                    const sourceValue = sourcePathData.sourceValue;
                    const targetValue = sourcePathData.targetValue;
                    const pathComputation = (endpoint: EvaluatedOnePathExpression): AST => {
                        if (endpoint.kind === "atom") {
                            return wrapApply(
                                wrapVar(`${full ? "@" : ""}apd_${endpoint.path.name}`),
                                ...prefixValues.map(value => Core.clone(value)),
                                ...endpoint.arguments.map(argument => Core.clone(argument))
                            );
                        }
                        if (endpoint.kind === "compose") {
                            return wrapApply(
                                wrapVar("@hit_apd1_corrected_comp"),
                                Core.clone(hitUniverseLevel),
                                Core.clone(motiveUniverseLevel),
                                Core.clone(hitType),
                                Core.clone(endpoint.left.sourcePoint),
                                Core.clone(endpoint.left.targetPoint),
                                Core.clone(endpoint.right.targetPoint),
                                Core.clone(endpoint.left.term),
                                Core.clone(endpoint.right.term),
                                wrapVar(motiveName),
                                Core.clone(dependentHead),
                                onePathDependentMethodValue(
                                    endpoint.left,
                                    motiveName,
                                    branchNames,
                                    pathMethodNames,
                                    computationName
                                ),
                                onePathDependentMethodValue(
                                    endpoint.right,
                                    motiveName,
                                    branchNames,
                                    pathMethodNames,
                                    computationName
                                ),
                                pathComputation(endpoint.left),
                                pathComputation(endpoint.right)
                            );
                        }
                        return wrapApply(
                            wrapVar("@hit_apd1_corrected_inv"),
                            Core.clone(hitUniverseLevel),
                            Core.clone(motiveUniverseLevel),
                            Core.clone(hitType),
                            Core.clone(endpoint.value.sourcePoint),
                            Core.clone(endpoint.value.targetPoint),
                            Core.clone(endpoint.value.term),
                            wrapVar(motiveName),
                            Core.clone(dependentHead),
                            onePathDependentMethodValue(
                                endpoint.value,
                                motiveName,
                                branchNames,
                                pathMethodNames,
                                computationName
                            ),
                            pathComputation(endpoint.value)
                        );
                    };
                    const sourceComputation = pathComputation(sourcePathExpression);
                    const targetComputation = pathComputation(targetPathExpression);
                    const dependentExpressionMethod = (
                        expression: EvaluatedTwoPathExpression
                    ): { sourceMethod: AST; targetMethod: AST; proof: AST } => {
                        if (expression.kind === "atom") {
                            const endpointIndex = twoPathEntries.findIndex(entry =>
                                entry.name === expression.path.name
                            );
                            if (endpointIndex < 0) {
                                throw new Error(
                                    `${computationName} 引用了未知二阶路径：${expression.path.name}`
                                );
                            }
                            return {
                                sourceMethod: onePathDependentMethodValue(
                                    expression.sourceExpression,
                                    motiveName,
                                    branchNames,
                                    pathMethodNames,
                                    computationName
                                ),
                                targetMethod: onePathDependentMethodValue(
                                    expression.targetExpression,
                                    motiveName,
                                    branchNames,
                                    pathMethodNames,
                                    computationName
                                ),
                                proof: wrapApply(
                                    wrapVar(twoPathMethodNames[endpointIndex]),
                                    ...expression.arguments.map(argument => Core.clone(argument))
                                )
                            };
                        }
                        if (expression.kind === "refl") {
                            const sourceMethod = onePathDependentMethodValue(
                                expression.sourceExpression,
                                motiveName,
                                branchNames,
                                pathMethodNames,
                                computationName
                            );
                            return {
                                sourceMethod,
                                targetMethod: Core.clone(sourceMethod),
                                proof: wrapApply(wrapVar("refl"), Core.clone(sourceMethod))
                            };
                        }
                        if (expression.kind === "compose") {
                            const left = dependentExpressionMethod(expression.left);
                            const right = dependentExpressionMethod(expression.right);
                            return {
                                sourceMethod: left.sourceMethod,
                                targetMethod: right.targetMethod,
                                proof: wrapApply(
                                    wrapVar("hit_dep2_comp"),
                                    wrapVar(motiveName),
                                    Core.clone(sourceValue),
                                    Core.clone(targetValue),
                                    Core.clone(left.sourceMethod),
                                    Core.clone(left.targetMethod),
                                    Core.clone(right.targetMethod),
                                    Core.clone(expression.left.term),
                                    Core.clone(expression.right.term),
                                    Core.clone(left.proof),
                                    Core.clone(right.proof)
                                )
                            };
                        }
                        const value = dependentExpressionMethod(expression.value);
                        return {
                            sourceMethod: value.targetMethod,
                            targetMethod: value.sourceMethod,
                            proof: wrapApply(
                                wrapVar("hit_dep2_inv"),
                                wrapVar(motiveName),
                                Core.clone(sourceValue),
                                Core.clone(targetValue),
                                Core.clone(value.sourceMethod),
                                Core.clone(value.targetMethod),
                                Core.clone(expression.value.term),
                                Core.clone(value.proof)
                            )
                        };
                    };
                    const dependentExpressionComputation = (
                        expression: EvaluatedTwoPathExpression
                    ): {
                        sourcePath: AST;
                        targetPath: AST;
                        sourceMethod: AST;
                        targetMethod: AST;
                        method: AST;
                        sourceComputation: AST;
                        targetComputation: AST;
                        proof: AST;
                    } => {
                        if (expression.kind === "atom") {
                            const method = dependentExpressionMethod(expression);
                            return {
                                sourcePath: Core.clone(expression.sourcePath),
                                targetPath: Core.clone(expression.targetPath),
                                sourceMethod: method.sourceMethod,
                                targetMethod: method.targetMethod,
                                method: method.proof,
                                sourceComputation: pathComputation(expression.sourceExpression),
                                targetComputation: pathComputation(expression.targetExpression),
                                proof: wrapApply(
                                    wrapVar(`${full ? "@" : ""}apd_${expression.path.name}`),
                                    ...prefixValues.map(value => Core.clone(value)),
                                    ...expression.arguments.map(argument => Core.clone(argument))
                                )
                            };
                        }
                        if (expression.kind === "refl") {
                            const sourceMethod = onePathDependentMethodValue(
                                expression.sourceExpression,
                                motiveName,
                                branchNames,
                                pathMethodNames,
                                computationName
                            );
                            const sourceComputation = pathComputation(expression.sourceExpression);
                            return {
                                sourcePath: Core.clone(expression.sourcePath),
                                targetPath: Core.clone(expression.sourcePath),
                                sourceMethod,
                                targetMethod: Core.clone(sourceMethod),
                                method: wrapApply(wrapVar("refl"), Core.clone(sourceMethod)),
                                sourceComputation,
                                targetComputation: Core.clone(sourceComputation),
                                proof: wrapApply(
                                    wrapVar("@hit_apd2_corrected_refl"),
                                    Core.clone(hitUniverseLevel),
                                    Core.clone(motiveUniverseLevel),
                                    Core.clone(hitType),
                                    Core.clone(sourcePathData.sourcePoint),
                                    Core.clone(sourcePathData.targetPoint),
                                    Core.clone(expression.sourcePath),
                                    wrapVar(motiveName),
                                    Core.clone(dependentHead),
                                    Core.clone(sourceMethod),
                                    Core.clone(sourceComputation)
                                )
                            };
                        }
                        if (expression.kind === "compose") {
                            const left = dependentExpressionComputation(expression.left);
                            const right = dependentExpressionComputation(expression.right);
                            const method = wrapApply(
                                wrapVar("hit_dep2_comp"),
                                wrapVar(motiveName),
                                Core.clone(sourceValue),
                                Core.clone(targetValue),
                                Core.clone(left.sourceMethod),
                                Core.clone(left.targetMethod),
                                Core.clone(right.targetMethod),
                                Core.clone(expression.left.term),
                                Core.clone(expression.right.term),
                                Core.clone(left.method),
                                Core.clone(right.method)
                            );
                            return {
                                sourcePath: left.sourcePath,
                                targetPath: right.targetPath,
                                sourceMethod: left.sourceMethod,
                                targetMethod: right.targetMethod,
                                method,
                                sourceComputation: left.sourceComputation,
                                targetComputation: right.targetComputation,
                                proof: wrapApply(
                                    wrapVar("@hit_apd2_corrected_comp"),
                                    Core.clone(hitUniverseLevel),
                                    Core.clone(motiveUniverseLevel),
                                    Core.clone(hitType),
                                    Core.clone(sourcePathData.sourcePoint),
                                    Core.clone(sourcePathData.targetPoint),
                                    Core.clone(left.sourcePath),
                                    Core.clone(left.targetPath),
                                    Core.clone(right.targetPath),
                                    wrapVar(motiveName),
                                    Core.clone(dependentHead),
                                    Core.clone(left.sourceMethod),
                                    Core.clone(left.targetMethod),
                                    Core.clone(right.targetMethod),
                                    Core.clone(expression.left.term),
                                    Core.clone(expression.right.term),
                                    Core.clone(left.sourceComputation),
                                    Core.clone(left.targetComputation),
                                    Core.clone(right.targetComputation),
                                    Core.clone(left.method),
                                    Core.clone(right.method),
                                    Core.clone(left.proof),
                                    Core.clone(right.proof)
                                )
                            };
                        }
                        const value = dependentExpressionComputation(expression.value);
                        const method = wrapApply(
                            wrapVar("hit_dep2_inv"),
                            wrapVar(motiveName),
                            Core.clone(sourceValue),
                            Core.clone(targetValue),
                            Core.clone(value.sourceMethod),
                            Core.clone(value.targetMethod),
                            Core.clone(expression.value.term),
                            Core.clone(value.method)
                        );
                        return {
                            sourcePath: value.targetPath,
                            targetPath: value.sourcePath,
                            sourceMethod: value.targetMethod,
                            targetMethod: value.sourceMethod,
                            method,
                            sourceComputation: value.targetComputation,
                            targetComputation: value.sourceComputation,
                            proof: wrapApply(
                                wrapVar("@hit_apd2_corrected_inv"),
                                Core.clone(hitUniverseLevel),
                                Core.clone(motiveUniverseLevel),
                                Core.clone(hitType),
                                Core.clone(sourcePathData.sourcePoint),
                                Core.clone(sourcePathData.targetPoint),
                                Core.clone(value.sourcePath),
                                Core.clone(value.targetPath),
                                wrapVar(motiveName),
                                Core.clone(dependentHead),
                                Core.clone(value.sourceMethod),
                                Core.clone(value.targetMethod),
                                Core.clone(expression.value.term),
                                Core.clone(value.sourceComputation),
                                Core.clone(value.targetComputation),
                                Core.clone(value.method),
                                Core.clone(value.proof)
                            )
                        };
                    };
                    const leftExpressionMethod = dependentExpressionMethod(endpointData.left);
                    const rightExpressionMethod = dependentExpressionMethod(endpointData.right);
                    const leftComputation = dependentExpressionComputation(endpointData.left).proof;
                    const rightComputation = dependentExpressionComputation(endpointData.right).proof;
                    const leftMethod = leftExpressionMethod.proof;
                    const rightMethod = rightExpressionMethod.proof;
                    const leftTwoPath = Core.clone(endpointData.left.term);
                    const rightTwoPath = Core.clone(endpointData.right.term);
                    const pathIndex = threePathEntries.findIndex(entry => entry.name === path.name);
                    const methodValue = wrapApply(
                        wrapVar(threePathMethodNames[pathIndex]),
                        ...argumentValues.map(argument => Core.clone(argument))
                    );
                    const endpointValue = Core.clone(sourceValue);
                    const twoPathDomain = strongEquality(
                        Core.clone(sourcePath),
                        Core.clone(targetPath)
                    );

                    const occupied = new Set([
                        ...prefixBinders.map(binder => binder.name),
                        ...argumentNames
                    ]);
                    const freshName = (base: string) => {
                        let result = base;
                        while (occupied.has(result)) result += "_";
                        occupied.add(result);
                        return result;
                    };
                    const twoPathName = freshName("dependentTwoPathValue");
                    const methodName = freshName("dependentTwoPathMethod");
                    const targetValueName = freshName("dependentTargetPathValue");
                    const correctedValueName = freshName("dependentCorrectedValue");
                    const rawFamily = (twoPathValue: AST) => strongEquality(
                        Core.clone(sourceMethod),
                        strongCompose(
                            wrapApply(
                                wrapVar("trans2"),
                                wrapVar(motiveName),
                                twoPathValue,
                                Core.clone(endpointValue)
                            ),
                            Core.clone(targetMethod)
                        )
                    );
                    const actualFamily = (twoPathValue: AST) => strongEquality(
                        wrapApply(
                            wrapVar("apd"),
                            Core.clone(dependentHead),
                            Core.clone(sourcePath)
                        ),
                        strongCompose(
                            wrapApply(
                                wrapVar("trans2"),
                                wrapVar(motiveName),
                                twoPathValue,
                                Core.clone(endpointValue)
                            ),
                            wrapApply(
                                wrapVar("apd"),
                                Core.clone(dependentHead),
                                Core.clone(targetPath)
                            )
                        )
                    );
                    const correction = strongLambda(
                        twoPathName,
                        Core.clone(twoPathDomain),
                        strongLambda(
                            methodName,
                            rawFamily(wrapVar(twoPathName)),
                            strongCompose(
                                strongCompose(
                                    Core.clone(sourceComputation),
                                    wrapVar(methodName)
                                ),
                                wrapApply(
                                    wrapVar("inveq"),
                                    wrapApply(
                                        wrapVar("ap"),
                                        strongLambda(
                                            targetValueName,
                                            Core.clone(targetPathData.type),
                                            strongCompose(
                                                wrapApply(
                                                    wrapVar("trans2"),
                                                    wrapVar(motiveName),
                                                    wrapVar(twoPathName),
                                                    Core.clone(endpointValue)
                                                ),
                                                wrapVar(targetValueName)
                                            )
                                        ),
                                        Core.clone(targetComputation)
                                    )
                                )
                            )
                        )
                    );
                    const mappedMethod = wrapApply(
                        wrapVar("hit_map_transport"),
                        correction,
                        Core.clone(leftTwoPath),
                        Core.clone(rightTwoPath),
                        Core.clone(pathTerm),
                        Core.clone(leftMethod),
                        Core.clone(rightMethod),
                        Core.clone(methodValue)
                    );
                    const actualFamilyLambda = strongLambda(
                        twoPathName,
                        Core.clone(twoPathDomain),
                        actualFamily(wrapVar(twoPathName))
                    );
                    const transportedComputation = wrapApply(
                        wrapVar("ap"),
                        strongLambda(
                            correctedValueName,
                            actualFamily(Core.clone(leftTwoPath)),
                            wrapApply(
                                wrapVar("trans"),
                                Core.clone(actualFamilyLambda),
                                Core.clone(pathTerm),
                                wrapVar(correctedValueName)
                            )
                        ),
                        Core.clone(leftComputation)
                    );
                    const correctedMethod = strongCompose(
                        strongCompose(transportedComputation, mappedMethod),
                        wrapApply(wrapVar("inveq"), Core.clone(rightComputation))
                    );
                    const action = wrapApply(
                        wrapVar("apd3"),
                        Core.clone(dependentHead),
                        Core.clone(pathTerm)
                    );
                    const expected = normalizedMetadataAst(strongWrapPis(
                        [...prefixBinders, ...localBinders],
                        strongEquality(action, correctedMethod)
                    ));
                    if (!sameGeneratedAstAlpha(actualComputationType, expected)) {
                        throw new Error(
                            `三维 HIT dependent 计算定理 ${computationName} 与 metadata 不一致`
                        );
                    }
                    canonicallyCertifiedTypeFormations.add(computationName);
                };

                for (const path of metadataThreePathEntries) {
                    validateThreePathDependentComputation(path, false);
                    validateThreePathDependentComputation(path, true);
                    validateThreePathActionComputation(path, false);
                    validateThreePathActionComputation(path, true);
                }
            }

            if (metadata.kind === "hit3") {
                const readTelescope = (source: AST, label: string) => {
                    const binders: { name: string; type: AST }[] = [];
                    let cursor = source;
                    while ((cursor.type === "P" || cursor.type === "->")
                        && cursor.nodes?.[0] && cursor.nodes?.[1]) {
                        binders.push({
                            name: cursor.type === "P" ? cursor.name : "",
                            type: Core.clone(cursor.nodes[0])
                        });
                        cursor = cursor.nodes[1];
                    }
                    if (!binders.length) throw new Error(`${label} telescope 不完整`);
                    return binders;
                };
                const surfaceEquality = (left: AST, right: AST): AST => ({
                    type: "=",
                    name: "",
                    nodes: [left, right]
                });
                const surfaceCompose = (left: AST, right: AST): AST => ({
                    type: "*",
                    name: "",
                    nodes: [left, right]
                });
                const surfaceLambda = (name: string, type: AST, body: AST): AST => ({
                    type: "L",
                    name,
                    nodes: [type, body]
                });
                const surfaceWrapPis = (
                    names: readonly string[],
                    types: readonly AST[],
                    body: AST
                ) => {
                    let result = body;
                    for (let index = names.length - 1; index >= 0; index--) {
                        result = {
                            type: "P",
                            name: names[index],
                            nodes: [Core.clone(types[index]), result]
                        };
                    }
                    return result;
                };
                const branchValue = (
                    point: AST,
                    branchNames: readonly string[],
                    label: string
                ) => hitBranchValue(point, branchNames, label);
                const validateThreeCoherenceTelescope = (
                    source: AST,
                    full: boolean,
                    dependent: boolean,
                    label: string
                ) => {
                    const binders = readTelescope(source, label);
                    const pathEntries = metadataPathEntries;
                    const twoPathEntries = metadataTwoPathEntries;
                    const threePathEntries = metadataThreePathEntries;
                    const expectedCount = (full ? 1 : 0)
                        + parameters.length
                        + 1
                        + metadata.constructors.length
                        + pathEntries.length
                        + twoPathEntries.length
                        + threePathEntries.length
                        + 1;
                    if (binders.length !== expectedCount) {
                        throw new Error(`${label} telescope 长度与三维 metadata 不一致`);
                    }
                    let offset = full ? 1 : 0;
                    offset += parameters.length;
                    const motiveName = binders[offset++].name;
                    const branchNames = binders
                        .slice(offset, offset + metadata.constructors.length)
                        .map(binder => binder.name);
                    offset += metadata.constructors.length;
                    const pathMethodNames = binders
                        .slice(offset, offset + pathEntries.length)
                        .map(binder => binder.name);
                    offset += pathEntries.length;
                    const twoPathMethodNames = binders
                        .slice(offset, offset + twoPathEntries.length)
                        .map(binder => binder.name);
                    offset += twoPathEntries.length;

                    for (let index = 0; index < threePathEntries.length; index++) {
                        const path = threePathEntries[index];
                        const argumentNames = path.argumentNames ?? [];
                        const argumentTypes = path.argumentTypes.map(normalizedMetadataAst);
                        const endpointData = evaluatedThreePathEndpoints.get(path.name);
                        if (!endpointData) {
                            throw new Error(`${label} ${path.name} 缺少已认证的表达式端点`);
                        }
                        const recursorExpressionMethod = (
                            expression: EvaluatedTwoPathExpression
                        ): AST => {
                            if (expression.kind === "atom") {
                                const endpointIndex = twoPathEntries.findIndex(entry =>
                                    entry.name === expression.path.name
                                );
                                if (endpointIndex < 0) {
                                    throw new Error(
                                        `${label} ${path.name} 引用了未知二阶路径：${expression.path.name}`
                                    );
                                }
                                return wrapApply(
                                    wrapVar(twoPathMethodNames[endpointIndex]),
                                    ...expression.arguments.map(argument => Core.clone(argument))
                                );
                            }
                            if (expression.kind === "refl") {
                                return wrapApply(
                                    wrapVar("refl"),
                                    onePathRecursorMethodValue(
                                        expression.sourceExpression,
                                        pathMethodNames,
                                        `${label} ${path.name}`
                                    )
                                );
                            }
                            if (expression.kind === "compose") {
                                return surfaceCompose(
                                    recursorExpressionMethod(expression.left),
                                    recursorExpressionMethod(expression.right)
                                );
                            }
                            return wrapApply(
                                wrapVar("inveq"),
                                recursorExpressionMethod(expression.value)
                            );
                        };
                        let expectedBody: AST;
                        if (dependent) {
                            const sourcePathExpression = endpointData.left.sourceExpression;
                            const targetPathExpression = endpointData.left.targetExpression;
                            const sourcePath = Core.clone(endpointData.left.sourcePath);
                            const targetPath = Core.clone(endpointData.left.targetPath);
                            const sourceMethod = onePathDependentMethodValue(
                                sourcePathExpression,
                                motiveName,
                                branchNames,
                                pathMethodNames,
                                `${label} ${path.name}`
                            );
                            const targetMethod = onePathDependentMethodValue(
                                targetPathExpression,
                                motiveName,
                                branchNames,
                                pathMethodNames,
                                `${label} ${path.name}`
                            );
                            const pointValue = branchValue(
                                sourcePathExpression.sourcePoint,
                                branchNames,
                                `${label} ${path.name}`
                            );
                            const targetPointValue = branchValue(
                                sourcePathExpression.targetPoint,
                                branchNames,
                                `${label} ${path.name}`
                            );
                            const dependentExpressionMethod = (
                                expression: EvaluatedTwoPathExpression
                            ): { sourceMethod: AST; targetMethod: AST; proof: AST } => {
                                if (expression.kind === "atom") {
                                    const endpointIndex = twoPathEntries.findIndex(entry =>
                                        entry.name === expression.path.name
                                    );
                                    if (endpointIndex < 0) {
                                        throw new Error(
                                            `${label} ${path.name} 引用了未知二阶路径：`
                                            + expression.path.name
                                        );
                                    }
                                    return {
                                        sourceMethod: onePathDependentMethodValue(
                                            expression.sourceExpression,
                                            motiveName,
                                            branchNames,
                                            pathMethodNames,
                                            `${label} ${path.name}`
                                        ),
                                        targetMethod: onePathDependentMethodValue(
                                            expression.targetExpression,
                                            motiveName,
                                            branchNames,
                                            pathMethodNames,
                                            `${label} ${path.name}`
                                        ),
                                        proof: wrapApply(
                                            wrapVar(twoPathMethodNames[endpointIndex]),
                                            ...expression.arguments.map(argument => Core.clone(argument))
                                        )
                                    };
                                }
                                if (expression.kind === "refl") {
                                    const sourceMethod = onePathDependentMethodValue(
                                        expression.sourceExpression,
                                        motiveName,
                                        branchNames,
                                        pathMethodNames,
                                        `${label} ${path.name}`
                                    );
                                    return {
                                        sourceMethod,
                                        targetMethod: Core.clone(sourceMethod),
                                        proof: wrapApply(wrapVar("refl"), Core.clone(sourceMethod))
                                    };
                                }
                                if (expression.kind === "compose") {
                                    const left = dependentExpressionMethod(expression.left);
                                    const right = dependentExpressionMethod(expression.right);
                                    return {
                                        sourceMethod: left.sourceMethod,
                                        targetMethod: right.targetMethod,
                                        proof: wrapApply(
                                            wrapVar("hit_dep2_comp"),
                                            wrapVar(motiveName),
                                            Core.clone(pointValue),
                                            Core.clone(targetPointValue),
                                            Core.clone(left.sourceMethod),
                                            Core.clone(left.targetMethod),
                                            Core.clone(right.targetMethod),
                                            Core.clone(expression.left.term),
                                            Core.clone(expression.right.term),
                                            Core.clone(left.proof),
                                            Core.clone(right.proof)
                                        )
                                    };
                                }
                                const value = dependentExpressionMethod(expression.value);
                                return {
                                    sourceMethod: value.targetMethod,
                                    targetMethod: value.sourceMethod,
                                    proof: wrapApply(
                                        wrapVar("hit_dep2_inv"),
                                        wrapVar(motiveName),
                                        Core.clone(pointValue),
                                        Core.clone(targetPointValue),
                                        Core.clone(value.sourceMethod),
                                        Core.clone(value.targetMethod),
                                        Core.clone(expression.value.term),
                                        Core.clone(value.proof)
                                    )
                                };
                            };
                            const leftMethod = dependentExpressionMethod(endpointData.left).proof;
                            const rightMethod = dependentExpressionMethod(endpointData.right).proof;
                            const occupied = new Set([
                                ...binders.slice(0, offset).map(binder => binder.name),
                                ...argumentNames
                            ]);
                            let pathValueName = "twoPathValue";
                            while (occupied.has(pathValueName)) pathValueName += "_";
                            const pathValue = wrapVar(pathValueName);
                            const family = surfaceLambda(
                                pathValueName,
                                surfaceEquality(Core.clone(sourcePath), Core.clone(targetPath)),
                                surfaceEquality(
                                    sourceMethod,
                                    surfaceCompose(
                                        wrapApply(
                                            wrapVar("trans2"),
                                            wrapVar(motiveName),
                                            pathValue,
                                            pointValue
                                        ),
                                        targetMethod
                                    )
                                )
                            );
                            const pathTerm = wrapApply(
                                wrapVar(path.name),
                                ...parameters.map(parameter => wrapVar(parameter.name)),
                                ...argumentNames.map(wrapVar)
                            );
                            expectedBody = surfaceEquality(
                                wrapApply(wrapVar("trans"), family, pathTerm, leftMethod),
                                rightMethod
                            );
                        } else {
                            const leftMethod = recursorExpressionMethod(endpointData.left);
                            const rightMethod = recursorExpressionMethod(endpointData.right);
                            expectedBody = surfaceEquality(leftMethod, rightMethod);
                        }
                        const expected = normalizedMetadataAst(surfaceWrapPis(
                            argumentNames,
                            argumentTypes,
                            expectedBody
                        ));
                        const actual = binders[offset + index]?.type;
                        if (!actual || !sameGeneratedAstAlpha(actual, expected)) {
                            throw new Error(`${label} 三阶 coherence ${path.name} 与 metadata 不一致`);
                        }
                    }
                };

                const publicEliminatorType = bundle.eliminator?.[1];
                const fullEliminatorType = metadata.fullEliminatorName
                    ? auxiliaryTypes.get(metadata.fullEliminatorName)
                    : undefined;
                const publicRecursorType = bundle.recursor?.[1];
                const fullRecursorType = metadata.fullRecursorName
                    ? auxiliaryTypes.get(metadata.fullRecursorName)
                    : undefined;
                if (!publicEliminatorType || !fullEliminatorType
                    || !publicRecursorType || !fullRecursorType) {
                    throw new Error("三维 HIT 消去器/递归器槽位不完整");
                }
                validateThreeCoherenceTelescope(
                    normalizedMetadataAst(publicEliminatorType), false, true, "公开消去器"
                );
                validateThreeCoherenceTelescope(
                    fullEliminatorType, true, true, "完整消去器"
                );
                validateThreeCoherenceTelescope(
                    normalizedMetadataAst(publicRecursorType), false, false, "公开递归器"
                );
                validateThreeCoherenceTelescope(
                    fullRecursorType, true, false, "完整递归器"
                );
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
        const strictRuleSchema = bundle.metadata?.ruleSchemaVersion === 1;
        const deferredComputationTypes = new Set<string>();
        if (strictRuleSchema) {
            for (const path of flattenHitPathLevels(
                hitPathLevelsFromCanonicalOrLegacy(bundle.metadata ?? {})
            )) {
                for (const name of [
                    path.computationName,
                    `apd_${path.name}`,
                    `@apd_${path.name}`,
                    `ap_${path.name}`,
                    `@ap_${path.name}`,
                    `ap2_${path.name}`,
                    `@ap2_${path.name}`,
                    `apd3_${path.name}`,
                    `@apd3_${path.name}`,
                    `ap3_${path.name}`,
                    `@ap3_${path.name}`
                ]) {
                    if (name) deferredComputationTypes.add(name);
                }
            }
        }
        const publishComputeRules = () => {
            for (const [head, rules] of Object.entries(normalizedRules)) {
                this.state.computeRules[head] = [
                    ...(this.state.computeRules[head] ?? []),
                    ...rules
                ];
            }
            this.syncSemanticComputeRules();
        };
        try {
            for (const [name, type] of normalizedEntries) this.state.sysTypes[name] = type;
            for (const [name, definition] of normalizedDefinitions) this.state.sysDefs[name] = definition;
            this.syncSemanticDefinitions();
            // Schema-v1 rules have already been reconstructed canonically.
            // Check the family, constructors, eliminators, and path constants
            // before publishing them. Path computation propositions are the
            // only deferred entries: their types intentionally reduce a point
            // eliminator application and therefore need the certified rules.
            if (!strictRuleSchema) publishComputeRules();
            for (const [name, type] of normalizedEntries) {
                if (deferredComputationTypes.has(name)) continue;
                this.checkTypeFormation(type, []);
            }
            if (strictRuleSchema) {
                this.validateCanonicalInductiveRuleTypes(
                    bundle,
                    normalizedEntries,
                    normalizedRules,
                    parameters,
                    indexCount
                );
                publishComputeRules();
            }
            for (const [name, type] of normalizedEntries) {
                if (!deferredComputationTypes.has(name)) continue;
                this.checkTypeFormation(
                    type,
                    [],
                    canonicallyCertifiedTypeFormations.has(name)
                        ? certifiedPath3ComputationResourceLimits
                        : undefined
                );
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
        const clonedHitPaths = bundle.metadata
            && (bundle.metadata.kind === "hit1"
                || bundle.metadata.kind === "hit2"
                || bundle.metadata.kind === "hit3")
            ? cloneCoreHitPathMetadata(bundle.metadata)
            : undefined;
        const metadata = bundle.metadata
            ? {
                version: bundle.metadata.version,
                kind: bundle.metadata.kind,
                dimension: bundle.metadata.dimension,
                ruleSchemaVersion: bundle.metadata.ruleSchemaVersion,
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
                    argumentNames: ctor.argumentNames ? [...ctor.argumentNames] : undefined,
                    recursiveArguments: ctor.recursiveArguments?.map(argument => ({
                        index: argument.index,
                        telescope: argument.telescope.map(binder => ({
                            name: binder.name,
                            type: Core.clone(binder.type)
                        })),
                        resultIndices: argument.resultIndices.map(index => Core.clone(index))
                    })),
                    resultIndices: ctor.resultIndices?.map(index => Core.clone(index))
                })),
                ...(clonedHitPaths ?? {})
            }
            : undefined;
        this.registeredSystemInductives.set(registrationName, {
            names: [...names],
            previousTypes,
            previousDefinitions,
            previousRules,
            certifiedLargeSystemTypes: [...canonicallyCertifiedTypeFormations],
            metadata
        });
        for (const name of canonicallyCertifiedTypeFormations) {
            this.certifiedLargeSystemTypes.add(name);
        }
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
            for (const name of registration.certifiedLargeSystemTypes) {
                this.certifiedLargeSystemTypes.delete(name);
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
        const clonedHitPaths = metadata.kind === "hit1"
            || metadata.kind === "hit2"
            || metadata.kind === "hit3"
            ? cloneCoreHitPathMetadata(metadata)
            : undefined;
        return {
            version: metadata.version,
            kind: metadata.kind,
            dimension: metadata.dimension,
            ruleSchemaVersion: metadata.ruleSchemaVersion,
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
                argumentNames: ctor.argumentNames ? [...ctor.argumentNames] : undefined,
                recursiveArguments: ctor.recursiveArguments?.map(argument => ({
                    index: argument.index,
                    telescope: argument.telescope.map(binder => ({
                        name: binder.name,
                        type: Core.clone(binder.type)
                    })),
                    resultIndices: argument.resultIndices.map(index => Core.clone(index))
                })),
                resultIndices: ctor.resultIndices?.map(index => Core.clone(index))
            })),
            ...(clonedHitPaths ?? {})
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
            this.restoreCheckedDefinitionCache(name, this.createSemanticDefinitionCacheSnapshot(
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
        const restored = isSemanticDefinitionCacheSnapshot(cache)
            ? cloneSemanticDefinitionCache(cache)
            : migrateLegacyDefinitionCache(cache);
        if (!restored || !this.semanticTypeChecker.setConstantSchemeSnapshot(name, restored)) {
            this.clearDefinitionCache(name);
            return;
        }
        this.state.defTypes[name] = restored;
        this.syncSemanticConstantType(name);
        this.syncSemanticDefinition(name);
    }
    /** Install a cache produced by the immediately preceding Core check. */
    restoreCheckedDefinitionCache(name: string, cache: DefinitionTypeCacheSnapshot) {
        if (!cache) return;
        const restored = isSemanticDefinitionCacheSnapshot(cache)
            ? cloneSemanticDefinitionCache(cache)
            : migrateLegacyDefinitionCache(cache);
        if (!restored || !this.semanticTypeChecker.setConstantSchemeSnapshot(name, restored)) {
            this.clearDefinitionCache(name);
            return;
        }
        this.state.defTypes[name] = restored;
        // Preserve explicit system types as the authoritative public type;
        // the compiled scheme is used only when no system type exists.
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
    checkTypeFormation(
        ast: AST,
        context: Context = [],
        semanticResourceLimits?: SemanticTypeSynthesisResourceLimits
    ) {
        const candidate = Core.clone(ast);
        const inferred = this.checkType(
            candidate,
            context,
            false,
            undefined,
            false,
            true,
            false,
            semanticResourceLimits
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
            maxSteps: semanticResourceLimits?.synthesisMaxSteps
                ?? Core.semanticTypeSynthesisMaxSteps,
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
        preservePresentation = true,
        semanticResourceLimits?: SemanticTypeSynthesisResourceLimits
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
                resourceLimits: semanticResourceLimits,
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
        target.nbeGeneratedMeta = source.nbeGeneratedMeta;
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
        target.nbeGeneratedMeta = surface.nbeGeneratedMeta;
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
            resourceLimits?: SemanticTypeSynthesisResourceLimits;
        } = {}
    ): AST | undefined {
        const allowHoles = options.allowHoles ?? false;
        const semanticAst = Core.clone(ast);
        const requestedElaboration = options.elaborateMetas ?? false;
        const certifiedOutputMaxNodes = (() => {
            if (!this.certifiedLargeSystemTypes.size) return undefined;
            const stack = [semanticAst];
            while (stack.length) {
                const node = stack.pop()!;
                if (node.type === "var" && !node.bondVarId
                    && this.certifiedLargeSystemTypes.has(node.name)) {
                    return certifiedPath3ComputationResourceLimits.outputMaxNodes;
                }
                stack.push(...(node.nodes ?? []));
            }
            return undefined;
        })();
        const inputMaxNodes = options.resourceLimits?.inputMaxNodes
            ?? Core.semanticNbEMaxNodes;
        const synthesisMaxSteps = options.resourceLimits?.synthesisMaxSteps
            ?? Core.semanticTypeSynthesisMaxSteps;
        const outputMaxNodes = options.resourceLimits?.outputMaxNodes
            ?? certifiedOutputMaxNodes
            ?? Core.semanticTypeCheckMaxOutputNodes;
        // A bare reference to a polymorphic definition has no use-site
        // arguments that could solve its cached scheme metas. Returning the
        // safely generalized type is still a complete synthesis result. Keep
        // applications and user-written holes strict.
        const generalizeMetas = !!options.generalizeMetas
            || this.isBareGeneralizedDefinitionReference(semanticAst);
        const canTryWithoutElaboration = requestedElaboration
            && fitsSemanticNbeBudget(
                semanticAst,
                inputMaxNodes,
                false,
                context,
                false
            );
        const maxNodes = canTryWithoutElaboration
            ? inputMaxNodes
            : requestedElaboration
            ? Math.max(Core.semanticTypeElaborationMaxNodes, inputMaxNodes)
            : inputMaxNodes;
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
            maxSteps: synthesisMaxSteps,
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
                    ? synthesisMaxSteps * 4
                    : synthesisMaxSteps
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
            Math.max(inputMaxNodes, outputMaxNodes),
            false,
            context,
            false,
            generalizedMetaNames
        )) {
            if (exceedsSemanticNbeNodeBudget(
                semanticType.type,
                Math.max(inputMaxNodes, outputMaxNodes)
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
            outputMaxNodes,
            false,
            context,
            false,
            generalizedMetaNames
        )) {
            if (exceedsSemanticNbeNodeBudget(
                compactType,
                outputMaxNodes
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
