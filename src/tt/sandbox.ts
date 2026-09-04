import { AST, ASTParser } from "./astparser.js";
import {
    Core,
    type CoreHitPathLevels,
    type CoreSystemInductiveBundle,
    type DefinitionTypeCacheSnapshot,
    type SemanticDefinitionTypeCacheSnapshot
} from "./core.js";
import {
    TTCoreEngine,
    TTCoreCheckResult,
    type TTTrustedDeclarationOrderEntry
} from "./engine.js";
import { initTypeSystem } from "./initial.js";
import {
    TheoremWorkspace,
    TheoremWorkspaceItem,
    TheoremWorkspaceLayoutItem,
    TheoremWorkspaceMutation
} from "./theorem-workspace.js";
import {
    hasLegacySurfaceSyntax,
    migrateLegacyDeclarationSource,
    migrateLegacySurfaceExpression
} from "./surface-syntax-migration.js";
import { expandTypeTheoryAliasesInSurface } from "./symbol-aliases.js";
import {
    assertCanonicalHitPathLevels,
    createHitPathLevels,
    flattenHitPathLevels,
    highestHitPathLevel,
    hitPathConstructorsAt,
    hitPathLevelsFromCanonicalOrLegacy,
    type HitPathLevels
} from "./hit-path-levels.js";

const parser = new ASTParser();

export const SANDBOX_SAVE_VERSION = 1;
export const SANDBOX_VALIDATION_CACHE_VERSION = 1;

/**
 * Bump whenever parsing, lowering, Core registration, or NbE cache semantics
 * change. Persisted validation data is an optimization hint, never authority.
 */
export const SANDBOX_VALIDATION_SEMANTIC_EPOCH =
    "sandbox-nbe-recursive-hit-points-v1-2026-09-02";

const SANDBOX_VALIDATION_CACHE_MAX_ENTRIES = 4_096;
const SANDBOX_VALIDATION_CACHE_MAX_OBJECTS = 500_000;
const SANDBOX_VALIDATION_CACHE_MAX_DEPTH = 256;
const SANDBOX_VALIDATION_CACHE_MAX_STRING_UNITS = 8 * 1024 * 1024;

export type GameMode = "survival" | "creative";

/** The sandbox is an authoring tool and is intentionally unavailable in survival. */
export function sandboxEnabledInMode(mode: GameMode): boolean {
    return mode === "creative";
}

export type SandboxDeclarationKind = "type" | "term" | "proposition" | "definition" | "inductive" | "hit";
export type SandboxDeclarationStatus = "unchecked" | "valid" | "invalid" | "disabled";

/** A trusted, body-less declaration owned only by the sandbox environment. */
export type SandboxDeclaration = {
    id: string;
    name: string;
    kind: SandboxDeclarationKind;
    source: string;
    typeSource: string;
    enabled: boolean;
    trusted: true;
    status: SandboxDeclarationStatus;
    error?: string;
    dependencies: string[];
    folderId: string | null;
    /** Parsed stage-2 signature, present for `kind: "inductive"`. */
    inductive?: SandboxInductiveDeclaration;
    /** Parsed stage-3 first-order HIT signature, present for `kind: "hit"`. */
    hit?: SandboxHitDeclaration;
    /** All generated names owned by an inductive declaration. */
    generatedNames?: string[];
    /** Worker-produced display AST for ordinary declarations; never persisted. */
    presentationAst?: AST;
};

export type SandboxSavedDeclaration = Omit<
    SandboxDeclaration,
    "inductive" | "hit" | "generatedNames" | "presentationAst"
>;

/** Persist only source-owned declaration state; parsed/lowered fields are rebuilt and re-certified. */
export function toSandboxSavedDeclaration(
    declaration: SandboxDeclaration
): SandboxSavedDeclaration {
    const {
        inductive: _inductive,
        hit: _hit,
        generatedNames: _generatedNames,
        presentationAst: _presentationAst,
        ...saved
    } = declaration;
    return { ...saved, dependencies: [...saved.dependencies] };
}

export type SandboxFolder = {
    kind: "folder";
    id: string;
    name: string;
    /** Number of following workspace rows owned by this folder subtree. */
    length: number;
    open: boolean;
    disabled: boolean;
};

export type SandboxSave = {
    version: typeof SANDBOX_SAVE_VERSION;
    declarations: SandboxSavedDeclaration[];
    folders?: SandboxFolder[];
    /** Unified visual order, including folder rows and declaration rows. */
    order?: string[];
    /** Untrusted replay hints. Every entry is re-certified by Core on restore. */
    validationCache?: SandboxValidationCache;
};

/** Ordered declaration semantics shared by incremental validation and Worker session reuse. */
export function sandboxValidationSignatures(
    save: Pick<SandboxSave, "declarations" | "folders" | "order">
): string[] {
    const folders = new Map((save.folders ?? []).map(folder => [folder.id, folder] as const));
    const declarations = new Map(save.declarations.map(declaration => [declaration.id, declaration] as const));
    const items: TheoremWorkspaceItem[] = [];
    const seen = new Set<string>();
    const append = (id: string) => {
        if (seen.has(id)) return;
        const folder = folders.get(id);
        if (folder) {
            seen.add(id);
            items.push({
                kind: "folder",
                id: folder.id,
                name: folder.name,
                length: Math.max(0, Number(folder.length) || 0),
                open: folder.open !== false,
                disabled: !!folder.disabled
            });
            return;
        }
        const declaration = declarations.get(id);
        if (!declaration) return;
        seen.add(id);
        items.push({
            kind: "theorem",
            id: declaration.id,
            value: declaration.source,
            local: false
        });
    };
    for (const id of save.order ?? []) append(id);
    for (const folder of folders.values()) append(folder.id);
    for (const declaration of declarations.values()) append(declaration.id);

    const workspace = new TheoremWorkspace(items);
    const layout = new Map(workspace.layout().map(item => [item.id, item] as const));
    return workspace.snapshot()
        .filter((item): item is Extract<TheoremWorkspaceItem, { kind: "theorem" }> => item.kind === "theorem")
        .map(item => {
            const declaration = declarations.get(item.id);
            return JSON.stringify({
                id: item.id,
                source: declaration?.source ?? item.value,
                enabled: declaration?.enabled !== false,
                disabled: !!layout.get(item.id)?.disabled
            });
        });
}

export function sandboxValidationSemanticsKey(save: SandboxSave): string {
    return JSON.stringify({
        version: save.version,
        declarations: sandboxValidationSignatures(save)
    });
}

export type SandboxValidationCacheEntry = {
    id: string;
    /** Chained fingerprint of the exact ordered declaration prefix. */
    prefixKey: string;
    kind: SandboxDeclarationKind;
    status: "valid" | "disabled";
    artifact?:
        | { kind: "axiom"; type: AST }
        | {
            kind: "definition";
            body: AST;
            cache: SemanticDefinitionTypeCacheSnapshot;
        }
        | { kind: "inductive" }
        | { kind: "hit" };
};

export type SandboxValidationCache = {
    version: typeof SANDBOX_VALIDATION_CACHE_VERSION;
    semanticEpoch: typeof SANDBOX_VALIDATION_SEMANTIC_EPOCH;
    /** Fingerprint of the complete visible system prelude and Core config. */
    preludeKey: string;
    entries: SandboxValidationCacheEntry[];
};

export type SandboxValidationResult = {
    ok: boolean;
    declarations: SandboxDeclaration[];
    error?: string;
    bridge?: SandboxBridge;
    /** Stable outcome for callers that need to distinguish invalid input from a cancelled or bounded run. */
    status?: SandboxValidationStatus;
    /** Deterministic counters for incremental-session regression tests and diagnostics. */
    validationStats: SandboxValidationStats;
    /** Fresh replay hints produced only from the Core-certified prefix. */
    validationCache?: SandboxValidationCache;
};

export type SandboxValidationStatus = "ok" | "invalid" | "cancelled" | "budget-exhausted";

/** Resource controls owned by the sandbox worker rather than the game-wide Core. */
export type SandboxValidationBudget = {
    /** Maximum declarations accepted by one validation request. */
    maxDeclarations?: number;
    /** Maximum total source characters, checked before constructing parser ASTs. */
    maxSourceChars?: number;
    /** Maximum syntax AST nodes estimated from the complete declaration set. */
    maxNodes?: number;
    /** Maximum validation accounting steps (declarations plus syntax nodes). */
    maxSteps?: number;
    /** Optional wall-clock guard checked at deterministic declaration boundaries. */
    timeoutMs?: number;
};

export type SandboxValidationOptions = SandboxValidationBudget & {
    /** A callback keeps the synchronous environment usable by deterministic tests and workers. */
    shouldCancel?: () => boolean;
};

export type SandboxValidationStats = {
    /** Declarations whose source and dependencies were checked in this validation. */
    checkedDeclarations: number;
    /** Prefix declarations restored through the same Core registration boundary. */
    replayedDeclarations: number;
    /** Ordered declaration prefix represented by the live Core after validation. */
    validatedThrough: number;
};

type SandboxValidationCacheReplayResult =
    | { status: "restored"; count: number }
    | { status: "discarded"; count: 0 }
    | { status: "cancelled" | "budget-exhausted"; count: number };

export type SandboxWorkspaceMutation = TheoremWorkspaceMutation;

export type SandboxCheckResult = TTCoreCheckResult & {
    source: string;
};

/** Structured stage-2 (v1) ordinary inductive signature. */
export type SandboxInductiveBinder = {
    name: string;
    type: AST;
    typeSource: string;
};

export type SandboxInductiveArgument = SandboxInductiveBinder & {
    /**
     * A direct recursive value, or a strictly-positive function ending in one.
     * The telescope records the arguments needed to form its induction
     * hypothesis. For example `(nat -> Tree)` has one telescope binder.
     */
    recursiveTelescope: SandboxInductiveBinder[] | null;
    /** Family indices of the recursive value at the end of the telescope. */
    recursiveResultIndices: AST[] | null;
};

export type SandboxInductiveConstructor = {
    name: string;
    /** Constructor-local type, with declaration parameters in scope. */
    type: AST;
    typeSource: string;
    /** Compatibility/display projection; lowering uses `argumentAsts`. */
    arguments: string[];
    argumentAsts: SandboxInductiveArgument[];
    result: AST;
    /** Indices supplied to the family in this constructor's result. */
    resultIndices: AST[];
};

export type SandboxInductiveDeclaration = {
    name: string;
    parameters: SandboxInductiveBinder[];
    /** Non-uniform family indices, written as `[name : type]`. */
    indices: SandboxInductiveBinder[];
    /** Compatibility/display projection; lowering uses `universeAst`. */
    universe: string;
    universeAst: AST;
    constructors: SandboxInductiveConstructor[];
};

export type SandboxHitPathConstructor = {
    name: string;
    /** Path-local telescope, with declaration parameters in scope. */
    arguments: SandboxInductiveBinder[];
    type: AST;
    typeSource: string;
    left: AST;
    right: AST;
    /** Common family indices of both point endpoints. */
    resultIndices: AST[];
};

export type SandboxHitTwoPathConstructor = {
    name: string;
    /** Second-path-local telescope, with declaration parameters in scope. */
    arguments: SandboxInductiveBinder[];
    type: AST;
    typeSource: string;
    /** The two first-path constructor applications joined by this 2-path. */
    left: AST;
    right: AST;
    /** Closed first-path endpoint expressions; uniform parameters are implicit. */
    leftExpression: SandboxHitOnePathExpression;
    rightExpression: SandboxHitOnePathExpression;
    /** Underlying point endpoints, used to validate path coherence. */
    leftPoint: AST;
    rightPoint: AST;
    /** Common family indices of both first-path endpoint expressions. */
    resultIndices: AST[];
};

export type SandboxHitOnePathExpression =
    | { kind: "atom"; name: string; arguments: AST[] }
    | {
        kind: "compose";
        left: SandboxHitOnePathExpression;
        right: SandboxHitOnePathExpression;
    }
    | { kind: "inverse"; value: SandboxHitOnePathExpression };

export type SandboxHitTwoPathExpression =
    | { kind: "atom"; name: string; arguments: AST[] }
    | { kind: "refl"; pathName: string; arguments: AST[] }
    | {
        kind: "compose";
        left: SandboxHitTwoPathExpression;
        right: SandboxHitTwoPathExpression;
    }
    | { kind: "inverse"; value: SandboxHitTwoPathExpression };

export type SandboxHitThreePathConstructor = {
    name: string;
    /** Third-path-local telescope, with declaration parameters in scope. */
    arguments: SandboxInductiveBinder[];
    type: AST;
    typeSource: string;
    /** The two second-path constructor applications joined by this 3-path. */
    left: AST;
    right: AST;
    leftExpression: SandboxHitTwoPathExpression;
    rightExpression: SandboxHitTwoPathExpression;
    /** Legacy atomic projections retained until the Core v7 switch lands. */
    leftTwoPath: string;
    rightTwoPath: string;
    /** Shared first-path boundary of the two second paths. */
    sourcePath: AST;
    targetPath: AST;
    /** Shared point boundary, retained for recursive Core validation. */
    sourcePoint: AST;
    targetPoint: AST;
    /** Common family indices of both second-path endpoint expressions. */
    resultIndices: AST[];
};

/** Structured higher-inductive signature (parameterized and non-indexed). */
export type SandboxHitPathLevels = HitPathLevels<
    SandboxHitPathConstructor,
    SandboxHitTwoPathConstructor,
    SandboxHitThreePathConstructor
>;

export type SandboxHitDeclaration = {
    name: string;
    parameters: SandboxInductiveBinder[];
    indices: SandboxInductiveBinder[];
    universe: string;
    universeAst: AST;
    pointConstructors: SandboxInductiveConstructor[];
    /** Canonical internal ordering for 1D-3D path constructors. */
    pathLevels: SandboxHitPathLevels;
};

type SandboxHitPathSource =
    | { pathLevels: SandboxHitPathLevels }
    | {
        pathLevels?: undefined;
        pathConstructors: readonly SandboxHitPathConstructor[];
        twoPathConstructors?: readonly SandboxHitTwoPathConstructor[];
        threePathConstructors?: readonly SandboxHitThreePathConstructor[];
    };

export function sandboxHitPathLevels(
    signature: SandboxHitPathSource
): SandboxHitPathLevels {
    return hitPathLevelsFromCanonicalOrLegacy(signature);
}

export type SandboxInductiveMetadata = {
    version: 2 | 3 | 4 | 5 | 6 | 7 | 8;
    kind?: "inductive" | "hit1" | "hit2" | "hit3";
    dimension?: number;
    ruleSchemaVersion: 1;
    typeName: string;
    parameterCount: number;
    indexCount: number;
    indices: { name: string; type: AST }[];
    eliminatorName: string;
    fullEliminatorName: string;
    recursorName: string;
    fullRecursorName: string;
    constructors: {
        name: string;
        argumentTypes: AST[];
        argumentNames: string[];
        recursiveArguments: {
            index: number;
            telescope: { name: string; type: AST }[];
            resultIndices: AST[];
        }[];
        resultIndices: AST[];
    }[];
    pathLevels?: CoreHitPathLevels;
    pathConstructors?: {
        name: string;
        argumentTypes: AST[];
        argumentNames?: string[];
        left: AST;
        right: AST;
        resultIndices?: AST[];
        computationName?: string;
    }[];
    twoPathConstructors?: {
        name: string;
        argumentTypes: AST[];
        argumentNames?: string[];
        left: AST;
        right: AST;
        leftPath: string;
        rightPath: string;
        resultIndices?: AST[];
        computationName?: string;
        strongComputationName?: string;
    }[];
    threePathConstructors?: {
        name: string;
        argumentTypes: AST[];
        argumentNames?: string[];
        left: AST;
        right: AST;
        leftTwoPath: string;
        rightTwoPath: string;
        sourcePath: AST;
        targetPath: AST;
        computationName?: string;
        actionComputationName?: string;
    }[];
};

/** The read-only projection consumed by the creative type layer. */
export type SandboxInductiveBundle = CoreSystemInductiveBundle & {
    metadata: SandboxInductiveMetadata;
    generatedNames: string[];
};

export type SandboxBridge = {
    axioms: readonly [string, AST][];
    inductives: readonly SandboxInductiveBundle[];
    /** Transparent sandbox definitions, kept distinct from trusted axioms. */
    definitions?: readonly [string, AST][];
    /** Original workspace order across all enabled, validated declarations. */
    order?: readonly TTTrustedDeclarationOrderEntry[];
};

/**
 * Read-only system environment made available while validating the sandbox.
 * Ordinary theorem rows are deliberately excluded: they have ordered and
 * folder-local visibility which cannot be represented by a global prelude.
 */
export type SandboxEnvironmentOptions = {
    /** IDs from `initTypeSystem` that are visible as built-ins. */
    systemRuleIds?: readonly string[];
    /** Multiplier for the semantic NbE budgets used while checking declarations. */
    semanticResourceScale?: number;
    /** Per-request sandbox validation limits. */
    validationMaxDeclarations?: number;
    validationMaxSourceChars?: number;
    validationMaxNodes?: number;
    validationMaxSteps?: number;
    validationTimeoutMs?: number;
};

/** Generous browser defaults that still bound malformed or accidentally enormous sandbox input. */
export const browserSandboxValidationLimits = Object.freeze({
    validationMaxDeclarations: 2_048,
    validationMaxSourceChars: 1_000_000,
    validationMaxNodes: 1_000_000,
    validationMaxSteps: 1_250_000,
    validationTimeoutMs: 120_000
}) satisfies SandboxEnvironmentOptions;

const sandboxTypeSystemRules = Object.freeze(initTypeSystem());
const defaultSandboxSystemRuleIds = Object.freeze(
    [...new Set(sandboxTypeSystemRules.map(rule => rule.id))]
);

/**
 * The complete system prelude used by a creative-mode type layer.  The UI
 * normally passes its current unlocked set explicitly; this export is useful
 * for non-DOM callers that want the same prelude without importing `initial`.
 */
export const creativeSandboxSystemRuleIds = defaultSandboxSystemRuleIds;

const isolatedSandboxSystemRuleIds = Object.freeze([
    "True", "False", "eq", "eq.="
]);

function sandboxStringFingerprint(value: string) {
    let left = 2166136261 >>> 0;
    let right = 0x9e3779b9 >>> 0;
    for (let index = 0; index < value.length; index++) {
        const unit = value.charCodeAt(index);
        left ^= unit;
        left = Math.imul(left, 16777619) >>> 0;
        right ^= unit + 0x9e3779b9 + ((right << 6) >>> 0) + (right >>> 2);
        right >>>= 0;
    }
    return `${value.length}:${left.toString(16).padStart(8, "0")}:${right.toString(16).padStart(8, "0")}`;
}

function sandboxValidationPrefixKey(previous: string, signature: string) {
    return sandboxStringFingerprint(`${previous}\u0000${signature}`);
}

function sandboxValidationPreludeKey(
    systemRuleIds: readonly string[],
    semanticResourceScale: number | undefined
) {
    const visible = new Set(systemRuleIds);
    const rules = sandboxTypeSystemRules
        .filter(rule => visible.has(rule.id))
        .map(rule => ({
            id: rule.id,
            prefix: rule.prefix,
            inferMode: rule.inferMode,
            postfix: rule.postfix,
            ast: parser.stringify(rule.ast)
        }));
    return sandboxStringFingerprint(JSON.stringify({
        saveVersion: SANDBOX_SAVE_VERSION,
        cacheVersion: SANDBOX_VALIDATION_CACHE_VERSION,
        semanticEpoch: SANDBOX_VALIDATION_SEMANTIC_EPOCH,
        systemRuleIds,
        rules,
        inferDisplayMode: "_",
        semanticResourceScale: semanticResourceScale ?? 1
    }));
}

/** Iterative guard before any recursive clone/compiler sees untrusted cache data. */
function sandboxValidationCacheWithinLimits(value: unknown) {
    if (!value || typeof value !== "object") return false;
    const seen = new WeakSet<object>();
    const stack: { value: unknown; depth: number }[] = [{ value, depth: 0 }];
    let objects = 0;
    let stringUnits = 0;
    while (stack.length) {
        const current = stack.pop()!;
        if (current.depth > SANDBOX_VALIDATION_CACHE_MAX_DEPTH) return false;
        if (typeof current.value === "string") {
            stringUnits += current.value.length;
            if (stringUnits > SANDBOX_VALIDATION_CACHE_MAX_STRING_UNITS) return false;
            continue;
        }
        if (!current.value || typeof current.value !== "object") continue;
        if (seen.has(current.value)) return false;
        seen.add(current.value);
        if (++objects > SANDBOX_VALIDATION_CACHE_MAX_OBJECTS) return false;
        if (Array.isArray(current.value)) {
            for (const item of current.value) {
                stack.push({ value: item, depth: current.depth + 1 });
            }
            continue;
        }
        for (const [key, item] of Object.entries(current.value as Record<string, unknown>)) {
            if (key === "origin") return false;
            stringUnits += key.length;
            if (stringUnits > SANDBOX_VALIDATION_CACHE_MAX_STRING_UNITS) return false;
            stack.push({ value: item, depth: current.depth + 1 });
        }
    }
    return true;
}

function sandboxAstHasInferenceHole(ast: AST | undefined) {
    if (!ast) return false;
    const stack = [ast];
    while (stack.length) {
        const current = stack.pop()!;
        if (current.type === "var"
            && (current.name === "_" || current.name?.startsWith("?"))) return true;
        for (const child of current.nodes ?? []) stack.push(child);
    }
    return false;
}

type ParsedSandboxDeclaration = {
    ast?: AST;
    name: string;
    /** Declared or inferred type syntax, when available. */
    typeAst?: AST;
    typeSource: string;
    /** Body of a transparent `name := term` declaration. */
    definitionAst?: AST;
    inductive?: SandboxInductiveDeclaration;
    hit?: SandboxHitDeclaration;
};

const sandboxNamePattern = String.raw`(?:[A-Za-z_][A-Za-z0-9_']*|[0-9]+[A-Za-z_][A-Za-z0-9_']*)`;
const sandboxNameRegex = new RegExp(`^${sandboxNamePattern}$`);

/**
 * Clipboard content often contains non-breaking or zero-width whitespace
 * around `:=` (for example when copied from a rendered theorem row).  The
 * core parser intentionally keeps its strict surface grammar, so normalize
 * only sandbox declaration input before handing it to that parser.  This
 * keeps the saved source deterministic without changing identifier semantics
 * elsewhere in the type-theory language.
 */
function normalizeSandboxSource(source: string): string {
    return String(source ?? "")
        .replace(/[\u200B-\u200D\u2060\uFEFF]/g, "")
        .replace(/\p{White_Space}/gu, " ")
        .trim();
}

function findMatchingDelimiter(source: string, start: number, open: string, close: string) {
    let depth = 0;
    for (let index = start; index < source.length; index++) {
        if (source[index] === open) depth++;
        else if (source[index] === close) {
            depth--;
            if (depth === 0) return index;
        }
    }
    return -1;
}

function parseInductiveBinder(
    source: string,
    owner: string,
    role: "参数" | "索引" = "参数"
): SandboxInductiveBinder {
    let ast: AST;
    try {
        // Inductive declarations are parsed by the sandbox's internal
        // compatibility layer. User-facing declaration input is validated at
        // parseSandboxDeclaration; constructor fragments still need to accept
        // legacy ASCII syntax from existing fixtures and migrated saves.
        ast = parser.parse(source.trim());
    } catch (error) {
        throw new Error(`${owner}${role}格式错误：${source}（${String(error)}）`);
    }
    if (ast.type !== ":" || ast.nodes?.[0]?.type !== "var" || !ast.nodes?.[1]) {
        throw new Error(`${owner}${role}必须使用“名称 : 类型”格式：${source}`);
    }
    const name = ast.nodes[0].name;
    if (!sandboxNameRegex.test(name)) throw new Error(`${owner}${role}名称不合法：${name}`);
    return {
        name,
        type: ast.nodes[1],
        typeSource: parser.stringify(ast.nodes[1])
    };
}

function splitInductiveSections(source: string) {
    const sections: string[] = [];
    let current = "";
    let depth = 0;
    for (const character of source) {
        if (character === "(" || character === "[" ) depth++;
        else if (character === ")" || character === "]") depth = Math.max(0, depth - 1);
        if (character === "|" && depth === 0) {
            sections.push(current.trim());
            current = "";
        } else {
            current += character;
        }
    }
    sections.push(current.trim());
    return sections;
}

/**
 * Migrate the type-bearing part of an inductive/HIT header without treating
 * its declared name or telescope variable names as old single-letter syntax.
 */
function migrateSandboxHeaderTail(source: string): string {
    let output = "";
    let cursor = 0;
    while (cursor < source.length) {
        const character = source[cursor];
        if (character === "(" || character === "[") {
            const close = character === "(" ? ")" : "]";
            const end = findMatchingDelimiter(source, cursor, character, close);
            if (end < 0) return output + source.slice(cursor);
            // Header telescope binders use `name : type`; preserving the left
            // side prevents e.g. `Pfoo` from becoming `Πfoo` on restore.
            output += character
                + migrateLegacyDeclarationSource(source.slice(cursor + 1, end))
                + close;
            cursor = end + 1;
            continue;
        }
        if (character === ":") {
            return output + ":" + migrateLegacySurfaceExpression(source.slice(cursor + 1));
        }
        output += character;
        cursor++;
    }
    return output;
}

/**
 * Migrate an old sandbox declaration at the save-load boundary.
 *
 * The general declaration migration is correct for ordinary entries.  An
 * inductive/HIT source additionally owns names in its header and each `|`
 * section, so those name portions remain opaque while their right-hand type
 * expressions are migrated.
 */
export function migrateLegacySandboxDeclarationSource(source: string): string {
    if (!source || typeof source !== "string") return source;
    const sections = splitInductiveSections(source);
    const header = sections[0] ?? "";
    const match = /^(\s*(?:inductive|hit)\s+)([^\s(\[\]|:]+)([\s\S]*)$/iu.exec(header);
    if (!match) return migrateLegacyDeclarationSource(source);
    const migratedHeader = match[1] + match[2] + migrateSandboxHeaderTail(match[3]);
    return [
        migratedHeader,
        ...sections.slice(1).map(section => migrateLegacyDeclarationSource(section))
    ].join(" | ");
}

/**
 * Clone and migrate the syntax fields of one sandbox save.  This is purposely
 * a load-boundary adapter: folder layout, row IDs, enabled state, validation
 * metadata, and any future persisted fields pass through untouched.
 */
export function migrateLegacySandboxSave(value: unknown): unknown {
    if (!value || typeof value !== "object" || !Array.isArray((value as { declarations?: unknown }).declarations)) {
        return value;
    }
    const save = value as { declarations: unknown[] };
    return {
        ...(value as Record<string, unknown>),
        declarations: save.declarations.map(declaration => {
            if (!declaration || typeof declaration !== "object") return declaration;
            const raw = declaration as Record<string, unknown>;
            const migrated: Record<string, unknown> = { ...raw };
            if (typeof raw.source === "string") {
                migrated.source = migrateLegacySandboxDeclarationSource(raw.source);
            }
            if (typeof raw.typeSource === "string") {
                migrated.typeSource = migrateLegacySurfaceExpression(raw.typeSource);
            }
            return migrated;
        })
    };
}

function flattenApplication(ast: AST): AST[] {
    const terms: AST[] = [];
    let head = ast;
    while (head?.type === "apply" && head.nodes?.[0] && head.nodes?.[1]) {
        terms.unshift(head.nodes[1]);
        head = head.nodes[0];
    }
    terms.unshift(head);
    return terms;
}

function inductiveResultIndices(
    ast: AST,
    name: string,
    parameters: readonly SandboxInductiveBinder[],
    indexCount: number,
    constructorName: string
): AST[] | null {
    const terms = flattenApplication(ast);
    if (terms[0]?.type !== "var" || terms[0].name !== name) return null;
    const expected = parameters.length + indexCount;
    if (terms.length !== expected + 1) {
        throw new Error(
            `构造子 ${constructorName} 返回 ${name} 时索引数量错误：需要 ${indexCount} 个索引`
        );
    }
    for (let index = 0; index < parameters.length; index++) {
        const argument = terms[index + 1];
        if (argument?.type !== "var" || argument.name !== parameters[index].name) {
            throw new Error(
                `构造子 ${constructorName} 的返回参数必须保持统一参数 ${parameters[index].name}`
            );
        }
    }
    return terms.slice(parameters.length + 1).map(term => Core.clone(term));
}

type SandboxRecursiveOccurrence = {
    telescope: SandboxInductiveBinder[];
    resultIndices: AST[];
};

function recursiveOccurrence(
    ast: AST,
    signatureName: string,
    parameters: readonly SandboxInductiveBinder[],
    indexCount: number,
    constructorName: string
): SandboxRecursiveOccurrence | null {
    const directIndices = inductiveResultIndices(
        ast,
        signatureName,
        parameters,
        indexCount,
        constructorName
    );
    if (directIndices) return { telescope: [], resultIndices: directIndices };
    if (ast.type === "P" || ast.type === "->") {
        const domain = ast.nodes?.[0];
        const body = ast.nodes?.[1];
        if (!domain || !body) throw new Error(`构造子 ${constructorName} 参数类型不完整`);
        if (containsSandboxName(domain, signatureName)) {
            throw new Error(`归纳类型必须严格正：构造子 ${constructorName} 在函数参数位置含有 ${signatureName}`);
        }
        const tail = recursiveOccurrence(
            body,
            signatureName,
            parameters,
            indexCount,
            constructorName
        );
        if (tail) {
            const used = new Set(tail.telescope.map(binder => binder.name));
            let binderName = ast.type === "P" && ast.name ? ast.name : "x";
            for (let suffix = 1; used.has(binderName); suffix++) binderName = `x${suffix}`;
            return {
                telescope: [{
                    name: binderName,
                    type: Core.clone(domain),
                    typeSource: parser.stringify(domain)
                }, ...tail.telescope],
                resultIndices: tail.resultIndices
            };
        }
        return null;
    }
    if (containsSandboxName(ast, signatureName)) {
        throw new Error(`构造子 ${constructorName} 含有尚不支持的嵌套递归出现：${signatureName}`);
    }
    return null;
}

function renameFreeInductiveNames(ast: AST, replacements: ReadonlyMap<string, string>, bound = new Set<string>()): AST {
    const clone = Core.clone(ast);
    const visit = (node: AST, scope: Set<string>) => {
        if (node.type === "var") {
            const replacement = !scope.has(node.name) ? replacements.get(node.name) : undefined;
            if (replacement) node.name = replacement;
            return;
        }
        if (["P", "L", "S", "W"].includes(node.type) && node.nodes?.[0] && node.nodes?.[1]) {
            visit(node.nodes[0], scope);
            const next = new Set(scope);
            if (node.name) next.add(node.name);
            visit(node.nodes[1], next);
            return;
        }
        for (const child of node.nodes ?? []) visit(child, scope);
    };
    visit(clone, bound);
    return clone;
}

/** Restore parser-only aliases, including aliases that appeared as binders. */
function restoreSandboxParsedNames(ast: AST, replacements: ReadonlyMap<string, string>): AST {
    const clone = Core.clone(ast);
    const visit = (node: AST) => {
        if (node.type === "var") {
            node.name = replacements.get(node.name) ?? node.name;
        } else if (["P", "L", "S", "W"].includes(node.type)) {
            node.name = replacements.get(node.name) ?? node.name;
        }
        for (const child of node.nodes ?? []) visit(child);
    };
    visit(clone);
    return clone;
}

function replaceSandboxIdentifiers(source: string, replacements: ReadonlyMap<string, string>) {
    let result = source;
    const entries = [...replacements.entries()].sort((left, right) => right[0].length - left[0].length);
    for (const [name, replacement] of entries) {
        const escaped = name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
        result = result.replace(
            new RegExp(`(?<![A-Za-z0-9_'])${escaped}(?![A-Za-z0-9_'])`, "g"),
            replacement
        );
    }
    return result;
}

function sandboxHitParserAliases(source: string, names: readonly string[]) {
    const hidden = new Map<string, string>();
    const restored = new Map<string, string>();
    let sequence = 0;
    for (const name of names) {
        if (hidden.has(name)) continue;
        let alias = `_SandboxHitName${sequence++}`;
        while (source.includes(alias) || restored.has(alias)) {
            alias = `_SandboxHitName${sequence++}`;
        }
        hidden.set(name, alias);
        restored.set(alias, name);
    }
    return { hidden, restored };
}

function collectSandboxAstNames(ast: AST, names = new Set<string>()) {
    if (ast.name) names.add(ast.name);
    for (const child of ast.nodes ?? []) collectSandboxAstNames(child, names);
    return names;
}

function renameRecursiveOccurrence(
    occurrence: SandboxRecursiveOccurrence,
    reserved: Set<string>
) {
    const replacements = new Map<string, string>();
    const renamed: SandboxInductiveBinder[] = [];
    for (const binder of occurrence.telescope) {
        const type = renameFreeInductiveNames(binder.type, replacements);
        let name = binder.name;
        if (reserved.has(name)) {
            name = "i";
            for (let suffix = 1; reserved.has(name); suffix++) name = `i${suffix}`;
        }
        replacements.set(binder.name, name);
        reserved.add(name);
        renamed.push({ name, type, typeSource: parser.stringify(type) });
    }
    return {
        telescope: renamed,
        resultIndices: occurrence.resultIndices.map(index =>
            renameFreeInductiveNames(index, replacements)
        )
    };
}

function decomposeConstructorType(
    type: AST,
    signatureName: string,
    parameters: readonly SandboxInductiveBinder[],
    indices: readonly SandboxInductiveBinder[],
    constructorName: string,
    constructorIndex: number
) {
    const arguments_: SandboxInductiveArgument[] = [];
    const usedNames = new Set([
        signatureName,
        ...parameters.map(parameter => parameter.name)
    ]);
    let result = Core.clone(type);
    while ((result.type === "P" || result.type === "->") && result.nodes?.[0] && result.nodes?.[1]) {
        let name = result.type === "P" && result.name
            ? result.name
            : `a${constructorIndex}_${arguments_.length}`;
        if (usedNames.has(name)) {
            if (result.type === "P") {
                throw new Error(`构造子 ${constructorName} 的参数名称重复或遮蔽类型参数：${name}`);
            }
            const base = name;
            for (let suffix = 1; usedNames.has(name); suffix++) name = `${base}_${suffix}`;
        }
        usedNames.add(name);
        const argumentType = Core.clone(result.nodes[0]);
        const recursive = recursiveOccurrence(
            argumentType,
            signatureName,
            parameters,
            indices.length,
            constructorName
        );
        arguments_.push({
            name,
            type: argumentType,
            typeSource: parser.stringify(argumentType),
            recursiveTelescope: recursive?.telescope ?? null,
            recursiveResultIndices: recursive?.resultIndices ?? null
        });
        result = Core.clone(result.nodes[1]);
    }
    const resultIndices = inductiveResultIndices(
        result,
        signatureName,
        parameters,
        indices.length,
        constructorName
    );
    if (!resultIndices) {
        if (containsSandboxName(result, signatureName)) {
            throw new Error(`构造子 ${constructorName} 必须直接返回 ${signatureName}`);
        }
        throw new Error(`构造子 ${constructorName} 必须返回 ${signatureName}`);
    }
    const recursiveScope = new Set([...usedNames, signatureName]);
    for (const argument of arguments_) {
        if (argument.recursiveTelescope) {
            const renamed = renameRecursiveOccurrence({
                telescope: argument.recursiveTelescope,
                resultIndices: argument.recursiveResultIndices ?? []
            },
                recursiveScope
            );
            argument.recursiveTelescope = renamed.telescope;
            argument.recursiveResultIndices = renamed.resultIndices;
        }
    }
    return { arguments: arguments_, result, resultIndices };
}

/** Extract declaration-owned telescope names before the compact parser sees them. */
function sandboxHeaderBinderNames(source: string): string[] {
    const names: string[] = [];
    let remainder = source.trim();
    while (remainder.startsWith("(") || remainder.startsWith("[")) {
        const open = remainder[0];
        const close = open === "(" ? ")" : "]";
        const end = findMatchingDelimiter(remainder, 0, open, close);
        if (end < 0) break;
        const match = new RegExp(String.raw`^\s*(${sandboxNamePattern})\s*:`).exec(
            remainder.slice(1, end)
        );
        if (match) names.push(match[1]);
        remainder = remainder.slice(end + 1).trim();
    }
    return names;
}

export function parseSandboxInductive(source: string): SandboxInductiveDeclaration {
    const text = normalizeSandboxSource(source);
    const [rawHeader, ...rawConstructors] = splitInductiveSections(text);
    const header = new RegExp(String.raw`^inductive\s+(${sandboxNamePattern})([\s\S]*)$`, "i")
        .exec(rawHeader);
    if (!header) {
        throw new Error("普通归纳类型声明必须使用 inductive 名称 [(参数 : 类型)] : Universe 格式");
    }
    const name = header[1];
    const constructorParts = rawConstructors
        .map(part => part.trim())
        .filter(Boolean)
        .map(raw => {
            const match = new RegExp(
                String.raw`^(${sandboxNamePattern})\s*(?::\s*([\s\S]*))?$`
            ).exec(raw);
            if (!match) throw new Error(`归纳构造子格式错误：${raw}`);
            return { raw, name: match[1], typeSource: match[2]?.trim() };
        });
    const aliases = sandboxHitParserAliases(
        text,
        [name, ...sandboxHeaderBinderNames(header[2]), ...constructorParts.map(part => part.name)]
    );
    const hideReferences = (value: string) => replaceSandboxIdentifiers(value, aliases.hidden);
    const restoreReferences = (ast: AST) => restoreSandboxParsedNames(ast, aliases.restored);
    let remainder = header[2].trim();
    const parameters: SandboxInductiveBinder[] = [];
    const indices: SandboxInductiveBinder[] = [];
    const parameterNames = new Set<string>();
    while (remainder.startsWith("(")) {
        const end = findMatchingDelimiter(remainder, 0, "(", ")");
        if (end < 0) throw new Error(`归纳类型 ${name} 的参数括号未闭合`);
        const parameter = parseInductiveBinder(
            hideReferences(remainder.slice(1, end)),
            `归纳类型 ${name}`
        );
        parameter.name = aliases.restored.get(parameter.name) ?? parameter.name;
        parameter.type = restoreReferences(parameter.type);
        parameter.typeSource = parser.stringify(parameter.type);
        if (parameter.name === name || parameterNames.has(parameter.name)) {
            throw new Error(`归纳类型 ${name} 的参数名称冲突：${parameter.name}`);
        }
        parameters.push(parameter);
        parameterNames.add(parameter.name);
        remainder = remainder.slice(end + 1).trim();
    }
    const indexNames = new Set<string>();
    while (remainder.startsWith("[")) {
        const end = findMatchingDelimiter(remainder, 0, "[", "]");
        if (end < 0) throw new Error(`归纳类型 ${name} 的索引括号未闭合`);
        const indexBinder = parseInductiveBinder(
            hideReferences(remainder.slice(1, end)),
            `归纳类型 ${name}`,
            "索引"
        );
        indexBinder.name = aliases.restored.get(indexBinder.name) ?? indexBinder.name;
        indexBinder.type = restoreReferences(indexBinder.type);
        indexBinder.typeSource = parser.stringify(indexBinder.type);
        if (indexBinder.name === name
            || parameterNames.has(indexBinder.name)
            || indexNames.has(indexBinder.name)) {
            throw new Error(`归纳类型 ${name} 的索引名称冲突：${indexBinder.name}`);
        }
        indices.push(indexBinder);
        indexNames.add(indexBinder.name);
        remainder = remainder.slice(end + 1).trim();
    }
    if (!remainder.startsWith(":")) {
        throw new Error(`归纳类型 ${name} 缺少 Universe 类型注释`);
    }
    const universeSource = remainder.slice(1).trim();
    if (!universeSource) throw new Error(`归纳类型 ${name} 缺少 Universe`);
    let universe: AST;
    try {
        universe = restoreReferences(parser.parse(hideReferences(universeSource)));
    } catch (error) {
        throw new Error(`归纳类型 ${name} 的 Universe 格式错误：${String(error)}`);
    }
    for (const parameter of parameters) {
        if (containsSandboxName(parameter.type, name)) {
            throw new Error(`归纳类型参数 ${parameter.name} 的类型不能递归引用 ${name}`);
        }
    }
    for (const indexBinder of indices) {
        if (containsSandboxName(indexBinder.type, name)) {
            throw new Error(`归纳类型索引 ${indexBinder.name} 的类型不能递归引用 ${name}`);
        }
    }
    if (containsSandboxName(universe, name)) {
        throw new Error(`归纳类型 ${name} 的 Universe 不能递归引用自身`);
    }

    const familyApplication = sandboxApply(
        sandboxVar(name),
        ...parameters.map(parameter => sandboxVar(parameter.name)),
        ...indices.map(index => sandboxVar(index.name))
    );
    const constructors: SandboxInductiveConstructor[] = [];
    for (const [constructorIndex, part] of constructorParts.entries()) {
        const constructorName = part.name;
        const explicitType = part.typeSource;
        if (!explicitType && indices.length) {
            throw new Error(`索引归纳构造子 ${constructorName} 必须显式写出返回索引`);
        }
        const typeSource = explicitType || parser.stringify(familyApplication);
        let type: AST;
        try {
            type = restoreReferences(parser.parse(hideReferences(typeSource)));
        } catch (error) {
            throw new Error(`构造子 ${constructorName} 类型格式错误：${String(error)}`);
        }
        const decomposed = decomposeConstructorType(
            type,
            name,
            parameters,
            indices,
            constructorName,
            constructorIndex
        );
        constructors.push({
            name: constructorName,
            type,
            typeSource,
            arguments: decomposed.arguments.map(argument => argument.typeSource),
            argumentAsts: decomposed.arguments,
            result: decomposed.result,
            resultIndices: decomposed.resultIndices
        });
    }
    if (!constructors.length) throw new Error("归纳类型至少需要一个构造子");
    const names = new Set<string>();
    for (const ctor of constructors) {
        if (ctor.name === name || names.has(ctor.name)) throw new Error(`归纳构造子名称冲突：${ctor.name}`);
        names.add(ctor.name);
    }
    return {
        name,
        parameters,
        indices,
        universe: universeSource,
        universeAst: universe,
        constructors
    };
}

function sandboxPathTelescope(type: AST, owner: string) {
    const arguments_: SandboxInductiveBinder[] = [];
    const used = new Set<string>();
    let body = Core.clone(type);
    while ((body.type === "P" || body.type === "->") && body.nodes?.[0] && body.nodes?.[1]) {
        let name = body.type === "P" && body.name ? body.name : `x${arguments_.length}`;
        if (body.type === "->") {
            const unavailable = collectSandboxAstNames(body.nodes[1], new Set(used));
            const base = name;
            for (let suffix = 1; unavailable.has(name); suffix++) name = `${base}_${suffix}`;
        }
        if (used.has(name)) {
            throw new Error(`路径构造子 ${owner} 的参数名称重复：${name}`);
        }
        used.add(name);
        arguments_.push({
            name,
            type: Core.clone(body.nodes[0]),
            typeSource: parser.stringify(body.nodes[0])
        });
        body = Core.clone(body.nodes[1]);
    }
    return { arguments: arguments_, body };
}

function elaborateHitEndpoint(
    endpoint: AST,
    signatureName: string,
    parameters: readonly SandboxInductiveBinder[],
    pointConstructors: readonly SandboxInductiveConstructor[],
    pathName: string,
    boundNames: ReadonlySet<string>,
    state = { nodes: 0 },
    depth = 0
) {
    if (depth > 128) throw new Error(`路径构造子 ${pathName} 的点端点嵌套过深`);
    if (++state.nodes > 4_096) throw new Error(`路径构造子 ${pathName} 的点端点节点过多`);
    const terms = flattenApplication(endpoint);
    const headName = terms[0]?.type === "var" ? terms[0].name : "";
    if (boundNames.has(headName)) {
        throw new Error(`路径构造子 ${pathName} 的端点 ${headName} 被局部参数遮蔽`);
    }
    const point = pointConstructors.find(constructor => constructor.name === headName);
    if (!point) {
        throw new Error(
            `路径构造子 ${pathName} 的路径端点必须由 ${signatureName} 的点构造子形成`
        );
    }
    const supplied = terms.slice(1);
    const pointArgumentCount = point.argumentAsts.length;
    const fullArgumentCount = parameters.length + pointArgumentCount;
    let arguments_: AST[];
    if (supplied.length === pointArgumentCount) {
        arguments_ = [
            ...parameters.map(parameter => sandboxVar(parameter.name)),
            ...supplied.map(argument => Core.clone(argument))
        ];
    } else if (supplied.length === fullArgumentCount) {
        for (let index = 0; index < parameters.length; index++) {
            const argument = supplied[index];
            if (argument?.type !== "var" || argument.name !== parameters[index].name) {
                throw new Error(
                    `路径构造子 ${pathName} 的端点必须保持统一参数 ${parameters[index].name}`
                );
            }
        }
        arguments_ = supplied.map(argument => Core.clone(argument));
    } else {
        throw new Error(
            `路径构造子 ${pathName} 的端点 ${headName} 参数数量错误：需要 ${pointArgumentCount} 个点参数`
        );
    }
    for (let index = 0; index < point.argumentAsts.length; index++) {
        const recursive = point.argumentAsts[index].recursiveTelescope;
        if (!recursive || recursive.length) continue;
        arguments_[parameters.length + index] = elaborateHitEndpoint(
            arguments_[parameters.length + index],
            signatureName,
            parameters,
            pointConstructors,
            pathName,
            boundNames,
            state,
            depth + 1
        ).term;
    }
    const argumentReplacements = new Map<string, AST>();
    point.argumentAsts.forEach((argument, index) => {
        argumentReplacements.set(argument.name, arguments_[parameters.length + index]);
    });
    return {
        term: sandboxConstructorTerm(headName, arguments_),
        resultIndices: point.resultIndices.map(index =>
            substituteSandboxFreeVars(index, argumentReplacements)
        )
    };
}

function substituteSandboxFreeVars(
    ast: AST,
    replacements: ReadonlyMap<string, AST>,
    bound = new Set<string>()
): AST {
    if (!ast) return ast;
    if (ast.type === "var") {
        const replacement = !bound.has(ast.name) ? replacements.get(ast.name) : undefined;
        return replacement ? Core.clone(replacement) : Core.clone(ast);
    }
    const clone = Core.clone(ast);
    if (["P", "L", "S", "W"].includes(clone.type)
        && clone.nodes?.[0] && clone.nodes?.[1]) {
        clone.nodes[0] = substituteSandboxFreeVars(clone.nodes[0], replacements, bound);
        const next = new Set(bound);
        if (clone.name) next.add(clone.name);
        clone.nodes[1] = substituteSandboxFreeVars(clone.nodes[1], replacements, next);
        return clone;
    }
    clone.nodes = clone.nodes?.map(child =>
        substituteSandboxFreeVars(child, replacements, bound)
    );
    return clone;
}

type ElaboratedHitOnePathExpression = {
    expression: SandboxHitOnePathExpression;
    term: AST;
    sourcePoint: AST;
    targetPoint: AST;
    /** Family indices of the first-path endpoints. */
    resultIndices: AST[];
};

const SANDBOX_HIT_ONE_PATH_EXPRESSION_MAX_DEPTH = 128;
const SANDBOX_HIT_ONE_PATH_EXPRESSION_MAX_NODES = 4_096;

function elaborateHitTwoPathEndpoint(
    endpoint: AST,
    signatureName: string,
    parameters: readonly SandboxInductiveBinder[],
    pointConstructors: readonly SandboxInductiveConstructor[],
    pathConstructors: readonly SandboxHitPathConstructor[],
    pathName: string,
    boundNames: ReadonlySet<string>,
    budget = { nodes: 0 },
    depth = 0
): ElaboratedHitOnePathExpression {
    if (depth > SANDBOX_HIT_ONE_PATH_EXPRESSION_MAX_DEPTH) {
        throw new Error(`二阶路径构造子 ${pathName} 的一阶路径表达式嵌套过深`);
    }
    if (++budget.nodes > SANDBOX_HIT_ONE_PATH_EXPRESSION_MAX_NODES) {
        throw new Error(`二阶路径构造子 ${pathName} 的一阶路径表达式节点过多`);
    }
    if (endpoint.type === "*" && endpoint.nodes?.[0] && endpoint.nodes?.[1]) {
        const left = elaborateHitTwoPathEndpoint(
            endpoint.nodes[0], signatureName, parameters, pointConstructors,
            pathConstructors, pathName, boundNames, budget, depth + 1
        );
        const right = elaborateHitTwoPathEndpoint(
            endpoint.nodes[1], signatureName, parameters, pointConstructors,
            pathConstructors, pathName, boundNames, budget, depth + 1
        );
        if (!sameSandboxAst(left.targetPoint, right.sourcePoint)) {
            throw new Error(`二阶路径构造子 ${pathName} 的组合端点中间点边界不一致`);
        }
        if (left.resultIndices.length !== right.resultIndices.length
            || left.resultIndices.some((index, position) =>
                !sameSandboxAst(index, right.resultIndices[position]))) {
            throw new Error(`二阶路径构造子 ${pathName} 的组合端点索引纤维不一致`);
        }
        return {
            expression: {
                kind: "compose",
                left: left.expression,
                right: right.expression
            },
            term: sandboxCompose(left.term, right.term),
            sourcePoint: left.sourcePoint,
            targetPoint: right.targetPoint,
            resultIndices: left.resultIndices.map(index => Core.clone(index))
        };
    }
    const inverseTerms = flattenApplication(endpoint);
    if (inverseTerms.length === 2
        && inverseTerms[0]?.type === "var"
        && inverseTerms[0].name === "inveq") {
        const value = elaborateHitTwoPathEndpoint(
            inverseTerms[1], signatureName, parameters, pointConstructors,
            pathConstructors, pathName, boundNames, budget, depth + 1
        );
        return {
            expression: { kind: "inverse", value: value.expression },
            term: sandboxApply(sandboxVar("inveq"), value.term),
            sourcePoint: value.targetPoint,
            targetPoint: value.sourcePoint,
            resultIndices: value.resultIndices.map(index => Core.clone(index))
        };
    }
    const terms = flattenApplication(endpoint);
    const headName = terms[0]?.type === "var" ? terms[0].name : "";
    if (boundNames.has(headName)) {
        throw new Error(`二阶路径构造子 ${pathName} 的端点 ${headName} 被局部参数遮蔽`);
    }
    const path = pathConstructors.find(candidate => candidate.name === headName);
    if (!path) {
        throw new Error(
            `二阶路径构造子 ${pathName} 的端点必须由 ${signatureName} 的一阶路径构造子形成`
        );
    }
    const supplied = terms.slice(1);
    const fullArgumentCount = parameters.length + path.arguments.length;
    let arguments_: AST[];
    if (supplied.length === path.arguments.length) {
        arguments_ = [
            ...parameters.map(parameter => sandboxVar(parameter.name)),
            ...supplied.map(argument => Core.clone(argument))
        ];
    } else if (supplied.length === fullArgumentCount) {
        for (let index = 0; index < parameters.length; index++) {
            const argument = supplied[index];
            if (argument?.type !== "var" || argument.name !== parameters[index].name) {
                throw new Error(
                    `二阶路径构造子 ${pathName} 的端点必须保持统一参数 ${parameters[index].name}`
                );
            }
        }
        arguments_ = supplied.map(argument => Core.clone(argument));
    } else {
        throw new Error(
            `二阶路径构造子 ${pathName} 的端点 ${headName} 参数数量错误：需要 ${path.arguments.length} 个路径参数`
        );
    }
    const pathTerm = sandboxConstructorTerm(headName, arguments_);
    const argumentReplacements = new Map<string, AST>();
    path.arguments.forEach((argument, index) => {
        argumentReplacements.set(argument.name, arguments_[parameters.length + index]);
    });
    return {
        expression: {
            kind: "atom",
            name: path.name,
            arguments: arguments_.slice(parameters.length).map(argument => Core.clone(argument))
        },
        term: pathTerm,
        sourcePoint: substituteSandboxFreeVars(path.left, argumentReplacements),
        targetPoint: substituteSandboxFreeVars(path.right, argumentReplacements),
        resultIndices: path.resultIndices.map(index =>
            substituteSandboxFreeVars(index, argumentReplacements)
        )
    };
}

type ElaboratedHitTwoPathExpression = {
    expression: SandboxHitTwoPathExpression;
    term: AST;
    sourcePath: AST;
    targetPath: AST;
    sourcePoint: AST;
    targetPoint: AST;
    /** Family indices of the second-path endpoints. */
    resultIndices: AST[];
};

const SANDBOX_HIT_TWO_PATH_EXPRESSION_MAX_DEPTH = 128;
const SANDBOX_HIT_TWO_PATH_EXPRESSION_MAX_NODES = 4_096;

function elaborateHitThreePathEndpoint(
    endpoint: AST,
    signatureName: string,
    parameters: readonly SandboxInductiveBinder[],
    pathConstructors: readonly SandboxHitPathConstructor[],
    twoPathConstructors: readonly SandboxHitTwoPathConstructor[],
    pathName: string,
    boundNames: ReadonlySet<string>,
    budget = { nodes: 0 },
    depth = 0
) : ElaboratedHitTwoPathExpression {
    if (depth > SANDBOX_HIT_TWO_PATH_EXPRESSION_MAX_DEPTH) {
        throw new Error(`三阶路径构造子 ${pathName} 的二阶路径表达式嵌套过深`);
    }
    if (++budget.nodes > SANDBOX_HIT_TWO_PATH_EXPRESSION_MAX_NODES) {
        throw new Error(`三阶路径构造子 ${pathName} 的二阶路径表达式节点过多`);
    }
    if (endpoint.type === "*" && endpoint.nodes?.[0] && endpoint.nodes?.[1]) {
        const left = elaborateHitThreePathEndpoint(
            endpoint.nodes[0], signatureName, parameters, pathConstructors, twoPathConstructors,
            pathName, boundNames, budget, depth + 1
        );
        const right = elaborateHitThreePathEndpoint(
            endpoint.nodes[1], signatureName, parameters, pathConstructors, twoPathConstructors,
            pathName, boundNames, budget, depth + 1
        );
        if (!sameSandboxAst(left.targetPath, right.sourcePath)) {
            throw new Error(
                `三阶路径构造子 ${pathName} 的二阶路径组合边界不一致：`
                + `${parser.stringify(left.targetPath)} != ${parser.stringify(right.sourcePath)}`
            );
        }
        if (!sameSandboxAst(left.targetPoint, right.sourcePoint)) {
            throw new Error(`三阶路径构造子 ${pathName} 的二阶路径组合点边界不一致`);
        }
        if (left.resultIndices.length !== right.resultIndices.length
            || left.resultIndices.some((index, position) =>
                !sameSandboxAst(index, right.resultIndices[position]))) {
            throw new Error(`三阶路径构造子 ${pathName} 的二阶路径组合索引纤维不一致`);
        }
        return {
            expression: { kind: "compose", left: left.expression, right: right.expression },
            term: sandboxCompose(left.term, right.term),
            sourcePath: left.sourcePath,
            targetPath: right.targetPath,
            sourcePoint: left.sourcePoint,
            targetPoint: right.targetPoint,
            resultIndices: left.resultIndices.map(index => Core.clone(index))
        };
    }
    const inverseTerms = flattenApplication(endpoint);
    if (inverseTerms.length === 2
        && inverseTerms[0]?.type === "var"
        && inverseTerms[0].name === "inveq") {
        const value = elaborateHitThreePathEndpoint(
            inverseTerms[1], signatureName, parameters, pathConstructors, twoPathConstructors,
            pathName, boundNames, budget, depth + 1
        );
        return {
            expression: { kind: "inverse", value: value.expression },
            term: sandboxApply(sandboxVar("inveq"), value.term),
            sourcePath: value.targetPath,
            targetPath: value.sourcePath,
            sourcePoint: value.targetPoint,
            targetPoint: value.sourcePoint,
            resultIndices: value.resultIndices.map(index => Core.clone(index))
        };
    }
    const terms = flattenApplication(endpoint);
    if (terms[0]?.type === "var" && terms[0].name === "refl") {
        if (terms.length !== 2) {
            throw new Error(
                `三阶路径构造子 ${pathName} 的 refl 端点必须恰好引用一个一阶路径构造子`
            );
        }
        const pathTerms = flattenApplication(terms[1]);
        const firstPathName = pathTerms[0]?.type === "var" ? pathTerms[0].name : "";
        if (boundNames.has(firstPathName)) {
            throw new Error(
                `三阶路径构造子 ${pathName} 的 refl 端点 ${firstPathName} 被局部参数遮蔽`
            );
        }
        const firstPath = pathConstructors.find(candidate => candidate.name === firstPathName);
        if (!firstPath) {
            throw new Error(
                `三阶路径构造子 ${pathName} 的 refl 端点必须引用 ${signatureName} 的一阶路径构造子`
            );
        }
        const supplied = pathTerms.slice(1);
        const fullArgumentCount = parameters.length + firstPath.arguments.length;
        let arguments_: AST[];
        if (supplied.length === firstPath.arguments.length) {
            arguments_ = [
                ...parameters.map(parameter => sandboxVar(parameter.name)),
                ...supplied.map(argument => Core.clone(argument))
            ];
        } else if (supplied.length === fullArgumentCount) {
            for (let index = 0; index < parameters.length; index++) {
                const argument = supplied[index];
                if (argument?.type !== "var" || argument.name !== parameters[index].name) {
                    throw new Error(
                        `三阶路径构造子 ${pathName} 的 refl 端点必须保持统一参数 ${parameters[index].name}`
                    );
                }
            }
            arguments_ = supplied.map(argument => Core.clone(argument));
        } else {
            throw new Error(
                `三阶路径构造子 ${pathName} 的 refl 端点 ${firstPathName} 参数数量错误：`
                + `需要 ${firstPath.arguments.length} 个路径参数`
            );
        }
        const firstPathTerm = sandboxConstructorTerm(firstPath.name, arguments_);
        const argumentReplacements = new Map<string, AST>();
        firstPath.arguments.forEach((argument, index) => {
            argumentReplacements.set(argument.name, arguments_[parameters.length + index]);
        });
        return {
            expression: {
                kind: "refl",
                pathName: firstPath.name,
                arguments: arguments_.slice(parameters.length).map(argument => Core.clone(argument))
            },
            term: sandboxApply(sandboxVar("refl"), firstPathTerm),
            sourcePath: Core.clone(firstPathTerm),
            targetPath: Core.clone(firstPathTerm),
            sourcePoint: substituteSandboxFreeVars(firstPath.left, argumentReplacements),
            targetPoint: substituteSandboxFreeVars(firstPath.right, argumentReplacements),
            resultIndices: firstPath.resultIndices.map(index =>
                substituteSandboxFreeVars(index, argumentReplacements)
            )
        };
    }
    const headName = terms[0]?.type === "var" ? terms[0].name : "";
    if (boundNames.has(headName)) {
        throw new Error(`三阶路径构造子 ${pathName} 的端点 ${headName} 被局部参数遮蔽`);
    }
    const twoPath = twoPathConstructors.find(candidate => candidate.name === headName);
    if (!twoPath) {
        throw new Error(
            `三阶路径构造子 ${pathName} 的端点必须由 ${signatureName} 的二阶路径构造子形成`
        );
    }
    const supplied = terms.slice(1);
    const fullArgumentCount = parameters.length + twoPath.arguments.length;
    let arguments_: AST[];
    if (supplied.length === twoPath.arguments.length) {
        arguments_ = [
            ...parameters.map(parameter => sandboxVar(parameter.name)),
            ...supplied.map(argument => Core.clone(argument))
        ];
    } else if (supplied.length === fullArgumentCount) {
        for (let index = 0; index < parameters.length; index++) {
            const argument = supplied[index];
            if (argument?.type !== "var" || argument.name !== parameters[index].name) {
                throw new Error(
                    `三阶路径构造子 ${pathName} 的端点必须保持统一参数 ${parameters[index].name}`
                );
            }
        }
        arguments_ = supplied.map(argument => Core.clone(argument));
    } else {
        throw new Error(
            `三阶路径构造子 ${pathName} 的端点 ${headName} 参数数量错误：需要 ${twoPath.arguments.length} 个路径参数`
        );
    }
    const twoPathTerm = sandboxConstructorTerm(headName, arguments_);
    const argumentReplacements = new Map<string, AST>();
    twoPath.arguments.forEach((argument, index) => {
        argumentReplacements.set(argument.name, arguments_[parameters.length + index]);
    });
    return {
        expression: {
            kind: "atom",
            name: twoPath.name,
            arguments: arguments_.slice(parameters.length).map(argument => Core.clone(argument))
        },
        term: twoPathTerm,
        sourcePath: substituteSandboxFreeVars(twoPath.left, argumentReplacements),
        targetPath: substituteSandboxFreeVars(twoPath.right, argumentReplacements),
        sourcePoint: substituteSandboxFreeVars(twoPath.leftPoint, argumentReplacements),
        targetPoint: substituteSandboxFreeVars(twoPath.rightPoint, argumentReplacements),
        resultIndices: twoPath.resultIndices.map(index =>
            substituteSandboxFreeVars(index, argumentReplacements)
        )
    };
}

/** Parse a parameterized, non-indexed higher inductive declaration. */
export function parseSandboxHit(source: string): SandboxHitDeclaration {
    const text = normalizeSandboxSource(source);
    const inspection = inspectSandboxHitSource(text);
    if (inspection.firstUnsupportedPath) {
        const unsupported = inspection.firstUnsupportedPath;
        throw new Error(
            `当前沙盒最高只解析三维 HIT：第 ${unsupported.sectionIndex} 个路径构造段`
            + `（字符偏移 ${unsupported.offset}）不支持 path${unsupported.level}`
        );
    }
    const [rawHeader, ...rawConstructors] = splitInductiveSections(text);
    const header = new RegExp(String.raw`^hit\s+(${sandboxNamePattern})([\s\S]*)$`, "i")
        .exec(rawHeader);
    if (!header) {
        throw new Error("HIT 声明必须使用 hit 名称 [(参数 : 类型)] : Universe 格式");
    }
    const declaredName = header[1];
    const constructorParts = rawConstructors
        .map(part => part.trim())
        .filter(Boolean)
        .map(raw => {
            const twoPath = /^path2\s+/i.test(raw);
            const threePath = /^path3\s+/i.test(raw);
            const normalized = twoPath || threePath
                ? raw.replace(/^path[23]\s+/i, "")
                : raw;
            const match = new RegExp(
                String.raw`^(${sandboxNamePattern})\s*(?::\s*([\s\S]*))?$`
            ).exec(normalized);
            if (!match) throw new Error(`HIT 构造子格式错误：${raw}`);
            return {
                raw,
                normalized,
                name: match[1],
                typeSource: match[2]?.trim(),
                twoPath,
                threePath
            };
        });
    // ASTParser reserves leading P/S/W/L/X as binder tokens. Parse every
    // declaration-owned identifier through a fresh, source-absent alias so
    // names such as `Point` remain legal in path endpoints. Fresh aliases also
    // prevent the old fixed `_SandboxHitSelf` placeholder from capturing a
    // user declaration with that exact spelling.
    const aliases = sandboxHitParserAliases(
        text,
        [declaredName, ...constructorParts.map(part => part.name)]
    );
    const hideReferences = (value: string) => replaceSandboxIdentifiers(value, aliases.hidden);
    const restoreReferences = (ast: AST) => restoreSandboxParsedNames(ast, aliases.restored);
    const hiddenDeclaredName = aliases.hidden.get(declaredName)!;
    const hideDeclaredName = (value: string) => replaceSandboxIdentifiers(
        value,
        new Map([[declaredName, hiddenDeclaredName]])
    );

    const pointSections: string[] = [];
    const pathSections: { raw: string; name: string; type: AST; typeSource: string }[] = [];
    const twoPathSections: { raw: string; name: string; type: AST; typeSource: string }[] = [];
    const threePathSections: { raw: string; name: string; type: AST; typeSource: string }[] = [];
    let sawPath = false;
    let sawTwoPath = false;
    let sawThreePath = false;
    for (const part of constructorParts) {
        const constructorName = part.name;
        const typeSource = part.typeSource;
        if (!typeSource) {
            if (part.threePath) throw new Error("三阶路径构造子必须声明类型");
            if (part.twoPath) throw new Error("二阶路径构造子必须声明类型");
            if (sawPath || sawTwoPath || sawThreePath) {
                throw new Error("点构造子必须写在路径构造子之前");
            }
            pointSections.push(part.raw);
            continue;
        }
        let type: AST;
        try {
            type = restoreReferences(parser.parse(hideReferences(typeSource)));
        } catch (error) {
            throw new Error(`构造子 ${constructorName} 类型格式错误：${String(error)}`);
        }
        const tail = sandboxPathTelescope(type, constructorName).body;
        if (part.threePath) {
            if (!sawTwoPath) throw new Error("三阶路径构造子必须写在二阶路径构造子之后");
            if (tail.type !== "=") throw new Error(`三阶路径构造子 ${constructorName} 必须以等式为结论`);
            sawThreePath = true;
            threePathSections.push({ raw: part.normalized, name: constructorName, type, typeSource });
        } else if (part.twoPath) {
            if (!sawPath) throw new Error("二阶路径构造子必须写在一阶路径构造子之后");
            if (sawThreePath) throw new Error("二阶路径构造子必须写在三阶路径构造子之前");
            if (tail.type !== "=") throw new Error(`二阶路径构造子 ${constructorName} 必须以等式为结论`);
            sawTwoPath = true;
            twoPathSections.push({ raw: part.normalized, name: constructorName, type, typeSource });
        } else if (tail.type === "=") {
            if (sawTwoPath || sawThreePath) {
                throw new Error("一阶路径构造子必须写在高阶路径构造子之前");
            }
            sawPath = true;
            pathSections.push({ raw: part.raw, name: constructorName, type, typeSource });
        } else {
            if (sawPath || sawTwoPath || sawThreePath) {
                throw new Error("点构造子必须写在路径构造子之前");
            }
            pointSections.push(part.raw);
        }
    }
    if (!pathSections.length) throw new Error("HIT 至少需要一个一阶路径构造子");

    const ordinarySource = hideDeclaredName([
        rawHeader.replace(/^hit\b/i, "inductive"),
        ...pointSections
    ].join(" | "));
    const internalOrdinary = parseSandboxInductive(ordinarySource);
    const ordinary: SandboxInductiveDeclaration = {
        ...internalOrdinary,
        name: declaredName,
        parameters: internalOrdinary.parameters.map(parameter => ({
            ...parameter,
            type: restoreReferences(parameter.type)
        })),
        indices: internalOrdinary.indices.map(index => ({
            ...index,
            type: restoreReferences(index.type)
        })),
        universeAst: restoreReferences(internalOrdinary.universeAst),
        constructors: internalOrdinary.constructors.map(constructor => {
            const type = restoreReferences(constructor.type);
            return {
                ...constructor,
                type,
                typeSource: parser.stringify(type),
                argumentAsts: constructor.argumentAsts.map(argument => {
                    const argumentType = restoreReferences(argument.type);
                    return {
                        ...argument,
                        type: argumentType,
                        typeSource: parser.stringify(argumentType),
                        recursiveTelescope: argument.recursiveTelescope?.map(binder => {
                            const binderType = restoreReferences(binder.type);
                            return {
                                ...binder,
                                type: binderType,
                                typeSource: parser.stringify(binderType)
                            };
                        }) ?? null,
                        recursiveResultIndices: argument.recursiveResultIndices?.map(restoreReferences) ?? null
                    };
                }),
                result: restoreReferences(constructor.result),
                resultIndices: constructor.resultIndices.map(restoreReferences)
            };
        })
    };
    const names = new Set([ordinary.name, ...ordinary.constructors.map(constructor => constructor.name)]);
    const parameterNames = new Set(ordinary.parameters.map(parameter => parameter.name));
    const pathConstructors: SandboxHitPathConstructor[] = [];
    for (const path of pathSections) {
        if (names.has(path.name)) throw new Error(`HIT 构造子名称冲突：${path.name}`);
        names.add(path.name);
        const { arguments: arguments_, body } = sandboxPathTelescope(path.type, path.name);
        if (body.type !== "=" || !body.nodes?.[0] || !body.nodes?.[1]) {
            throw new Error(`路径构造子 ${path.name} 必须以等式为结论`);
        }
        for (const argument of arguments_) {
            if (parameterNames.has(argument.name)) {
                throw new Error(`路径构造子 ${path.name} 的参数不能遮蔽统一参数：${argument.name}`);
            }
            if (containsSandboxName(argument.type, ordinary.name)) {
                throw new Error(`路径构造子 ${path.name} 的参数不能递归引用 ${ordinary.name}`);
            }
        }
        const endpointBoundNames = new Set([
            ...ordinary.parameters.map(parameter => parameter.name),
            ...arguments_.map(argument => argument.name)
        ]);
        const left = elaborateHitEndpoint(
            body.nodes[0], ordinary.name, ordinary.parameters, ordinary.constructors, path.name,
            endpointBoundNames
        );
        const right = elaborateHitEndpoint(
            body.nodes[1], ordinary.name, ordinary.parameters, ordinary.constructors, path.name,
            endpointBoundNames
        );
        // Keep the left endpoint's indices as canonical metadata.  Syntactic
        // inequality is not enough to reject the path: Core performs the final
        // bounded NbE equality check after all ambient definitions are loaded.
        const elaboratedType = sandboxWrapPis(arguments_, {
            type: "=",
            name: "",
            nodes: [Core.clone(left.term), Core.clone(right.term)]
        });
        pathConstructors.push({
            name: path.name,
            arguments: arguments_,
            type: elaboratedType,
            typeSource: parser.stringify(elaboratedType),
            left: left.term,
            right: right.term,
            resultIndices: left.resultIndices.map(index => Core.clone(index))
        });
    }
    const twoPathConstructors: SandboxHitTwoPathConstructor[] = [];
    for (const path2 of twoPathSections) {
        if (names.has(path2.name)) throw new Error(`HIT 构造子名称冲突：${path2.name}`);
        names.add(path2.name);
        const { arguments: arguments_, body } = sandboxPathTelescope(path2.type, path2.name);
        if (body.type !== "=" || !body.nodes?.[0] || !body.nodes?.[1]) {
            throw new Error(`二阶路径构造子 ${path2.name} 必须以等式为结论`);
        }
        for (const argument of arguments_) {
            if (parameterNames.has(argument.name)) {
                throw new Error(`二阶路径构造子 ${path2.name} 的参数不能遮蔽统一参数：${argument.name}`);
            }
            if (containsSandboxName(argument.type, ordinary.name)) {
                throw new Error(`二阶路径构造子 ${path2.name} 的参数不能递归引用 ${ordinary.name}`);
            }
        }
        const endpointBoundNames = new Set([
            ...ordinary.parameters.map(parameter => parameter.name),
            ...arguments_.map(argument => argument.name)
        ]);
        const left = elaborateHitTwoPathEndpoint(
            body.nodes[0], ordinary.name, ordinary.parameters, ordinary.constructors,
            pathConstructors, path2.name, endpointBoundNames
        );
        const right = elaborateHitTwoPathEndpoint(
            body.nodes[1], ordinary.name, ordinary.parameters, ordinary.constructors,
            pathConstructors, path2.name, endpointBoundNames
        );
        if (!ordinary.indices.length
            && (!sameSandboxAst(left.sourcePoint, right.sourcePoint)
                || !sameSandboxAst(left.targetPoint, right.targetPoint))) {
            throw new Error(`二阶路径构造子 ${path2.name} 的一阶路径端点不一致`);
        }
        if (ordinary.indices.length) {
            if (left.resultIndices.length !== ordinary.indices.length
                || right.resultIndices.length !== ordinary.indices.length) {
                throw new Error(`索引 HIT 二阶路径构造子 ${path2.name} 的端点索引纤维不一致`);
            }
        }
        const elaboratedType = sandboxWrapPis(arguments_, sandboxEquality(
            Core.clone(left.term), Core.clone(right.term)
        ));
        twoPathConstructors.push({
            name: path2.name,
            arguments: arguments_,
            type: elaboratedType,
            typeSource: parser.stringify(elaboratedType),
            left: left.term,
            right: right.term,
            leftExpression: left.expression,
            rightExpression: right.expression,
            leftPoint: left.sourcePoint,
            rightPoint: right.targetPoint,
            resultIndices: left.resultIndices.map(index => Core.clone(index))
        });
    }
    const threePathConstructors: SandboxHitThreePathConstructor[] = [];
    for (const path3 of threePathSections) {
        if (names.has(path3.name)) throw new Error(`HIT 构造子名称冲突：${path3.name}`);
        names.add(path3.name);
        const { arguments: arguments_, body } = sandboxPathTelescope(path3.type, path3.name);
        if (body.type !== "=" || !body.nodes?.[0] || !body.nodes?.[1]) {
            throw new Error(`三阶路径构造子 ${path3.name} 必须以等式为结论`);
        }
        for (const argument of arguments_) {
            if (parameterNames.has(argument.name)) {
                throw new Error(`三阶路径构造子 ${path3.name} 的参数不能遮蔽统一参数：${argument.name}`);
            }
            if (containsSandboxName(argument.type, ordinary.name)) {
                throw new Error(`三阶路径构造子 ${path3.name} 的参数不能递归引用 ${ordinary.name}`);
            }
        }
        const endpointBoundNames = new Set([
            ...ordinary.parameters.map(parameter => parameter.name),
            ...arguments_.map(argument => argument.name)
        ]);
        const left = elaborateHitThreePathEndpoint(
            body.nodes[0], ordinary.name, ordinary.parameters,
            pathConstructors, twoPathConstructors, path3.name, endpointBoundNames
        );
        const right = elaborateHitThreePathEndpoint(
            body.nodes[1], ordinary.name, ordinary.parameters,
            pathConstructors, twoPathConstructors, path3.name, endpointBoundNames
        );
        if (!ordinary.indices.length) {
            if (!sameSandboxAst(left.sourcePath, right.sourcePath)
                || !sameSandboxAst(left.targetPath, right.targetPath)) {
                throw new Error(`三阶路径构造子 ${path3.name} 的二阶路径边界不一致`);
            }
            if (!sameSandboxAst(left.sourcePoint, right.sourcePoint)
                || !sameSandboxAst(left.targetPoint, right.targetPoint)) {
                throw new Error(`三阶路径构造子 ${path3.name} 的一阶路径边界不一致`);
            }
        } else {
            if (left.expression.kind !== "atom" || right.expression.kind !== "atom") {
                throw new Error(
                    `索引 HIT 三阶路径构造子 ${path3.name} 目前只支持原子二阶路径端点`
                );
            }
            if (left.resultIndices.length !== ordinary.indices.length
                || right.resultIndices.length !== ordinary.indices.length) {
                throw new Error(`索引 HIT 三阶路径构造子 ${path3.name} 的端点索引纤维不一致`);
            }
        }
        const elaboratedType = sandboxWrapPis(arguments_, sandboxEquality(
            Core.clone(left.term), Core.clone(right.term)
        ));
        threePathConstructors.push({
            name: path3.name,
            arguments: arguments_,
            type: elaboratedType,
            typeSource: parser.stringify(elaboratedType),
            left: left.term,
            right: right.term,
            leftExpression: left.expression,
            rightExpression: right.expression,
            leftTwoPath: left.expression.kind === "atom" ? left.expression.name : "",
            rightTwoPath: right.expression.kind === "atom" ? right.expression.name : "",
            sourcePath: left.sourcePath,
            targetPath: left.targetPath,
            sourcePoint: left.sourcePoint,
            targetPoint: left.targetPoint,
            resultIndices: left.resultIndices.map(index => Core.clone(index))
        });
    }
    return {
        name: ordinary.name,
        parameters: ordinary.parameters,
        indices: ordinary.indices,
        universe: ordinary.universe,
        universeAst: ordinary.universeAst,
        pointConstructors: ordinary.constructors,
        pathLevels: createHitPathLevels(
            pathConstructors,
            twoPathConstructors,
            threePathConstructors
        )
    };
}

function sameSandboxAst(left: AST, right: AST): boolean {
    if (!left || !right || left.type !== right.type || left.name !== right.name) return false;
    const leftNodes = left.nodes ?? [];
    const rightNodes = right.nodes ?? [];
    return leftNodes.length === rightNodes.length
        && leftNodes.every((node, index) => sameSandboxAst(node, rightNodes[index]));
}

function containsSandboxName(ast: AST, name: string): boolean {
    if (!ast) return false;
    if (ast.type === "var") return ast.name === name;
    return (ast.nodes ?? []).some(child => containsSandboxName(child, name));
}

function sandboxVar(name: string): AST {
    return { type: "var", name, nodes: [] };
}

function sandboxApply(...terms: AST[]): AST {
    let result = terms[0];
    for (let index = 1; index < terms.length; index++) {
        result = { type: "apply", name: "", nodes: [result, terms[index]] };
    }
    return result;
}

function sandboxArrow(domain: AST, codomain: AST): AST {
    return { type: "->", name: "", nodes: [domain, codomain] };
}

function sandboxPi(name: string, domain: AST, body: AST): AST {
    return { type: "P", name, nodes: [domain, body] };
}

function sandboxConstructorTerm(name: string, arguments_: AST[]): AST {
    return sandboxApply(sandboxVar(name), ...arguments_);
}

function sandboxWrapPis(
    binders: readonly Pick<SandboxInductiveBinder, "name" | "type">[],
    body: AST
) {
    let result = body;
    for (let index = binders.length - 1; index >= 0; index--) {
        result = sandboxPi(binders[index].name, Core.clone(binders[index].type), result);
    }
    return result;
}

function sandboxLambda(name: string, domain: AST, body: AST): AST {
    return { type: "L", name, nodes: [domain, body] };
}

function sandboxWrapLambdas(
    binders: readonly Pick<SandboxInductiveBinder, "name" | "type">[],
    body: AST
) {
    let result = body;
    for (let index = binders.length - 1; index >= 0; index--) {
        result = sandboxLambda(binders[index].name, Core.clone(binders[index].type), result);
    }
    return result;
}

function sandboxFreshName(base: string, used: Set<string>) {
    let candidate = base;
    for (let suffix = 1; used.has(candidate); suffix++) candidate = `${base}${suffix}`;
    used.add(candidate);
    return candidate;
}

function sandboxInductionHypothesisName(argumentName: string) {
    const generated = /^a(\d+)_(\d+)$/.exec(argumentName);
    return generated ? `ih${generated[1]}_${generated[2]}` : `${argumentName}_ih`;
}

function sandboxRecursiveValue(argument: AST, telescope: readonly SandboxInductiveBinder[]) {
    return sandboxApply(
        Core.clone(argument),
        ...telescope.map(binder => sandboxVar(binder.name))
    );
}

function sandboxRecursiveHypothesisType(
    motiveName: string,
    argument: AST,
    telescope: readonly SandboxInductiveBinder[],
    resultIndices: readonly AST[]
) {
    return sandboxWrapPis(
        telescope,
        sandboxApply(
            sandboxVar(motiveName),
            ...resultIndices.map(index => Core.clone(index)),
            sandboxRecursiveValue(argument, telescope)
        )
    );
}

function sandboxRecursiveCall(
    recursionHead: AST,
    argument: AST,
    telescope: readonly SandboxInductiveBinder[],
    resultIndices: readonly AST[]
) {
    return sandboxWrapLambdas(
        telescope,
        sandboxApply(
            Core.clone(recursionHead),
            ...resultIndices.map(index => Core.clone(index)),
            sandboxRecursiveValue(argument, telescope)
        )
    );
}

/** Lower a validated ordinary signature to Core's trusted system bundle. */
export function lowerSandboxInductive(signature: SandboxInductiveDeclaration): SandboxInductiveBundle {
    const typeName = signature.name;
    const parameterVars = signature.parameters.map(parameter => sandboxVar(parameter.name));
    const indexVars = signature.indices.map(index => sandboxVar(index.name));
    const inductiveType = sandboxApply(sandboxVar(typeName), ...parameterVars, ...indexVars);
    const constructorEntries: [string, AST][] = [];
    const metadataConstructors: SandboxInductiveMetadata["constructors"] = [];
    const generatedScope = new Set([
        ...signature.parameters.map(parameter => parameter.name),
        ...signature.indices.map(index => index.name),
        ...signature.constructors.flatMap(constructor => constructor.argumentAsts.map(argument => argument.name))
    ]);
    const motiveName = sandboxFreshName("C", generatedScope);
    const motiveUniverseName = sandboxFreshName("u", generatedScope);
    const resultName = sandboxFreshName("x", generatedScope);
    const branchNames = signature.constructors.map((_, index) =>
        sandboxFreshName(`c${index}`, generatedScope)
    );
    const branchTypes: AST[] = [];
    const recursorBranchNames = signature.constructors.map((_, index) =>
        sandboxFreshName(`r${index}`, generatedScope)
    );
    const recursorBranchTypes: AST[] = [];

    for (const ctor of signature.constructors) {
        metadataConstructors.push({
            name: ctor.name,
            argumentTypes: ctor.argumentAsts.map(argument => Core.clone(argument.type)),
            argumentNames: ctor.argumentAsts.map(argument => argument.name),
            recursiveArguments: ctor.argumentAsts.flatMap((argument, index) =>
                argument.recursiveTelescope
                    ? [{
                        index,
                        telescope: argument.recursiveTelescope.map(binder => ({
                            name: binder.name,
                            type: Core.clone(binder.type)
                        })),
                        resultIndices: (argument.recursiveResultIndices ?? [])
                            .map(resultIndex => Core.clone(resultIndex))
                    }]
                    : []
            ),
            resultIndices: ctor.resultIndices.map(index => Core.clone(index))
        });
        const ctorType = sandboxWrapPis(
            [...signature.parameters, ...ctor.argumentAsts],
            Core.clone(ctor.result)
        );
        constructorEntries.push([ctor.name, ctorType]);
    }

    const motive = sandboxWrapPis(
        signature.indices,
        sandboxArrow(
            Core.clone(inductiveType),
            sandboxApply(sandboxVar("U"), sandboxVar(motiveUniverseName))
        )
    );
    for (let ctorIndex = 0; ctorIndex < signature.constructors.length; ctorIndex++) {
        const ctor = signature.constructors[ctorIndex];
        const argumentVars = ctor.argumentAsts.map(argument => sandboxVar(argument.name));
        let branch: AST = sandboxApply(
            sandboxVar(motiveName),
            ...ctor.resultIndices.map(index => Core.clone(index)),
            sandboxConstructorTerm(ctor.name, [...parameterVars, ...argumentVars])
        );
        const branchScope = new Set(generatedScope);
        for (let index = ctor.argumentAsts.length - 1; index >= 0; index--) {
            const argument = ctor.argumentAsts[index];
            const recursive = argument.recursiveTelescope;
            if (recursive) {
                branch = sandboxPi(
                    sandboxFreshName(sandboxInductionHypothesisName(argument.name), branchScope),
                    sandboxRecursiveHypothesisType(
                        motiveName,
                        argumentVars[index],
                        recursive,
                        argument.recursiveResultIndices ?? []
                    ),
                    branch
                );
            }
            branch = sandboxPi(argument.name, Core.clone(argument.type), branch);
        }
        branchTypes.push(branch);

        let recursorBranch: AST = sandboxVar(motiveName);
        const recursorBranchScope = new Set(generatedScope);
        for (let index = ctor.argumentAsts.length - 1; index >= 0; index--) {
            const argument = ctor.argumentAsts[index];
            const recursive = argument.recursiveTelescope;
            if (recursive) {
                recursorBranch = sandboxPi(
                    sandboxFreshName(sandboxInductionHypothesisName(argument.name), recursorBranchScope),
                    sandboxWrapPis(recursive, sandboxVar(motiveName)),
                    recursorBranch
                );
            }
            recursorBranch = sandboxPi(
                argument.name,
                Core.clone(argument.type),
                recursorBranch
            );
        }
        recursorBranchTypes.push(recursorBranch);
    }

    let fullEliminatorType: AST = sandboxWrapPis(
        signature.indices,
        sandboxPi(
            resultName,
            Core.clone(inductiveType),
            sandboxApply(sandboxVar(motiveName), ...indexVars, sandboxVar(resultName))
        )
    );
    for (let index = branchTypes.length - 1; index >= 0; index--) {
        fullEliminatorType = sandboxPi(branchNames[index], branchTypes[index], fullEliminatorType);
    }
    fullEliminatorType = sandboxPi(
        motiveName,
        motive,
        fullEliminatorType
    );
    fullEliminatorType = sandboxWrapPis(signature.parameters, fullEliminatorType);
    fullEliminatorType = sandboxPi(motiveUniverseName, sandboxVar("U@"), fullEliminatorType);

    const publicMotive = sandboxWrapPis(
        signature.indices,
        sandboxArrow(
            Core.clone(inductiveType),
            sandboxApply(sandboxVar("U"), sandboxVar("@0"))
        )
    );
    let publicEliminatorType: AST = sandboxWrapPis(
        signature.indices,
        sandboxPi(
            resultName,
            Core.clone(inductiveType),
            sandboxApply(sandboxVar(motiveName), ...indexVars, sandboxVar(resultName))
        )
    );
    for (let index = branchTypes.length - 1; index >= 0; index--) {
        publicEliminatorType = sandboxPi(branchNames[index], branchTypes[index], publicEliminatorType);
    }
    // The motive must bind the branch methods and the final result.  Putting
    // `C` outside the branch binders keeps every `C <constructor>` occurrence
    // in scope (the previous order left C free and was rejected by Core).
    publicEliminatorType = sandboxPi(motiveName, publicMotive, publicEliminatorType);
    publicEliminatorType = sandboxWrapPis(signature.parameters, publicEliminatorType);

    let fullRecursorType: AST = sandboxWrapPis(
        signature.indices,
        sandboxPi(
            resultName,
            Core.clone(inductiveType),
            sandboxVar(motiveName)
        )
    );
    for (let index = recursorBranchTypes.length - 1; index >= 0; index--) {
        fullRecursorType = sandboxPi(
            recursorBranchNames[index],
            recursorBranchTypes[index],
            fullRecursorType
        );
    }
    fullRecursorType = sandboxPi(
        motiveName,
        sandboxApply(sandboxVar("U"), sandboxVar(motiveUniverseName)),
        fullRecursorType
    );
    fullRecursorType = sandboxWrapPis(signature.parameters, fullRecursorType);
    fullRecursorType = sandboxPi(motiveUniverseName, sandboxVar("U@"), fullRecursorType);

    let publicRecursorType: AST = sandboxWrapPis(
        signature.indices,
        sandboxPi(
            resultName,
            Core.clone(inductiveType),
            sandboxVar(motiveName)
        )
    );
    for (let index = recursorBranchTypes.length - 1; index >= 0; index--) {
        publicRecursorType = sandboxPi(
            recursorBranchNames[index],
            recursorBranchTypes[index],
            publicRecursorType
        );
    }
    publicRecursorType = sandboxPi(
        motiveName,
        sandboxApply(sandboxVar("U"), sandboxVar("@0")),
        publicRecursorType
    );
    publicRecursorType = sandboxWrapPis(signature.parameters, publicRecursorType);

    const computeRules: Record<string, { pattern: AST[]; result: AST }[]> = {
        [`ind_${typeName}`]: [],
        [`@ind_${typeName}`]: [],
        [`rec_${typeName}`]: [],
        [`@rec_${typeName}`]: []
    };
    for (let ctorIndex = 0; ctorIndex < signature.constructors.length; ctorIndex++) {
        const ctor = signature.constructors[ctorIndex];
        const parameterPatterns = signature.parameters.map((_, index) => sandboxVar(`?p${index}`));
        const argumentVars = ctor.argumentAsts.map((_, index) => sandboxVar(`?a${ctorIndex}_${index}`));
        const patternReplacements = new Map<string, string>();
        signature.parameters.forEach((parameter, index) =>
            patternReplacements.set(parameter.name, parameterPatterns[index].name)
        );
        ctor.argumentAsts.forEach((argument, index) =>
            patternReplacements.set(argument.name, argumentVars[index].name)
        );
        const recursivePatternTelescope = (telescope: readonly SandboxInductiveBinder[]) =>
            telescope.map(binder => ({
                ...binder,
                type: renameFreeInductiveNames(binder.type, patternReplacements)
            }));
        const resultIndexPatterns = ctor.resultIndices.map(index =>
            renameFreeInductiveNames(index, patternReplacements)
        );
        const method = sandboxVar(`?${branchNames[ctorIndex]}`);
        let result = method;
        const methodArgs: AST[] = [];
        const publicInductionHead = sandboxApply(
            sandboxVar(`ind_${typeName}`),
            ...parameterPatterns,
            sandboxVar(`?${motiveName}`),
            ...branchNames.map(name => sandboxVar(`?${name}`))
        );
        const fullInductionHead = sandboxApply(
            sandboxVar(`@ind_${typeName}`),
            sandboxVar(`?${motiveUniverseName}`),
            ...parameterPatterns,
            sandboxVar(`?${motiveName}`),
            ...branchNames.map(name => sandboxVar(`?${name}`))
        );
        for (let index = 0; index < ctor.argumentAsts.length; index++) {
            methodArgs.push(Core.clone(argumentVars[index]));
            const recursive = ctor.argumentAsts[index].recursiveTelescope;
            if (recursive) {
                methodArgs.push(sandboxRecursiveCall(
                    publicInductionHead,
                    argumentVars[index],
                    recursivePatternTelescope(recursive),
                    (ctor.argumentAsts[index].recursiveResultIndices ?? []).map(resultIndex =>
                        renameFreeInductiveNames(resultIndex, patternReplacements)
                    )
                ));
            }
        }
        if (methodArgs.length) result = sandboxApply(method, ...methodArgs);
        const ctorTerm = sandboxConstructorTerm(
            ctor.name,
            [...parameterPatterns, ...argumentVars]
        );
        const publicPattern = [
            sandboxVar(`ind_${typeName}`),
            ...parameterPatterns,
            sandboxVar(`?${motiveName}`),
            ...branchNames.map(name => sandboxVar(`?${name}`)),
            ...resultIndexPatterns.map(index => Core.clone(index)),
            ctorTerm
        ];
        computeRules[`ind_${typeName}`].push({ pattern: publicPattern, result });
        const fullMethodArgs: AST[] = [];
        for (let index = 0; index < ctor.argumentAsts.length; index++) {
            fullMethodArgs.push(Core.clone(argumentVars[index]));
            const recursive = ctor.argumentAsts[index].recursiveTelescope;
            if (recursive) {
                fullMethodArgs.push(sandboxRecursiveCall(
                    fullInductionHead,
                    argumentVars[index],
                    recursivePatternTelescope(recursive),
                    (ctor.argumentAsts[index].recursiveResultIndices ?? []).map(resultIndex =>
                        renameFreeInductiveNames(resultIndex, patternReplacements)
                    )
                ));
            }
        }
        const fullResult = fullMethodArgs.length
            ? sandboxApply(Core.clone(method), ...fullMethodArgs)
            : Core.clone(method);
        computeRules[`@ind_${typeName}`].push({
            pattern: [
                sandboxVar(`@ind_${typeName}`),
                sandboxVar(`?${motiveUniverseName}`),
                ...publicPattern.slice(1)
            ],
            result: fullResult
        });

        const recursorMethod = sandboxVar(`?${recursorBranchNames[ctorIndex]}`);
        const publicRecursorArgs: AST[] = [];
        const fullRecursorArgs: AST[] = [];
        const publicRecursorHead = sandboxApply(
            sandboxVar(`rec_${typeName}`),
            ...parameterPatterns,
            sandboxVar(`?${motiveName}`),
            ...recursorBranchNames.map(name => sandboxVar(`?${name}`))
        );
        const fullRecursorHead = sandboxApply(
            sandboxVar(`@rec_${typeName}`),
            sandboxVar(`?${motiveUniverseName}`),
            ...parameterPatterns,
            sandboxVar(`?${motiveName}`),
            ...recursorBranchNames.map(name => sandboxVar(`?${name}`))
        );
        for (let index = 0; index < ctor.argumentAsts.length; index++) {
            publicRecursorArgs.push(Core.clone(argumentVars[index]));
            fullRecursorArgs.push(Core.clone(argumentVars[index]));
            const recursive = ctor.argumentAsts[index].recursiveTelescope;
            if (recursive) {
                publicRecursorArgs.push(sandboxRecursiveCall(
                    publicRecursorHead,
                    argumentVars[index],
                    recursivePatternTelescope(recursive),
                    (ctor.argumentAsts[index].recursiveResultIndices ?? []).map(resultIndex =>
                        renameFreeInductiveNames(resultIndex, patternReplacements)
                    )
                ));
                fullRecursorArgs.push(sandboxRecursiveCall(
                    fullRecursorHead,
                    argumentVars[index],
                    recursivePatternTelescope(recursive),
                    (ctor.argumentAsts[index].recursiveResultIndices ?? []).map(resultIndex =>
                        renameFreeInductiveNames(resultIndex, patternReplacements)
                    )
                ));
            }
        }
        const publicRecursorResult = publicRecursorArgs.length
            ? sandboxApply(Core.clone(recursorMethod), ...publicRecursorArgs)
            : Core.clone(recursorMethod);
        const fullRecursorResult = fullRecursorArgs.length
            ? sandboxApply(Core.clone(recursorMethod), ...fullRecursorArgs)
            : Core.clone(recursorMethod);
        const recursorTail = [
            ...parameterPatterns,
            sandboxVar(`?${motiveName}`),
            ...recursorBranchNames.map(name => sandboxVar(`?${name}`)),
            ...resultIndexPatterns.map(index => Core.clone(index)),
            Core.clone(ctorTerm)
        ];
        computeRules[`rec_${typeName}`].push({
            pattern: [sandboxVar(`rec_${typeName}`), ...recursorTail],
            result: publicRecursorResult
        });
        computeRules[`@rec_${typeName}`].push({
            pattern: [
                sandboxVar(`@rec_${typeName}`),
                sandboxVar(`?${motiveUniverseName}`),
                ...recursorTail
            ],
            result: fullRecursorResult
        });
    }

    const generatedNames = [
        typeName,
        ...constructorEntries.map(([name]) => name),
        `ind_${typeName}`,
        `@ind_${typeName}`,
        `rec_${typeName}`,
        `@rec_${typeName}`
    ];
    return {
        type: [
            typeName,
            sandboxWrapPis(
                [...signature.parameters, ...signature.indices],
                Core.clone(signature.universeAst)
            )
        ],
        constructors: constructorEntries,
        auxiliaryTypes: [
            [`@ind_${typeName}`, fullEliminatorType],
            [`@rec_${typeName}`, fullRecursorType]
        ],
        eliminator: [`ind_${typeName}`, publicEliminatorType],
        recursor: [`rec_${typeName}`, publicRecursorType],
        computeRules,
        metadata: {
            version: 2,
            ruleSchemaVersion: 1,
            typeName,
            parameterCount: signature.parameters.length,
            indexCount: signature.indices.length,
            indices: signature.indices.map(index => ({
                name: index.name,
                type: Core.clone(index.type)
            })),
            eliminatorName: `ind_${typeName}`,
            fullEliminatorName: `@ind_${typeName}`,
            recursorName: `rec_${typeName}`,
            fullRecursorName: `@rec_${typeName}`,
            constructors: metadataConstructors
        },
        generatedNames
    } as SandboxInductiveBundle;
}

function sandboxInsertPis(type: AST, depth: number, binders: readonly SandboxInductiveBinder[]) {
    const root = Core.clone(type);
    let cursor = root;
    for (let index = 0; index < depth; index++) {
        if ((cursor.type !== "P" && cursor.type !== "->") || !cursor.nodes?.[1]) {
            throw new Error("HIT 消去器类型结构与点构造 lowering 不一致");
        }
        cursor = cursor.nodes[1];
    }
    const tail = Core.clone(cursor);
    const replacement = sandboxWrapPis(binders, tail);
    Object.assign(cursor, replacement);
    return root;
}

function sandboxHitBranchValue(
    endpoint: AST,
    parameters: readonly SandboxInductiveBinder[],
    pointConstructors: readonly SandboxInductiveConstructor[],
    branchNames: readonly string[],
    state = { nodes: 0 },
    depth = 0
) {
    if (depth > 128) throw new Error("HIT 点端点构造表达式嵌套过深");
    if (++state.nodes > 4_096) throw new Error("HIT 点端点构造表达式节点过多");
    const terms = flattenApplication(endpoint);
    const constructorName = terms[0]?.name;
    const constructorIndex = pointConstructors.findIndex(ctor => ctor.name === constructorName);
    if (constructorIndex < 0) throw new Error(`未知的 HIT 点构造子端点：${constructorName || ""}`);
    const constructor = pointConstructors[constructorIndex];
    const supplied = terms.slice(1);
    const localCount = constructor.argumentAsts.length;
    const fullCount = parameters.length + localCount;
    let arguments_: AST[];
    if (supplied.length === localCount) {
        arguments_ = supplied.map(argument => Core.clone(argument));
    } else if (supplied.length === fullCount) {
        for (let index = 0; index < parameters.length; index++) {
            if (!sameSandboxAst(supplied[index], sandboxVar(parameters[index].name))) {
                throw new Error(
                    `HIT 点端点 ${constructorName} 未保持统一参数 ${parameters[index].name}`
                );
            }
        }
        arguments_ = supplied.slice(parameters.length).map(argument => Core.clone(argument));
    } else {
        throw new Error(
            `HIT 点端点 ${constructorName} 参数数量错误：需要 ${localCount} 个点参数`
        );
    }
    const methodArguments: AST[] = [];
    for (let index = 0; index < constructor.argumentAsts.length; index++) {
        const argument = arguments_[index];
        methodArguments.push(Core.clone(argument));
        const recursive = constructor.argumentAsts[index].recursiveTelescope;
        if (!recursive) continue;
        if (recursive.length) {
            throw new Error(
                `HIT 路径端点暂不支持函数型递归点参数：${constructorName}.${constructor.argumentAsts[index].name}`
            );
        }
        methodArguments.push(sandboxHitBranchValue(
            argument,
            parameters,
            pointConstructors,
            branchNames,
            state,
            depth + 1
        ));
    }
    return methodArguments.length
        ? sandboxApply(sandboxVar(branchNames[constructorIndex]), ...methodArguments)
        : sandboxVar(branchNames[constructorIndex]);
}

function sandboxHitFiberType(
    signature: Pick<SandboxHitDeclaration, "name" | "parameters">,
    resultIndices: readonly AST[]
) {
    return sandboxApply(
        sandboxVar(signature.name),
        ...signature.parameters.map(parameter => sandboxVar(parameter.name)),
        ...resultIndices.map(index => Core.clone(index))
    );
}

function sandboxHitFiberMotive(
    signature: Pick<SandboxHitDeclaration, "name" | "parameters">,
    motiveName: string,
    resultIndices: readonly AST[]
) {
    if (!resultIndices.length) return sandboxVar(motiveName);
    const occupied = new Set<string>([
        signature.name,
        motiveName,
        ...signature.parameters.map(parameter => parameter.name)
    ]);
    for (const index of resultIndices) collectSandboxAstNames(index, occupied);
    const valueName = sandboxFreshName("fiberValue", occupied);
    return sandboxLambda(
        valueName,
        sandboxHitFiberType(signature, resultIndices),
        sandboxApply(
            sandboxVar(motiveName),
            ...resultIndices.map(index => Core.clone(index)),
            sandboxVar(valueName)
        )
    );
}

function sandboxHitHeadAtIndices(head: AST, resultIndices: readonly AST[]) {
    return resultIndices.length
        ? sandboxApply(
            Core.clone(head),
            ...resultIndices.map(index => Core.clone(index))
        )
        : Core.clone(head);
}

function sandboxHitPathMethodValue(
    endpoint: AST,
    parameters: readonly SandboxInductiveBinder[],
    pathConstructors: readonly SandboxHitPathConstructor[],
    methodNames: readonly string[],
    owner: string
) {
    const terms = flattenApplication(endpoint);
    const pathName = terms[0]?.type === "var" ? terms[0].name : "";
    const pathIndex = pathConstructors.findIndex(path => path.name === pathName);
    if (pathIndex < 0) throw new Error(`未知的二维 HIT 一阶路径端点：${pathName || owner}`);
    const arguments_ = terms.slice(1 + parameters.length).map(argument => Core.clone(argument));
    return sandboxApply(sandboxVar(methodNames[pathIndex]), ...arguments_);
}

function sandboxHitOnePathExpressionData(
    expression: SandboxHitOnePathExpression,
    parameters: readonly SandboxInductiveBinder[],
    pathConstructors: readonly SandboxHitPathConstructor[],
    owner: string
): { term: AST; sourcePoint: AST; targetPoint: AST; pathIndex?: number; arguments_?: AST[] } {
    if (expression.kind === "compose") {
        const left = sandboxHitOnePathExpressionData(
            expression.left, parameters, pathConstructors, owner
        );
        const right = sandboxHitOnePathExpressionData(
            expression.right, parameters, pathConstructors, owner
        );
        if (!sameSandboxAst(left.targetPoint, right.sourcePoint)) {
            throw new Error(`二维 HIT 一阶路径表达式 ${owner} 的组合中间点边界不一致`);
        }
        return {
            term: sandboxCompose(left.term, right.term),
            sourcePoint: left.sourcePoint,
            targetPoint: right.targetPoint
        };
    }
    if (expression.kind === "inverse") {
        const value = sandboxHitOnePathExpressionData(
            expression.value, parameters, pathConstructors, owner
        );
        return {
            term: sandboxApply(sandboxVar("inveq"), value.term),
            sourcePoint: value.targetPoint,
            targetPoint: value.sourcePoint
        };
    }
    const pathIndex = pathConstructors.findIndex(path => path.name === expression.name);
    if (pathIndex < 0) {
        throw new Error(`未知的二维 HIT 一阶路径端点：${expression.name || owner}`);
    }
    const path = pathConstructors[pathIndex];
    if (expression.arguments.length !== path.arguments.length) {
        throw new Error(`二维 HIT 一阶路径端点 ${expression.name} 的参数数量与 metadata 不一致`);
    }
    const arguments_ = expression.arguments.map(argument => Core.clone(argument));
    const replacements = new Map<string, AST>();
    path.arguments.forEach((argument, index) => replacements.set(argument.name, arguments_[index]));
    return {
        term: sandboxConstructorTerm(path.name, [
            ...parameters.map(parameter => sandboxVar(parameter.name)),
            ...arguments_
        ]),
        sourcePoint: substituteSandboxFreeVars(path.left, replacements),
        targetPoint: substituteSandboxFreeVars(path.right, replacements),
        pathIndex,
        arguments_
    };
}

function sandboxHitOnePathExpressionMethodValue(
    expression: SandboxHitOnePathExpression,
    parameters: readonly SandboxInductiveBinder[],
    pathConstructors: readonly SandboxHitPathConstructor[],
    methodNames: readonly string[],
    owner: string
): AST {
    if (expression.kind === "compose") {
        return sandboxCompose(
            sandboxHitOnePathExpressionMethodValue(
                expression.left, parameters, pathConstructors, methodNames, owner
            ),
            sandboxHitOnePathExpressionMethodValue(
                expression.right, parameters, pathConstructors, methodNames, owner
            )
        );
    }
    if (expression.kind === "inverse") {
        return sandboxApply(
            sandboxVar("inveq"),
            sandboxHitOnePathExpressionMethodValue(
                expression.value, parameters, pathConstructors, methodNames, owner
            )
        );
    }
    const data = sandboxHitOnePathExpressionData(
        expression, parameters, pathConstructors, owner
    );
    if (data.pathIndex === undefined || !data.arguments_) {
        throw new Error(`二维 HIT 一阶路径端点 ${owner} 缺少原子路径数据`);
    }
    return sandboxApply(
        sandboxVar(methodNames[data.pathIndex]),
        ...data.arguments_.map(argument => Core.clone(argument))
    );
}

function sandboxHitTwoPathMethodValue(
    endpoint: AST,
    parameters: readonly SandboxInductiveBinder[],
    twoPathConstructors: readonly SandboxHitTwoPathConstructor[],
    methodNames: readonly string[],
    owner: string
) {
    const terms = flattenApplication(endpoint);
    const pathName = terms[0]?.type === "var" ? terms[0].name : "";
    const pathIndex = twoPathConstructors.findIndex(path => path.name === pathName);
    if (pathIndex < 0) throw new Error(`未知的三维 HIT 二阶路径端点：${pathName || owner}`);
    const arguments_ = terms.slice(1 + parameters.length).map(argument => Core.clone(argument));
    return sandboxApply(sandboxVar(methodNames[pathIndex]), ...arguments_);
}

function sandboxHitReflExpressionPathData(
    expression: Extract<SandboxHitTwoPathExpression, { kind: "refl" }>,
    parameters: readonly SandboxInductiveBinder[],
    pathConstructors: readonly SandboxHitPathConstructor[],
    owner: string
) {
    const pathIndex = pathConstructors.findIndex(path => path.name === expression.pathName);
    if (pathIndex < 0) {
        throw new Error(`未知的三维 HIT refl 一阶路径端点：${expression.pathName || owner}`);
    }
    const path = pathConstructors[pathIndex];
    if (expression.arguments.length !== path.arguments.length) {
        throw new Error(`三维 HIT refl 一阶路径端点 ${expression.pathName} 的参数数量与 metadata 不一致`);
    }
    const arguments_ = expression.arguments.map(argument => Core.clone(argument));
    return {
        path,
        pathIndex,
        arguments_,
        pathTerm: sandboxConstructorTerm(path.name, [
            ...parameters.map(parameter => sandboxVar(parameter.name)),
            ...arguments_
        ])
    };
}

function sandboxHitTwoPathExpressionTerm(
    expression: SandboxHitTwoPathExpression,
    parameters: readonly SandboxInductiveBinder[],
    pathConstructors: readonly SandboxHitPathConstructor[],
    twoPathConstructors: readonly SandboxHitTwoPathConstructor[],
    owner: string
): AST {
    if (expression.kind === "compose") {
        return sandboxCompose(
            sandboxHitTwoPathExpressionTerm(
                expression.left, parameters, pathConstructors, twoPathConstructors, owner
            ),
            sandboxHitTwoPathExpressionTerm(
                expression.right, parameters, pathConstructors, twoPathConstructors, owner
            )
        );
    }
    if (expression.kind === "inverse") {
        return sandboxApply(
            sandboxVar("inveq"),
            sandboxHitTwoPathExpressionTerm(
                expression.value, parameters, pathConstructors, twoPathConstructors, owner
            )
        );
    }
    if (expression.kind === "refl") {
        const data = sandboxHitReflExpressionPathData(
            expression, parameters, pathConstructors, owner
        );
        return sandboxApply(sandboxVar("refl"), data.pathTerm);
    }
    const path = twoPathConstructors.find(candidate => candidate.name === expression.name);
    if (!path) throw new Error(`未知的三维 HIT 二阶路径端点：${expression.name || owner}`);
    if (expression.arguments.length !== path.arguments.length) {
        throw new Error(`三维 HIT 二阶路径端点 ${expression.name} 的参数数量与 metadata 不一致`);
    }
    return sandboxConstructorTerm(path.name, [
        ...parameters.map(parameter => sandboxVar(parameter.name)),
        ...expression.arguments.map(argument => Core.clone(argument))
    ]);
}

function sandboxHitTwoPathExpressionBoundary(
    expression: SandboxHitTwoPathExpression,
    parameters: readonly SandboxInductiveBinder[],
    pathConstructors: readonly SandboxHitPathConstructor[],
    twoPathConstructors: readonly SandboxHitTwoPathConstructor[],
    owner: string
): { sourcePath: AST; targetPath: AST } {
    if (expression.kind === "compose") {
        const left = sandboxHitTwoPathExpressionBoundary(
            expression.left, parameters, pathConstructors, twoPathConstructors, owner
        );
        const right = sandboxHitTwoPathExpressionBoundary(
            expression.right, parameters, pathConstructors, twoPathConstructors, owner
        );
        return { sourcePath: left.sourcePath, targetPath: right.targetPath };
    }
    if (expression.kind === "inverse") {
        const value = sandboxHitTwoPathExpressionBoundary(
            expression.value, parameters, pathConstructors, twoPathConstructors, owner
        );
        return { sourcePath: value.targetPath, targetPath: value.sourcePath };
    }
    if (expression.kind === "refl") {
        const data = sandboxHitReflExpressionPathData(
            expression, parameters, pathConstructors, owner
        );
        return {
            sourcePath: Core.clone(data.pathTerm),
            targetPath: Core.clone(data.pathTerm)
        };
    }
    const path = twoPathConstructors.find(candidate => candidate.name === expression.name);
    if (!path) throw new Error(`未知的三维 HIT 二阶路径端点：${expression.name || owner}`);
    const replacements = new Map<string, AST>();
    path.arguments.forEach((argument, index) => {
        replacements.set(argument.name, expression.arguments[index]);
    });
    return {
        sourcePath: substituteSandboxFreeVars(path.left, replacements),
        targetPath: substituteSandboxFreeVars(path.right, replacements)
    };
}

function sandboxHitTwoPathExpressionOnePathBoundary(
    expression: SandboxHitTwoPathExpression,
    parameters: readonly SandboxInductiveBinder[],
    pathConstructors: readonly SandboxHitPathConstructor[],
    twoPathConstructors: readonly SandboxHitTwoPathConstructor[],
    owner: string
): { source: SandboxHitOnePathExpression; target: SandboxHitOnePathExpression } {
    if (expression.kind === "compose") {
        const left = sandboxHitTwoPathExpressionOnePathBoundary(
            expression.left, parameters, pathConstructors, twoPathConstructors, owner
        );
        const right = sandboxHitTwoPathExpressionOnePathBoundary(
            expression.right, parameters, pathConstructors, twoPathConstructors, owner
        );
        return { source: left.source, target: right.target };
    }
    if (expression.kind === "inverse") {
        const value = sandboxHitTwoPathExpressionOnePathBoundary(
            expression.value, parameters, pathConstructors, twoPathConstructors, owner
        );
        return { source: value.target, target: value.source };
    }
    if (expression.kind === "refl") {
        const data = sandboxHitReflExpressionPathData(
            expression, parameters, pathConstructors, owner
        );
        const atom: SandboxHitOnePathExpression = {
            kind: "atom",
            name: data.path.name,
            arguments: data.arguments_.map(argument => Core.clone(argument))
        };
        return { source: atom, target: structuredClone(atom) };
    }
    const path = twoPathConstructors.find(candidate => candidate.name === expression.name);
    if (!path) throw new Error(`未知的三维 HIT 二阶路径端点：${expression.name || owner}`);
    if (expression.arguments.length !== path.arguments.length) {
        throw new Error(`三维 HIT 二阶路径端点 ${expression.name} 参数数量与 metadata 不一致`);
    }
    const replacements = new Map<string, AST>();
    path.arguments.forEach((argument, index) => {
        replacements.set(argument.name, expression.arguments[index]);
    });
    const mapArgument = (ast: AST) => substituteSandboxFreeVars(ast, replacements);
    return {
        source: sandboxMapHitOnePathExpression(path.leftExpression, mapArgument),
        target: sandboxMapHitOnePathExpression(path.rightExpression, mapArgument)
    };
}

function sandboxHitTwoPathExpressionMethodValue(
    expression: SandboxHitTwoPathExpression,
    parameters: readonly SandboxInductiveBinder[],
    pathConstructors: readonly SandboxHitPathConstructor[],
    pathMethodNames: readonly string[],
    twoPathConstructors: readonly SandboxHitTwoPathConstructor[],
    twoPathMethodNames: readonly string[],
    owner: string
): AST {
    if (expression.kind === "compose") {
        return sandboxCompose(
            sandboxHitTwoPathExpressionMethodValue(
                expression.left, parameters, pathConstructors, pathMethodNames,
                twoPathConstructors, twoPathMethodNames, owner
            ),
            sandboxHitTwoPathExpressionMethodValue(
                expression.right, parameters, pathConstructors, pathMethodNames,
                twoPathConstructors, twoPathMethodNames, owner
            )
        );
    }
    if (expression.kind === "inverse") {
        return sandboxApply(
            sandboxVar("inveq"),
            sandboxHitTwoPathExpressionMethodValue(
                expression.value, parameters, pathConstructors, pathMethodNames,
                twoPathConstructors, twoPathMethodNames, owner
            )
        );
    }
    if (expression.kind === "refl") {
        const data = sandboxHitReflExpressionPathData(
            expression, parameters, pathConstructors, owner
        );
        return sandboxApply(
            sandboxVar("refl"),
            sandboxApply(sandboxVar(pathMethodNames[data.pathIndex]), ...data.arguments_)
        );
    }
    const pathIndex = twoPathConstructors.findIndex(path => path.name === expression.name);
    if (pathIndex < 0) throw new Error(`未知的三维 HIT 二阶路径端点：${expression.name || owner}`);
    return sandboxApply(
        sandboxVar(twoPathMethodNames[pathIndex]),
        ...expression.arguments.map(argument => Core.clone(argument))
    );
}

function sandboxHitTwoPathData(
    endpoint: AST,
    parameters: readonly SandboxInductiveBinder[],
    twoPathConstructors: readonly SandboxHitTwoPathConstructor[],
    owner: string
) {
    const terms = flattenApplication(endpoint);
    const pathName = terms[0]?.type === "var" ? terms[0].name : "";
    const pathIndex = twoPathConstructors.findIndex(path => path.name === pathName);
    if (pathIndex < 0) throw new Error(`未知的三维 HIT 二阶路径端点：${pathName || owner}`);
    const path = twoPathConstructors[pathIndex];
    const arguments_ = terms.slice(1 + parameters.length).map(argument => Core.clone(argument));
    return {
        path,
        pathIndex,
        arguments_,
        pathTerm: sandboxConstructorTerm(path.name, [
            ...parameters.map(parameter => sandboxVar(parameter.name)),
            ...arguments_
        ])
    };
}

/**
 * Resolve one of a 2-path's endpoint paths together with the dependent
 * equality type required by its path method.  Keeping this information in one
 * place is important for the 2-path computation theorem: the first-path
 * computation terms and the user-supplied coherence term need the exact same
 * endpoints, not merely syntactically similar path-method applications.
 */
function sandboxHitPathData(
    endpoint: AST,
    parameters: readonly SandboxInductiveBinder[],
    pointConstructors: readonly SandboxInductiveConstructor[],
    pathConstructors: readonly SandboxHitPathConstructor[],
    motiveName: string,
    branchNames: readonly string[],
    owner: string,
    motive: AST = sandboxVar(motiveName)
) {
    const terms = flattenApplication(endpoint);
    const pathName = terms[0]?.type === "var" ? terms[0].name : "";
    const pathIndex = pathConstructors.findIndex(path => path.name === pathName);
    if (pathIndex < 0) {
        throw new Error(`未知的二维 HIT 一阶路径端点：${pathName || owner}`);
    }
    const path = pathConstructors[pathIndex];
    const arguments_ = terms
        .slice(1 + parameters.length)
        .map(argument => Core.clone(argument));
    const pathTerm = sandboxConstructorTerm(path.name, [
        ...parameters.map(parameter => sandboxVar(parameter.name)),
        ...arguments_
    ]);
    const leftBranch = sandboxHitBranchValue(
        path.left, parameters, pointConstructors, branchNames
    );
    const rightBranch = sandboxHitBranchValue(
        path.right, parameters, pointConstructors, branchNames
    );
    const type = sandboxEquality(
        sandboxApply(sandboxVar("trans"), Core.clone(motive), pathTerm, leftBranch),
        rightBranch
    );
    return { path, pathIndex, arguments_, pathTerm, type };
}

function sandboxEquality(left: AST, right: AST): AST {
    return { type: "=", name: "", nodes: [left, right] };
}

function sandboxCompose(left: AST, right: AST): AST {
    return { type: "*", name: "", nodes: [left, right] };
}

function sandboxRenameHitPathArguments(
    path: SandboxHitPathConstructor,
    reserved: ReadonlySet<string>
): SandboxHitPathConstructor {
    const chosen = new Set(reserved);
    const occupied = new Set(reserved);
    for (const argument of path.arguments) {
        occupied.add(argument.name);
        collectSandboxAstNames(argument.type, occupied);
    }
    collectSandboxAstNames(path.left, occupied);
    collectSandboxAstNames(path.right, occupied);
    for (const index of path.resultIndices) collectSandboxAstNames(index, occupied);
    const replacements = new Map<string, string>();
    const arguments_: SandboxInductiveBinder[] = [];
    for (const argument of path.arguments) {
        const type = renameFreeInductiveNames(argument.type, replacements);
        let name = argument.name;
        if (chosen.has(name)) name = sandboxFreshName(`path_${name}`, occupied);
        else occupied.add(name);
        chosen.add(name);
        replacements.set(argument.name, name);
        arguments_.push({ name, type, typeSource: parser.stringify(type) });
    }
    const left = renameFreeInductiveNames(path.left, replacements);
    const right = renameFreeInductiveNames(path.right, replacements);
    const resultIndices = path.resultIndices.map(index =>
        renameFreeInductiveNames(index, replacements)
    );
    const type = sandboxWrapPis(arguments_, sandboxEquality(Core.clone(left), Core.clone(right)));
    return {
        name: path.name,
        arguments: arguments_,
        type,
        typeSource: parser.stringify(type),
        left,
        right,
        resultIndices
    };
}

function sandboxRenameHitTwoPathArguments(
    path: SandboxHitTwoPathConstructor,
    reserved: ReadonlySet<string>
): SandboxHitTwoPathConstructor {
    const chosen = new Set(reserved);
    const occupied = new Set(reserved);
    for (const argument of path.arguments) {
        occupied.add(argument.name);
        collectSandboxAstNames(argument.type, occupied);
    }
    collectSandboxAstNames(path.left, occupied);
    collectSandboxAstNames(path.right, occupied);
    const replacements = new Map<string, string>();
    const arguments_: SandboxInductiveBinder[] = [];
    for (const argument of path.arguments) {
        const type = renameFreeInductiveNames(argument.type, replacements);
        let name = argument.name;
        if (chosen.has(name)) name = sandboxFreshName(`path2_${name}`, occupied);
        else occupied.add(name);
        chosen.add(name);
        replacements.set(argument.name, name);
        arguments_.push({ name, type, typeSource: parser.stringify(type) });
    }
    const left = renameFreeInductiveNames(path.left, replacements);
    const right = renameFreeInductiveNames(path.right, replacements);
    const leftExpression = sandboxMapHitOnePathExpression(
        path.leftExpression,
        ast => renameFreeInductiveNames(ast, replacements)
    );
    const rightExpression = sandboxMapHitOnePathExpression(
        path.rightExpression,
        ast => renameFreeInductiveNames(ast, replacements)
    );
    const leftPoint = renameFreeInductiveNames(path.leftPoint, replacements);
    const rightPoint = renameFreeInductiveNames(path.rightPoint, replacements);
    const resultIndices = path.resultIndices.map(index =>
        renameFreeInductiveNames(index, replacements)
    );
    const type = sandboxWrapPis(arguments_, sandboxEquality(Core.clone(left), Core.clone(right)));
    return {
        name: path.name,
        arguments: arguments_,
        type,
        typeSource: parser.stringify(type),
        left,
        right,
        leftExpression,
        rightExpression,
        leftPoint,
        rightPoint,
        resultIndices
    };
}

function sandboxMapHitOnePathExpression(
    expression: SandboxHitOnePathExpression,
    mapAst: (ast: AST) => AST
): SandboxHitOnePathExpression {
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
            value: sandboxMapHitOnePathExpression(expression.value, mapAst)
        };
    }
    return {
        kind: "compose",
        left: sandboxMapHitOnePathExpression(expression.left, mapAst),
        right: sandboxMapHitOnePathExpression(expression.right, mapAst)
    };
}

function sandboxMapHitTwoPathExpression(
    expression: SandboxHitTwoPathExpression,
    mapAst: (ast: AST) => AST
): SandboxHitTwoPathExpression {
    if (expression.kind === "atom") {
        return {
            kind: "atom",
            name: expression.name,
            arguments: expression.arguments.map(mapAst)
        };
    }
    if (expression.kind === "refl") {
        return {
            kind: "refl",
            pathName: expression.pathName,
            arguments: expression.arguments.map(mapAst)
        };
    }
    if (expression.kind === "inverse") {
        return {
            kind: "inverse",
            value: sandboxMapHitTwoPathExpression(expression.value, mapAst)
        };
    }
    return {
        kind: "compose",
        left: sandboxMapHitTwoPathExpression(expression.left, mapAst),
        right: sandboxMapHitTwoPathExpression(expression.right, mapAst)
    };
}

function sandboxRenameHitThreePathArguments(
    path: SandboxHitThreePathConstructor,
    reserved: ReadonlySet<string>
): SandboxHitThreePathConstructor {
    const chosen = new Set(reserved);
    const occupied = new Set(reserved);
    for (const argument of path.arguments) {
        occupied.add(argument.name);
        collectSandboxAstNames(argument.type, occupied);
    }
    for (const ast of [
        path.left,
        path.right,
        path.sourcePath,
        path.targetPath,
        path.sourcePoint,
        path.targetPoint,
        ...path.resultIndices
    ]) collectSandboxAstNames(ast, occupied);
    const replacements = new Map<string, string>();
    const arguments_: SandboxInductiveBinder[] = [];
    for (const argument of path.arguments) {
        const type = renameFreeInductiveNames(argument.type, replacements);
        let name = argument.name;
        if (chosen.has(name)) name = sandboxFreshName(`path3_${name}`, occupied);
        else occupied.add(name);
        chosen.add(name);
        replacements.set(argument.name, name);
        arguments_.push({ name, type, typeSource: parser.stringify(type) });
    }
    const rename = (ast: AST) => renameFreeInductiveNames(ast, replacements);
    const left = rename(path.left);
    const right = rename(path.right);
    const type = sandboxWrapPis(arguments_, sandboxEquality(Core.clone(left), Core.clone(right)));
    return {
        ...path,
        arguments: arguments_,
        type,
        typeSource: parser.stringify(type),
        left,
        right,
        leftExpression: sandboxMapHitTwoPathExpression(path.leftExpression, rename),
        rightExpression: sandboxMapHitTwoPathExpression(path.rightExpression, rename),
        sourcePath: rename(path.sourcePath),
        targetPath: rename(path.targetPath),
        sourcePoint: rename(path.sourcePoint),
        targetPoint: rename(path.targetPoint),
        resultIndices: path.resultIndices.map(rename)
    };
}

function sandboxRenameHitUniformParameters(
    signature: SandboxHitDeclaration,
    reserved: ReadonlySet<string>
): SandboxHitDeclaration {
    const sourcePathLevels = sandboxHitPathLevels(signature);
    const sourcePathConstructors = hitPathConstructorsAt(sourcePathLevels, 1);
    const sourceTwoPathConstructors = hitPathConstructorsAt(sourcePathLevels, 2);
    const sourceThreePathConstructors = hitPathConstructorsAt(sourcePathLevels, 3);
    const occupied = new Set(reserved);
    const collectBinder = (binder: SandboxInductiveBinder) => {
        occupied.add(binder.name);
        collectSandboxAstNames(binder.type, occupied);
    };
    for (const parameter of signature.parameters) collectBinder(parameter);
    for (const index of signature.indices) collectBinder(index);
    collectSandboxAstNames(signature.universeAst, occupied);
    for (const constructor of signature.pointConstructors) {
        occupied.add(constructor.name);
        collectSandboxAstNames(constructor.type, occupied);
        for (const argument of constructor.argumentAsts) collectBinder(argument);
        collectSandboxAstNames(constructor.result, occupied);
        for (const index of constructor.resultIndices) collectSandboxAstNames(index, occupied);
    }
    for (const path of sourcePathConstructors) {
        occupied.add(path.name);
        collectSandboxAstNames(path.type, occupied);
        for (const argument of path.arguments) collectBinder(argument);
        collectSandboxAstNames(path.left, occupied);
        collectSandboxAstNames(path.right, occupied);
        for (const index of path.resultIndices) collectSandboxAstNames(index, occupied);
    }
    for (const path of sourceTwoPathConstructors) {
        occupied.add(path.name);
        collectSandboxAstNames(path.type, occupied);
        for (const argument of path.arguments) collectBinder(argument);
        collectSandboxAstNames(path.left, occupied);
        collectSandboxAstNames(path.right, occupied);
        collectSandboxAstNames(path.leftPoint, occupied);
        collectSandboxAstNames(path.rightPoint, occupied);
    }
    for (const path of sourceThreePathConstructors) {
        occupied.add(path.name);
        collectSandboxAstNames(path.type, occupied);
        for (const argument of path.arguments) collectBinder(argument);
        collectSandboxAstNames(path.left, occupied);
        collectSandboxAstNames(path.right, occupied);
        collectSandboxAstNames(path.sourcePath, occupied);
        collectSandboxAstNames(path.targetPath, occupied);
        collectSandboxAstNames(path.sourcePoint, occupied);
        collectSandboxAstNames(path.targetPoint, occupied);
        for (const index of path.resultIndices) collectSandboxAstNames(index, occupied);
    }

    const replacements = new Map<string, string>();
    const parameters = signature.parameters.map(parameter => {
        const type = renameFreeInductiveNames(parameter.type, replacements);
        const name = reserved.has(parameter.name)
            ? sandboxFreshName(`param_${parameter.name}`, occupied)
            : parameter.name;
        occupied.add(name);
        replacements.set(parameter.name, name);
        return { name, type, typeSource: parser.stringify(type) };
    });
    if ([...replacements].every(([name, replacement]) => name === replacement)) {
        return signature;
    }
    const rename = (ast: AST) => renameFreeInductiveNames(ast, replacements);
    const renameBinder = <T extends SandboxInductiveBinder>(binder: T): T => {
        const type = rename(binder.type);
        return { ...binder, type, typeSource: parser.stringify(type) };
    };
    const pointConstructors = signature.pointConstructors.map(constructor => {
        const type = rename(constructor.type);
        const argumentAsts = constructor.argumentAsts.map(argument => ({
            ...renameBinder(argument),
            recursiveTelescope: argument.recursiveTelescope?.map(renameBinder) ?? null,
            recursiveResultIndices: argument.recursiveResultIndices?.map(rename) ?? null
        }));
        return {
            ...constructor,
            type,
            typeSource: parser.stringify(type),
            arguments: argumentAsts.map(argument => argument.typeSource),
            argumentAsts,
            result: rename(constructor.result),
            resultIndices: constructor.resultIndices.map(rename)
        };
    });
    const pathConstructors = sourcePathConstructors.map(path => {
        const type = rename(path.type);
        return {
            ...path,
            arguments: path.arguments.map(renameBinder),
            type,
            typeSource: parser.stringify(type),
            left: rename(path.left),
            right: rename(path.right),
            resultIndices: path.resultIndices.map(rename)
        };
    });
    const twoPathConstructors = sourceTwoPathConstructors.map(path => {
        const type = rename(path.type);
        return {
            ...path,
            arguments: path.arguments.map(renameBinder),
            type,
            typeSource: parser.stringify(type),
            left: rename(path.left),
            right: rename(path.right),
            leftExpression: sandboxMapHitOnePathExpression(path.leftExpression, rename),
            rightExpression: sandboxMapHitOnePathExpression(path.rightExpression, rename),
            leftPoint: rename(path.leftPoint),
            rightPoint: rename(path.rightPoint),
            resultIndices: path.resultIndices.map(rename)
        };
    });
    const threePathConstructors = sourceThreePathConstructors.map(path => {
        const type = rename(path.type);
        return {
            ...path,
            arguments: path.arguments.map(renameBinder),
            type,
            typeSource: parser.stringify(type),
            left: rename(path.left),
            right: rename(path.right),
            leftExpression: sandboxMapHitTwoPathExpression(path.leftExpression, rename),
            rightExpression: sandboxMapHitTwoPathExpression(path.rightExpression, rename),
            sourcePath: rename(path.sourcePath),
            targetPath: rename(path.targetPath),
            sourcePoint: rename(path.sourcePoint),
            targetPoint: rename(path.targetPoint),
            resultIndices: path.resultIndices.map(rename)
        };
    });
    const universeAst = rename(signature.universeAst);
    return {
        ...signature,
        parameters,
        indices: signature.indices.map(renameBinder),
        universe: parser.stringify(universeAst),
        universeAst,
        pointConstructors,
        pathLevels: createHitPathLevels(
            pathConstructors,
            twoPathConstructors,
            threePathConstructors
        )
    };
}

/**
 * Validate the structured indexed-HIT1 metadata before lowering.  Parsed
 * source always supplies these arrays, but callers may provide a structured
 * clone (for example a save cache or a forged bridge).  Lowering must reject
 * missing or truncated index metadata explicitly instead of producing a
 * malformed bundle or throwing a generic `TypeError` later in the pipeline.
 */
function assertSandboxHitOnePathMetadata(signature: SandboxHitDeclaration) {
    if (!signature || !Array.isArray(signature.indices)
        || !Array.isArray(signature.pointConstructors)) {
        throw new Error("HIT indexed metadata 结构无效");
    }
    const indexCount = signature.indices.length;
    const assertAst = (value: unknown, label: string) => {
        if (!value || typeof value !== "object" || Array.isArray(value)
            || typeof (value as { type?: unknown }).type !== "string") {
            throw new Error(`${label} AST 结构无效`);
        }
        const stack: unknown[] = [value];
        const seen = new WeakSet<object>();
        let nodes = 0;
        while (stack.length) {
            const current = stack.pop();
            if (!current || typeof current !== "object" || Array.isArray(current)
                || typeof (current as { type?: unknown }).type !== "string") {
                throw new Error(`${label} AST 结构无效`);
            }
            if (seen.has(current)) continue;
            seen.add(current);
            if (++nodes > 4_096) throw new Error(`${label} AST 节点过多`);
            const children = (current as { nodes?: unknown }).nodes;
            if (children !== undefined && !Array.isArray(children)) {
                throw new Error(`${label} AST 子节点结构无效`);
            }
            const childNodes: unknown[] = Array.isArray(children) ? children : [];
            for (const child of childNodes) stack.push(child);
        }
    };
    const assertAstArray = (value: unknown, expectedLength: number, label: string) => {
        if (!Array.isArray(value) || value.length !== expectedLength) {
            throw new Error(`${label} 与索引数量不一致`);
        }
        value.forEach((entry, index) => assertAst(entry, `${label}[${index}]`));
    };
    for (const constructor of signature.pointConstructors) {
        if (!constructor || typeof constructor !== "object"
            || !Array.isArray(constructor.argumentAsts)) {
            throw new Error("HIT 点构造子 metadata 结构无效");
        }
        assertAstArray(
            constructor.resultIndices,
            indexCount,
            `HIT 点构造子 ${constructor.name} resultIndices`
        );
        for (const argument of constructor.argumentAsts) {
            if (!argument || typeof argument !== "object") {
                throw new Error(`HIT 点构造子 ${constructor.name} 参数 metadata 结构无效`);
            }
            const telescope = argument.recursiveTelescope;
            const recursive = telescope !== null && telescope !== undefined;
            if (recursive) {
                if (!Array.isArray(telescope)) {
                    throw new Error(
                        `HIT 点构造子 ${constructor.name} 递归参数 ${argument.name}`
                        + " 的 telescope 结构无效"
                    );
                }
                for (const [index, binder] of telescope.entries()) {
                    if (!binder || typeof binder !== "object"
                        || typeof (binder as { name?: unknown }).name !== "string") {
                        throw new Error(
                            `HIT 点构造子 ${constructor.name} 递归参数 ${argument.name}`
                            + ` 的 telescope[${index}] 结构无效`
                        );
                    }
                    assertAst(
                        (binder as { type?: unknown }).type,
                        `HIT 点构造子 ${constructor.name} 递归参数 ${argument.name}`
                        + ` telescope[${index}]`
                    );
                }
                assertAstArray(
                    argument.recursiveResultIndices,
                    indexCount,
                    `HIT 点构造子 ${constructor.name} 递归参数 ${argument.name}`
                    + " 的 resultIndices"
                );
            } else if (argument.recursiveResultIndices !== null
                && argument.recursiveResultIndices !== undefined) {
                throw new Error(
                    `HIT 点构造子 ${constructor.name} 非递归参数 ${argument.name}`
                    + " 不能携带 recursiveResultIndices"
                );
            }
        }
    }
    for (const path of hitPathConstructorsAt(signature.pathLevels, 1)) {
        assertAstArray(
            path.resultIndices,
            indexCount,
            `HIT 一阶路径构造子 ${path.name} resultIndices`
        );
    }
    for (const path of hitPathConstructorsAt(signature.pathLevels, 2)) {
        assertAstArray(
            path.resultIndices,
            indexCount,
            `HIT 二阶路径构造子 ${path.name} resultIndices`
        );
    }
    for (const path of hitPathConstructorsAt(signature.pathLevels, 3)) {
        if (indexCount > 0 && (path.leftExpression.kind !== "atom"
            || path.rightExpression.kind !== "atom")) {
            throw new Error(
                `索引 HIT 三阶路径构造子 ${path.name} 目前只支持原子二阶路径端点`
            );
        }
        assertAstArray(
            path.resultIndices,
            indexCount,
            `HIT 三阶路径构造子 ${path.name} resultIndices`
        );
    }
}

/** Lower a HIT while keeping path computation propositional. */
export function lowerSandboxHit(signature: SandboxHitDeclaration): SandboxInductiveBundle {
    assertCanonicalHitPathLevels(signature.pathLevels);
    const inputPathConstructors = hitPathConstructorsAt(signature.pathLevels, 1);
    const inputTwoPathConstructors = hitPathConstructorsAt(signature.pathLevels, 2);
    const inputThreePathConstructors = hitPathConstructorsAt(signature.pathLevels, 3);
    assertSandboxHitOnePathMetadata(signature);
    if (!inputPathConstructors.length) throw new Error("一阶 HIT 至少需要一个一阶路径构造子");
    const uniformParameterReserved = new Set([
        signature.name,
        ...signature.indices.map(index => index.name),
        ...signature.pointConstructors.map(constructor => constructor.name),
        ...inputPathConstructors.flatMap(path => [
            path.name,
            `apd_${path.name}`,
            `@apd_${path.name}`,
            `ap_${path.name}`,
            `@ap_${path.name}`
        ]),
        ...inputTwoPathConstructors.flatMap(path => [
            path.name,
            `apd_${path.name}`,
            `@apd_${path.name}`,
            `ap_${path.name}`,
            `@ap_${path.name}`,
            `ap2_${path.name}`,
            `@ap2_${path.name}`
        ]),
        ...inputThreePathConstructors.flatMap(path => [
            path.name,
            `apd3_${path.name}`,
            `@apd3_${path.name}`,
            `ap3_${path.name}`,
            `@ap3_${path.name}`
        ]),
        `ind_${signature.name}`,
        `@ind_${signature.name}`,
        `rec_${signature.name}`,
        `@rec_${signature.name}`,
        "U",
        "U@",
        "eq",
        "trans",
        "trans2",
        "trans3",
        "apd",
        "ap",
        "apd2",
        "ap2",
        "apd3",
        "ap3",
        "@hit_ap2",
        "hit_ap2",
        "@hit_ap2_comp",
        "hit_ap2_comp",
        "@hit_ap2_inv",
        "hit_ap2_inv",
        "@hit_ap2_corrected_comp",
        "@hit_ap2_corrected_inv",
        "@hit_ap2_corrected_refl",
        "@hit_apd2_comp",
        "hit_apd2_comp",
        "@hit_apd2_inv",
        "hit_apd2_inv",
        "@hit_apd2_corrected_comp",
        "hit_apd2_corrected_comp",
        "@hit_apd2_corrected_inv",
        "hit_apd2_corrected_inv",
        "@hit_apd2_corrected_refl",
        "@hit_dep2_comp",
        "hit_dep2_comp",
        "@hit_dep2_inv",
        "hit_dep2_inv",
        "@hit_map_transport",
        "hit_map_transport",
        "@hit_dep1_comp",
        "hit_dep1_comp",
        "@hit_dep1_inv",
        "hit_dep1_inv",
        "@hit_apd1_corrected_comp",
        "@hit_apd1_corrected_inv",
        "@hit_ap1_corrected_comp",
        "@hit_ap1_corrected_inv"
    ]);
    signature = sandboxRenameHitUniformParameters(signature, uniformParameterReserved);
    let pathConstructors = [...hitPathConstructorsAt(signature.pathLevels, 1)];
    let twoPathConstructors = [...hitPathConstructorsAt(signature.pathLevels, 2)];
    let threePathConstructors = [...hitPathConstructorsAt(signature.pathLevels, 3)];
    const ordinary: SandboxInductiveDeclaration = {
        name: signature.name,
        parameters: signature.parameters,
        indices: signature.indices,
        universe: signature.universe,
        universeAst: signature.universeAst,
        constructors: signature.pointConstructors
    };
    const base = lowerSandboxInductive(ordinary);
    const fullEliminatorEntry = base.auxiliaryTypes?.find(([name]) => name === `@ind_${signature.name}`);
    const fullRecursorEntry = base.auxiliaryTypes?.find(([name]) => name === `@rec_${signature.name}`);
    if (!fullEliminatorEntry || !fullRecursorEntry || !base.eliminator || !base.recursor) {
        throw new Error("HIT lowering 缺少普通归纳消去器骨架");
    }
    const motiveBinder = extractSandboxPiBinder(base.eliminator[1], signature.parameters.length);
    const fullUniverseBinder = extractSandboxPiBinder(fullEliminatorEntry[1], 0);
    const pointBranchBinders = extractSandboxPiBinders(
        base.eliminator[1], signature.parameters.length + 1, signature.pointConstructors.length
    );
    const recursorPointBinders = extractSandboxPiBinders(
        base.recursor[1], signature.parameters.length + 1, signature.pointConstructors.length
    );
    const motiveName = motiveBinder.name;
    const motiveUniverseName = fullUniverseBinder.name;
    const branchNames = pointBranchBinders.map(binder => binder.name);
    const recursorBranchNames = recursorPointBinders.map(binder => binder.name);
    const reserved = new Set([
        ...uniformParameterReserved,
        ...signature.parameters.map(parameter => parameter.name),
        ...signature.indices.map(index => index.name),
        motiveName,
        motiveUniverseName,
        ...branchNames,
        ...recursorBranchNames,
        signature.name,
        ...signature.pointConstructors.map(constructor => constructor.name),
        ...pathConstructors.map(path => path.name),
        ...twoPathConstructors.map(path => path.name),
        ...threePathConstructors.map(path => path.name),
        `ind_${signature.name}`,
        `@ind_${signature.name}`,
        `rec_${signature.name}`,
        `@rec_${signature.name}`
    ]);
    pathConstructors = pathConstructors.map(path =>
        sandboxRenameHitPathArguments(path, reserved)
    );
    twoPathConstructors = twoPathConstructors.map(path =>
        sandboxRenameHitTwoPathArguments(path, reserved)
    );
    threePathConstructors = threePathConstructors.map(path =>
        sandboxRenameHitThreePathArguments(path, reserved)
    );
    signature = {
        ...signature,
        pathLevels: createHitPathLevels(
            pathConstructors,
            twoPathConstructors,
            threePathConstructors
        )
    };
    const coherenceScope = new Set([
        ...reserved,
        ...pathConstructors.flatMap(path =>
            path.arguments.map(argument => argument.name)
        ),
        ...twoPathConstructors.flatMap(path =>
            path.arguments.map(argument => argument.name)
        ),
        ...threePathConstructors.flatMap(path =>
            path.arguments.map(argument => argument.name)
        )
    ]);
    const pathMethodNames = pathConstructors.map((_, index) =>
        sandboxFreshName(`p${index}`, coherenceScope)
    );
    const recursorPathMethodNames = pathConstructors.map((_, index) =>
        sandboxFreshName(`q${index}`, coherenceScope)
    );
    const dependentTwoPathMethodNames = twoPathConstructors.map((_, index) =>
        sandboxFreshName(`p2_${index}`, coherenceScope)
    );
    const recursorTwoPathMethodNames = twoPathConstructors.map((_, index) =>
        sandboxFreshName(`q2_${index}`, coherenceScope)
    );
    const dependentThreePathMethodNames = threePathConstructors.map((_, index) =>
        sandboxFreshName(`p3_${index}`, coherenceScope)
    );
    const recursorThreePathMethodNames = threePathConstructors.map((_, index) =>
        sandboxFreshName(`q3_${index}`, coherenceScope)
    );
    const parameterVars = signature.parameters.map(parameter => sandboxVar(parameter.name));
    const hitType = sandboxApply(sandboxVar(signature.name), ...parameterVars);
    const hitUniverseLevel = signature.universeAst.type === "apply"
        && signature.universeAst.nodes?.[0]?.type === "var"
        && signature.universeAst.nodes[0].name === "U"
        && signature.universeAst.nodes[1]
        ? Core.clone(signature.universeAst.nodes[1])
        : null;
    if (!hitUniverseLevel) {
        throw new Error(`HIT ${signature.name} 的 Universe 缺少显式层级`);
    }

    const dependentPathBinders: SandboxInductiveBinder[] = [];
    const recursorPathBinders: SandboxInductiveBinder[] = [];
    for (let index = 0; index < pathConstructors.length; index++) {
        const path = pathConstructors[index];
        const pathArguments = path.arguments.map(argument => sandboxVar(argument.name));
        const pathTerm = sandboxConstructorTerm(path.name, [...parameterVars, ...pathArguments]);
        const fiberMotive = sandboxHitFiberMotive(signature, motiveName, path.resultIndices);
        const leftBranch = sandboxHitBranchValue(
            path.left, signature.parameters, signature.pointConstructors, branchNames
        );
        const rightBranch = sandboxHitBranchValue(
            path.right, signature.parameters, signature.pointConstructors, branchNames
        );
        const dependentType = sandboxWrapPis(path.arguments, sandboxEquality(
            sandboxApply(sandboxVar("trans"), fiberMotive, pathTerm, leftBranch),
            rightBranch
        ));
        dependentPathBinders.push({
            name: pathMethodNames[index],
            type: dependentType,
            typeSource: parser.stringify(dependentType)
        });

        const leftRecursorBranch = sandboxHitBranchValue(
            path.left, signature.parameters, signature.pointConstructors, recursorBranchNames
        );
        const rightRecursorBranch = sandboxHitBranchValue(
            path.right, signature.parameters, signature.pointConstructors, recursorBranchNames
        );
        const recursorType = sandboxWrapPis(
            path.arguments,
            sandboxEquality(leftRecursorBranch, rightRecursorBranch)
        );
        recursorPathBinders.push({
            name: recursorPathMethodNames[index],
            type: recursorType,
            typeSource: parser.stringify(recursorType)
        });
    }

    const dependentOnePathExpressionMethod = (
        expression: SandboxHitOnePathExpression,
        owner: string,
        motive: AST = sandboxVar(motiveName)
    ): {
        term: AST;
        sourcePoint: AST;
        targetPoint: AST;
        sourceValue: AST;
        targetValue: AST;
        method: AST;
    } => {
        if (expression.kind === "compose") {
            const left = dependentOnePathExpressionMethod(expression.left, owner, motive);
            const right = dependentOnePathExpressionMethod(expression.right, owner, motive);
            if (!sameSandboxAst(left.targetPoint, right.sourcePoint)) {
                throw new Error(`二维 HIT 一阶路径表达式 ${owner} 的组合中间点边界不一致`);
            }
            return {
                term: sandboxCompose(left.term, right.term),
                sourcePoint: left.sourcePoint,
                targetPoint: right.targetPoint,
                sourceValue: left.sourceValue,
                targetValue: right.targetValue,
                method: sandboxApply(
                    sandboxVar("hit_dep1_comp"),
                    Core.clone(motive),
                    left.sourceValue,
                    left.targetValue,
                    right.targetValue,
                    left.method,
                    right.method
                )
            };
        }
        if (expression.kind === "inverse") {
            const value = dependentOnePathExpressionMethod(expression.value, owner, motive);
            return {
                term: sandboxApply(sandboxVar("inveq"), value.term),
                sourcePoint: value.targetPoint,
                targetPoint: value.sourcePoint,
                sourceValue: value.targetValue,
                targetValue: value.sourceValue,
                method: sandboxApply(
                    sandboxVar("hit_dep1_inv"),
                    Core.clone(motive),
                    value.sourceValue,
                    value.targetValue,
                    value.method
                )
            };
        }
        const data = sandboxHitOnePathExpressionData(
            expression, signature.parameters, pathConstructors, owner
        );
        if (data.pathIndex === undefined || !data.arguments_) {
            throw new Error(`二维 HIT 一阶路径端点 ${owner} 缺少原子路径数据`);
        }
        const sourceValue = sandboxHitBranchValue(
            data.sourcePoint, signature.parameters, signature.pointConstructors, branchNames
        );
        const targetValue = sandboxHitBranchValue(
            data.targetPoint, signature.parameters, signature.pointConstructors, branchNames
        );
        return {
            term: data.term,
            sourcePoint: data.sourcePoint,
            targetPoint: data.targetPoint,
            sourceValue,
            targetValue,
            method: sandboxApply(
                sandboxVar(pathMethodNames[data.pathIndex]),
                ...data.arguments_.map(argument => Core.clone(argument))
            )
        };
    };

    const dependentTwoPathBinders: SandboxInductiveBinder[] = [];
    const recursorTwoPathBinders: SandboxInductiveBinder[] = [];
    for (let index = 0; index < twoPathConstructors.length; index++) {
        const path = twoPathConstructors[index];
        const pathArguments = path.arguments.map(argument => sandboxVar(argument.name));
        const fiberMotive = sandboxHitFiberMotive(
            signature,
            motiveName,
            path.resultIndices
        );
        const leftDependent = dependentOnePathExpressionMethod(
            path.leftExpression, path.name, fiberMotive
        );
        const rightDependent = dependentOnePathExpressionMethod(
            path.rightExpression, path.name, fiberMotive
        );
        const leftMethod = leftDependent.method;
        const rightMethod = rightDependent.method;
        const endpointValue = leftDependent.sourceValue;
        const transportedRightMethod = {
            type: "*",
            name: "",
            nodes: [
                sandboxApply(
                    sandboxVar("trans2"),
                    fiberMotive,
                    sandboxConstructorTerm(path.name, [
                        ...parameterVars,
                        ...pathArguments
                    ]),
                    endpointValue
                ),
                rightMethod
            ]
        } as AST;
        const dependentType = sandboxWrapPis(path.arguments, sandboxEquality(
            leftMethod,
            transportedRightMethod
        ));
        dependentTwoPathBinders.push({
            name: dependentTwoPathMethodNames[index],
            type: dependentType,
            typeSource: parser.stringify(dependentType)
        });

        const leftRecursorMethod = sandboxHitOnePathExpressionMethodValue(
            path.leftExpression, signature.parameters, pathConstructors,
            recursorPathMethodNames, path.name
        );
        const rightRecursorMethod = sandboxHitOnePathExpressionMethodValue(
            path.rightExpression, signature.parameters, pathConstructors,
            recursorPathMethodNames, path.name
        );
        const recursorType = sandboxWrapPis(path.arguments, sandboxEquality(
            leftRecursorMethod,
            rightRecursorMethod
        ));
        recursorTwoPathBinders.push({
            name: recursorTwoPathMethodNames[index],
            type: recursorType,
            typeSource: parser.stringify(recursorType)
        });
    }

    const dependentThreePathBinders: SandboxInductiveBinder[] = [];
    const recursorThreePathBinders: SandboxInductiveBinder[] = [];
    const dependentTwoPathExpressionMethod = (
        expression: SandboxHitTwoPathExpression,
        owner: string,
        sourceValue: AST,
        targetValue: AST
    ): { term: AST; sourceMethod: AST; targetMethod: AST; proof: AST } => {
        if (expression.kind === "compose") {
            const left = dependentTwoPathExpressionMethod(
                expression.left, owner, sourceValue, targetValue
            );
            const right = dependentTwoPathExpressionMethod(
                expression.right, owner, sourceValue, targetValue
            );
            return {
                term: sandboxCompose(left.term, right.term),
                sourceMethod: left.sourceMethod,
                targetMethod: right.targetMethod,
                proof: sandboxApply(
                    sandboxVar("hit_dep2_comp"),
                    sandboxVar(motiveName),
                    Core.clone(sourceValue),
                    Core.clone(targetValue),
                    left.sourceMethod,
                    left.targetMethod,
                    right.targetMethod,
                    left.term,
                    right.term,
                    left.proof,
                    right.proof
                )
            };
        }
        if (expression.kind === "inverse") {
            const value = dependentTwoPathExpressionMethod(
                expression.value, owner, sourceValue, targetValue
            );
            return {
                term: sandboxApply(sandboxVar("inveq"), value.term),
                sourceMethod: value.targetMethod,
                targetMethod: value.sourceMethod,
                proof: sandboxApply(
                    sandboxVar("hit_dep2_inv"),
                    sandboxVar(motiveName),
                    Core.clone(sourceValue),
                    Core.clone(targetValue),
                    value.sourceMethod,
                    value.targetMethod,
                    value.term,
                    value.proof
                )
            };
        }
        if (expression.kind === "refl") {
            const data = sandboxHitReflExpressionPathData(
                expression, signature.parameters, pathConstructors, owner
            );
            const method = sandboxApply(
                sandboxVar(pathMethodNames[data.pathIndex]),
                ...data.arguments_
            );
            return {
                term: sandboxApply(sandboxVar("refl"), data.pathTerm),
                sourceMethod: Core.clone(method),
                targetMethod: Core.clone(method),
                proof: sandboxApply(sandboxVar("refl"), method)
            };
        }
        const pathIndex = twoPathConstructors.findIndex(path => path.name === expression.name);
        if (pathIndex < 0) throw new Error(`未知的三维 HIT 二阶路径端点：${expression.name || owner}`);
        const path = twoPathConstructors[pathIndex];
        const replacements = new Map<string, AST>();
        path.arguments.forEach((argument, index) => {
            replacements.set(argument.name, expression.arguments[index]);
        });
        const sourceExpression = sandboxMapHitOnePathExpression(
            path.leftExpression,
            ast => substituteSandboxFreeVars(ast, replacements)
        );
        const targetExpression = sandboxMapHitOnePathExpression(
            path.rightExpression,
            ast => substituteSandboxFreeVars(ast, replacements)
        );
        const fiberMotive = sandboxHitFiberMotive(
            signature, motiveName, path.resultIndices
        );
        const source = dependentOnePathExpressionMethod(
            sourceExpression, owner, fiberMotive
        );
        const target = dependentOnePathExpressionMethod(
            targetExpression, owner, fiberMotive
        );
        return {
            term: sandboxHitTwoPathExpressionTerm(
                expression, signature.parameters, pathConstructors, twoPathConstructors, owner
            ),
            sourceMethod: source.method,
            targetMethod: target.method,
            proof: sandboxApply(
                sandboxVar(dependentTwoPathMethodNames[pathIndex]),
                ...expression.arguments.map(argument => Core.clone(argument))
            )
        };
    };
    for (let index = 0; index < threePathConstructors.length; index++) {
        const path = threePathConstructors[index];
        const pathArguments = path.arguments.map(argument => sandboxVar(argument.name));
        const pathTerm = sandboxConstructorTerm(path.name, [...parameterVars, ...pathArguments]);
        const fiberMotive = sandboxHitFiberMotive(signature, motiveName, path.resultIndices);
        const sourceValue = sandboxHitBranchValue(
            path.sourcePoint, signature.parameters, signature.pointConstructors, branchNames
        );
        const targetValue = sandboxHitBranchValue(
            path.targetPoint, signature.parameters, signature.pointConstructors, branchNames
        );
        const leftDependentExpression = dependentTwoPathExpressionMethod(
            path.leftExpression, path.name, sourceValue, targetValue
        );
        const rightDependentExpression = dependentTwoPathExpressionMethod(
            path.rightExpression, path.name, sourceValue, targetValue
        );
        const leftMethod = leftDependentExpression.proof;
        const rightMethod = rightDependentExpression.proof;
        const sourceMethod = leftDependentExpression.sourceMethod;
        const targetMethod = leftDependentExpression.targetMethod;
        const endpointValue = sandboxHitBranchValue(
            path.sourcePoint,
            signature.parameters,
            signature.pointConstructors,
            branchNames
        );
        const lambdaScope = new Set<string>([
            ...coherenceScope,
            ...path.arguments.map(argument => argument.name)
        ]);
        for (const ast of [path.sourcePath, path.targetPath, sourceMethod, targetMethod]) {
            collectSandboxAstNames(ast, lambdaScope);
        }
        const pathValueName = sandboxFreshName("twoPathValue", lambdaScope);
        const pathValue = sandboxVar(pathValueName);
        const coherenceFamily = sandboxLambda(
            pathValueName,
            sandboxEquality(Core.clone(path.sourcePath), Core.clone(path.targetPath)),
            sandboxEquality(
                sourceMethod,
                sandboxCompose(
                    sandboxApply(
                        sandboxVar("trans2"),
                        Core.clone(fiberMotive),
                        pathValue,
                        endpointValue
                    ),
                    targetMethod
                )
            )
        );
        const dependentType = sandboxWrapPis(path.arguments, sandboxEquality(
            sandboxApply(sandboxVar("trans"), coherenceFamily, pathTerm, leftMethod),
            rightMethod
        ));
        dependentThreePathBinders.push({
            name: dependentThreePathMethodNames[index],
            type: dependentType,
            typeSource: parser.stringify(dependentType)
        });

        const leftRecursorMethod = sandboxHitTwoPathExpressionMethodValue(
            path.leftExpression,
            signature.parameters,
            pathConstructors,
            recursorPathMethodNames,
            twoPathConstructors,
            recursorTwoPathMethodNames,
            path.name
        );
        const rightRecursorMethod = sandboxHitTwoPathExpressionMethodValue(
            path.rightExpression,
            signature.parameters,
            pathConstructors,
            recursorPathMethodNames,
            twoPathConstructors,
            recursorTwoPathMethodNames,
            path.name
        );
        const recursorType = sandboxWrapPis(path.arguments, sandboxEquality(
            leftRecursorMethod,
            rightRecursorMethod
        ));
        recursorThreePathBinders.push({
            name: recursorThreePathMethodNames[index],
            type: recursorType,
            typeSource: parser.stringify(recursorType)
        });
    }

    const allDependentPathBinders = [
        ...dependentPathBinders,
        ...dependentTwoPathBinders,
        ...dependentThreePathBinders
    ];
    const allRecursorPathBinders = [
        ...recursorPathBinders,
        ...recursorTwoPathBinders,
        ...recursorThreePathBinders
    ];

    const publicEliminatorType = sandboxInsertPis(
        base.eliminator![1],
        signature.parameters.length + 1 + signature.pointConstructors.length,
        allDependentPathBinders
    );
    const fullEliminatorType = sandboxInsertPis(
        fullEliminatorEntry[1],
        1 + signature.parameters.length + 1 + signature.pointConstructors.length,
        allDependentPathBinders
    );
    const publicRecursorType = sandboxInsertPis(
        base.recursor[1],
        signature.parameters.length + 1 + signature.pointConstructors.length,
        allRecursorPathBinders
    );
    const fullRecursorType = sandboxInsertPis(
        fullRecursorEntry[1],
        1 + signature.parameters.length + 1 + signature.pointConstructors.length,
        allRecursorPathBinders
    );

    // Keep computation-rule metavariables disjoint from ordinary lowering's
    // `?pN` parameter patterns and generated branch names.
    const pathPatternVariables = pathMethodNames.map((_, index) => sandboxVar(`?hitPath${index}`));
    const recursorPathPatternVariables = recursorPathMethodNames.map((_, index) =>
        sandboxVar(`?hitRecPath${index}`)
    );
    const twoPathPatternVariables = dependentTwoPathMethodNames.map((_, index) =>
        sandboxVar(`?hitTwoPath${index}`)
    );
    const recursorTwoPathPatternVariables = recursorTwoPathMethodNames.map((_, index) =>
        sandboxVar(`?hitRecTwoPath${index}`)
    );
    const threePathPatternVariables = dependentThreePathMethodNames.map((_, index) =>
        sandboxVar(`?hitThreePath${index}`)
    );
    const recursorThreePathPatternVariables = recursorThreePathMethodNames.map((_, index) =>
        sandboxVar(`?hitRecThreePath${index}`)
    );
    const insertHitMethodArguments = (
        source: AST,
        targetHead: string,
        insertion: number,
        additions: readonly AST[]
    ): AST => {
        const visit = (node: AST): AST => {
            if (node.type === "apply") {
                const terms = flattenApplication(node);
                const head = terms[0];
                if (head?.type === "var" && head.name === targetHead) {
                    const arguments_ = terms.slice(1).map(visit);
                    return sandboxApply(
                        Core.clone(head),
                        ...arguments_.slice(0, insertion),
                        ...additions.map(argument => Core.clone(argument)),
                        ...arguments_.slice(insertion)
                    );
                }
            }
            const clone = Core.clone(node);
            clone.nodes = clone.nodes?.map(visit);
            return clone;
        };
        return visit(source);
    };
    const computeRules = Object.fromEntries(
        Object.entries(base.computeRules ?? {}).map(([head, rules]) => [
            head,
            rules.map(rule => {
                const pattern = rule.pattern.map(term => Core.clone(term));
                const full = head.startsWith("@");
                const insertion = 1 + (full ? 1 : 0) + signature.parameters.length + 1
                    + signature.pointConstructors.length;
                pattern.splice(
                    insertion,
                    0,
                    ...(head.includes("rec_")
                        ? [
                            ...recursorPathPatternVariables,
                            ...recursorTwoPathPatternVariables,
                            ...recursorThreePathPatternVariables
                        ]
                        : [
                            ...pathPatternVariables,
                            ...twoPathPatternVariables,
                            ...threePathPatternVariables
                        ])
                        .map(term => Core.clone(term))
                );
                const methodArguments = head.includes("rec_")
                    ? [
                        ...recursorPathPatternVariables,
                        ...recursorTwoPathPatternVariables,
                        ...recursorThreePathPatternVariables
                    ]
                    : [
                        ...pathPatternVariables,
                        ...twoPathPatternVariables,
                        ...threePathPatternVariables
                    ];
                const resultInsertion = (full ? 1 : 0)
                    + signature.parameters.length
                    + 1
                    + signature.pointConstructors.length;
                return {
                    pattern,
                    result: insertHitMethodArguments(
                        rule.result,
                        head,
                        resultInsertion,
                        methodArguments
                    )
                };
            })
        ])
    ) as Record<string, { pattern: AST[]; result: AST }[]>;

    const pathTypes: [string, AST][] = pathConstructors.map(path => [
        path.name,
        sandboxWrapPis(signature.parameters, Core.clone(path.type))
    ]);
    pathTypes.push(...twoPathConstructors.map(path => [
        path.name,
        sandboxWrapPis(signature.parameters, Core.clone(path.type))
    ] as [string, AST]));
    pathTypes.push(...threePathConstructors.map(path => [
        path.name,
        sandboxWrapPis(signature.parameters, Core.clone(path.type))
    ] as [string, AST]));
    const computationTypes: [string, AST][] = [];
    for (let index = 0; index < pathConstructors.length; index++) {
        const path = pathConstructors[index];
        const pathArguments = path.arguments.map(argument => sandboxVar(argument.name));
        const pathTerm = sandboxConstructorTerm(path.name, [...parameterVars, ...pathArguments]);
        const dependentHead = sandboxHitHeadAtIndices(sandboxApply(
            sandboxVar(`ind_${signature.name}`),
            ...parameterVars,
            sandboxVar(motiveName),
            ...branchNames.map(name => sandboxVar(name)),
            ...pathMethodNames.map(name => sandboxVar(name)),
            ...dependentTwoPathMethodNames.map(name => sandboxVar(name)),
            ...dependentThreePathMethodNames.map(name => sandboxVar(name))
        ), path.resultIndices);
        const fullDependentHead = sandboxHitHeadAtIndices(sandboxApply(
            sandboxVar(`@ind_${signature.name}`),
            sandboxVar(motiveUniverseName),
            ...parameterVars,
            sandboxVar(motiveName),
            ...branchNames.map(name => sandboxVar(name)),
            ...pathMethodNames.map(name => sandboxVar(name)),
            ...dependentTwoPathMethodNames.map(name => sandboxVar(name)),
            ...dependentThreePathMethodNames.map(name => sandboxVar(name))
        ), path.resultIndices);
        const recursorHead = sandboxHitHeadAtIndices(sandboxApply(
            sandboxVar(`rec_${signature.name}`),
            ...parameterVars,
            sandboxVar(motiveName),
            ...recursorBranchNames.map(name => sandboxVar(name)),
            ...recursorPathMethodNames.map(name => sandboxVar(name)),
            ...recursorTwoPathMethodNames.map(name => sandboxVar(name)),
            ...recursorThreePathMethodNames.map(name => sandboxVar(name))
        ), path.resultIndices);
        const fullRecursorHead = sandboxHitHeadAtIndices(sandboxApply(
            sandboxVar(`@rec_${signature.name}`),
            sandboxVar(motiveUniverseName),
            ...parameterVars,
            sandboxVar(motiveName),
            ...recursorBranchNames.map(name => sandboxVar(name)),
            ...recursorPathMethodNames.map(name => sandboxVar(name)),
            ...recursorTwoPathMethodNames.map(name => sandboxVar(name)),
            ...recursorThreePathMethodNames.map(name => sandboxVar(name))
        ), path.resultIndices);
        const pathMethodValue = sandboxApply(sandboxVar(pathMethodNames[index]), ...pathArguments);
        const recursorPathMethodValue = sandboxApply(
            sandboxVar(recursorPathMethodNames[index]), ...pathArguments
        );

        const publicApdBody = sandboxWrapPis(path.arguments, sandboxEquality(
            sandboxApply(sandboxVar("apd"), dependentHead, pathTerm),
            pathMethodValue
        ));
        let publicApdType = sandboxWrapPis(allDependentPathBinders, publicApdBody);
        const pointBranchBinders = extractSandboxPiBinders(
            base.eliminator![1], signature.parameters.length + 1, signature.pointConstructors.length
        );
        publicApdType = sandboxWrapPis(pointBranchBinders, publicApdType);
        publicApdType = sandboxPi(
            motiveName,
            extractSandboxPiBinder(base.eliminator![1], signature.parameters.length).type,
            publicApdType
        );
        publicApdType = sandboxWrapPis(signature.parameters, publicApdType);

        let fullApdType = sandboxWrapPis(path.arguments, sandboxEquality(
            sandboxApply(sandboxVar("apd"), fullDependentHead, pathTerm),
            Core.clone(pathMethodValue)
        ));
        fullApdType = sandboxWrapPis(allDependentPathBinders, fullApdType);
        const fullPointBranchBinders = extractSandboxPiBinders(
            fullEliminatorEntry[1], 1 + signature.parameters.length + 1,
            signature.pointConstructors.length
        );
        fullApdType = sandboxWrapPis(fullPointBranchBinders, fullApdType);
        fullApdType = sandboxPi(
            motiveName,
            extractSandboxPiBinder(fullEliminatorEntry[1], 1 + signature.parameters.length).type,
            fullApdType
        );
        fullApdType = sandboxWrapPis(signature.parameters, fullApdType);
        fullApdType = sandboxPi(motiveUniverseName, sandboxVar("U@"), fullApdType);

        let publicApType = sandboxWrapPis(path.arguments, sandboxEquality(
            sandboxApply(sandboxVar("ap"), recursorHead, pathTerm),
            recursorPathMethodValue
        ));
        publicApType = sandboxWrapPis(allRecursorPathBinders, publicApType);
        const recursorPointBinders = extractSandboxPiBinders(
            base.recursor[1], signature.parameters.length + 1, signature.pointConstructors.length
        );
        publicApType = sandboxWrapPis(recursorPointBinders, publicApType);
        publicApType = sandboxPi(
            motiveName,
            extractSandboxPiBinder(base.recursor[1], signature.parameters.length).type,
            publicApType
        );
        publicApType = sandboxWrapPis(signature.parameters, publicApType);

        let fullApType = sandboxWrapPis(path.arguments, sandboxEquality(
            sandboxApply(sandboxVar("ap"), fullRecursorHead, pathTerm),
            Core.clone(recursorPathMethodValue)
        ));
        fullApType = sandboxWrapPis(allRecursorPathBinders, fullApType);
        const fullRecursorPointBinders = extractSandboxPiBinders(
            fullRecursorEntry[1], 1 + signature.parameters.length + 1,
            signature.pointConstructors.length
        );
        fullApType = sandboxWrapPis(fullRecursorPointBinders, fullApType);
        fullApType = sandboxPi(
            motiveName,
            extractSandboxPiBinder(fullRecursorEntry[1], 1 + signature.parameters.length).type,
            fullApType
        );
        fullApType = sandboxWrapPis(signature.parameters, fullApType);
        fullApType = sandboxPi(motiveUniverseName, sandboxVar("U@"), fullApType);

        computationTypes.push(
            [`apd_${path.name}`, publicApdType],
            [`@apd_${path.name}`, fullApdType],
            [`ap_${path.name}`, publicApType],
            [`@ap_${path.name}`, fullApType]
        );
    }

    type SharedDependentOnePathComputation = {
        term: AST;
        sourcePoint: AST;
        targetPoint: AST;
        sourceValue: AST;
        targetValue: AST;
        type: AST;
        method: AST;
        computation: AST;
    };
    const makeSharedDependentOnePathComputation = (
        expression: SandboxHitOnePathExpression,
        head: AST,
        full: boolean,
        owner: string,
        motive: AST = sandboxVar(motiveName),
        domainType: AST = hitType
    ): SharedDependentOnePathComputation => {
        if (expression.kind === "compose") {
            const left = makeSharedDependentOnePathComputation(
                expression.left, head, full, owner, motive, domainType
            );
            const right = makeSharedDependentOnePathComputation(
                expression.right, head, full, owner, motive, domainType
            );
            const method = sandboxApply(
                sandboxVar("hit_dep1_comp"),
                Core.clone(motive),
                Core.clone(left.sourceValue),
                Core.clone(left.targetValue),
                Core.clone(right.targetValue),
                Core.clone(left.method),
                Core.clone(right.method)
            );
            const term = sandboxCompose(left.term, right.term);
            return {
                term,
                sourcePoint: left.sourcePoint,
                targetPoint: right.targetPoint,
                sourceValue: left.sourceValue,
                targetValue: right.targetValue,
                type: sandboxEquality(
                    sandboxApply(
                        sandboxVar("trans"), Core.clone(motive),
                        Core.clone(term), Core.clone(left.sourceValue)
                    ),
                    Core.clone(right.targetValue)
                ),
                method,
                computation: sandboxApply(
                    sandboxVar("@hit_apd1_corrected_comp"),
                    Core.clone(hitUniverseLevel),
                    full ? sandboxVar(motiveUniverseName) : sandboxVar("@0"),
                    Core.clone(domainType),
                    Core.clone(left.sourcePoint),
                    Core.clone(left.targetPoint),
                    Core.clone(right.targetPoint),
                    Core.clone(left.term),
                    Core.clone(right.term),
                    Core.clone(motive),
                    Core.clone(head),
                    Core.clone(left.method),
                    Core.clone(right.method),
                    Core.clone(left.computation),
                    Core.clone(right.computation)
                )
            };
        }
        if (expression.kind === "inverse") {
            const value = makeSharedDependentOnePathComputation(
                expression.value, head, full, owner, motive, domainType
            );
            const term = sandboxApply(sandboxVar("inveq"), value.term);
            const method = sandboxApply(
                sandboxVar("hit_dep1_inv"),
                Core.clone(motive),
                Core.clone(value.sourceValue),
                Core.clone(value.targetValue),
                Core.clone(value.method)
            );
            return {
                term,
                sourcePoint: value.targetPoint,
                targetPoint: value.sourcePoint,
                sourceValue: value.targetValue,
                targetValue: value.sourceValue,
                type: sandboxEquality(
                    sandboxApply(
                        sandboxVar("trans"), Core.clone(motive),
                        Core.clone(term), Core.clone(value.targetValue)
                    ),
                    Core.clone(value.sourceValue)
                ),
                method,
                computation: sandboxApply(
                    sandboxVar("@hit_apd1_corrected_inv"),
                    Core.clone(hitUniverseLevel),
                    full ? sandboxVar(motiveUniverseName) : sandboxVar("@0"),
                    Core.clone(domainType),
                    Core.clone(value.sourcePoint),
                    Core.clone(value.targetPoint),
                    Core.clone(value.term),
                    Core.clone(motive),
                    Core.clone(head),
                    Core.clone(value.method),
                    Core.clone(value.computation)
                )
            };
        }
        const data = sandboxHitOnePathExpressionData(
            expression, signature.parameters, pathConstructors, owner
        );
        if (data.pathIndex === undefined || !data.arguments_) {
            throw new Error(`二维 HIT 一阶路径端点 ${owner} 缺少原子路径数据`);
        }
        const atom = pathConstructors[data.pathIndex];
        const sourceValue = sandboxHitBranchValue(
            data.sourcePoint, signature.parameters, signature.pointConstructors, branchNames
        );
        const targetValue = sandboxHitBranchValue(
            data.targetPoint, signature.parameters, signature.pointConstructors, branchNames
        );
        const method = sandboxApply(
            sandboxVar(pathMethodNames[data.pathIndex]),
            ...data.arguments_.map(argument => Core.clone(argument))
        );
        return {
            term: data.term,
            sourcePoint: data.sourcePoint,
            targetPoint: data.targetPoint,
            sourceValue,
            targetValue,
            type: sandboxEquality(
                sandboxApply(
                    sandboxVar("trans"), Core.clone(motive),
                    Core.clone(data.term), Core.clone(sourceValue)
                ),
                Core.clone(targetValue)
            ),
            method,
            computation: sandboxApply(
                sandboxVar(`${full ? "@" : ""}apd_${atom.name}`),
                ...(full ? [sandboxVar(motiveUniverseName)] : []),
                ...parameterVars,
                sandboxVar(motiveName),
                ...branchNames.map(name => sandboxVar(name)),
                ...pathMethodNames.map(name => sandboxVar(name)),
                ...dependentTwoPathMethodNames.map(name => sandboxVar(name)),
                ...dependentThreePathMethodNames.map(name => sandboxVar(name)),
                ...data.arguments_.map(argument => Core.clone(argument))
            )
        };
    };
    type SharedRecursorOnePathComputation = {
        term: AST;
        sourcePoint: AST;
        targetPoint: AST;
        method: AST;
        computation: AST;
    };
    const makeSharedRecursorOnePathComputation = (
        expression: SandboxHitOnePathExpression,
        head: AST,
        full: boolean,
        owner: string,
        domainType: AST = hitType
    ): SharedRecursorOnePathComputation => {
        if (expression.kind === "compose") {
            const left = makeSharedRecursorOnePathComputation(
                expression.left, head, full, owner, domainType
            );
            const right = makeSharedRecursorOnePathComputation(
                expression.right, head, full, owner, domainType
            );
            const method = sandboxCompose(left.method, right.method);
            return {
                term: sandboxCompose(left.term, right.term),
                sourcePoint: left.sourcePoint,
                targetPoint: right.targetPoint,
                method,
                computation: sandboxApply(
                    sandboxVar("@hit_ap1_corrected_comp"),
                    Core.clone(hitUniverseLevel),
                    full ? sandboxVar(motiveUniverseName) : sandboxVar("@0"),
                    Core.clone(domainType),
                    sandboxVar(motiveName),
                    Core.clone(left.sourcePoint),
                    Core.clone(left.targetPoint),
                    Core.clone(right.targetPoint),
                    Core.clone(left.term),
                    Core.clone(right.term),
                    Core.clone(head),
                    Core.clone(left.method),
                    Core.clone(right.method),
                    Core.clone(left.computation),
                    Core.clone(right.computation)
                )
            };
        }
        if (expression.kind === "inverse") {
            const value = makeSharedRecursorOnePathComputation(
                expression.value, head, full, owner, domainType
            );
            const method = sandboxApply(sandboxVar("inveq"), value.method);
            return {
                term: sandboxApply(sandboxVar("inveq"), value.term),
                sourcePoint: value.targetPoint,
                targetPoint: value.sourcePoint,
                method,
                computation: sandboxApply(
                    sandboxVar("@hit_ap1_corrected_inv"),
                    Core.clone(hitUniverseLevel),
                    full ? sandboxVar(motiveUniverseName) : sandboxVar("@0"),
                    Core.clone(domainType),
                    sandboxVar(motiveName),
                    Core.clone(value.sourcePoint),
                    Core.clone(value.targetPoint),
                    Core.clone(value.term),
                    Core.clone(head),
                    Core.clone(value.method),
                    Core.clone(value.computation)
                )
            };
        }
        const data = sandboxHitOnePathExpressionData(
            expression, signature.parameters, pathConstructors, owner
        );
        if (data.pathIndex === undefined || !data.arguments_) {
            throw new Error(`二维 HIT 一阶路径端点 ${owner} 缺少原子路径数据`);
        }
        const atom = pathConstructors[data.pathIndex];
        const method = sandboxApply(
            sandboxVar(recursorPathMethodNames[data.pathIndex]),
            ...data.arguments_.map(argument => Core.clone(argument))
        );
        return {
            term: data.term,
            sourcePoint: data.sourcePoint,
            targetPoint: data.targetPoint,
            method,
            computation: sandboxApply(
                sandboxVar(`${full ? "@" : ""}ap_${atom.name}`),
                ...(full ? [sandboxVar(motiveUniverseName)] : []),
                ...parameterVars,
                sandboxVar(motiveName),
                ...recursorBranchNames.map(name => sandboxVar(name)),
                ...recursorPathMethodNames.map(name => sandboxVar(name)),
                ...recursorTwoPathMethodNames.map(name => sandboxVar(name)),
                ...recursorThreePathMethodNames.map(name => sandboxVar(name)),
                ...data.arguments_.map(argument => Core.clone(argument))
            )
        };
    };

    // Two-dimensional path computation is propositional.  The first-path
    // computation rules are themselves propositional, so the raw p2 method
    // cannot be used directly as the RHS of apd2: its endpoints are p0 and
    // trans2 ... p1, while apd2 has the corresponding apd endpoints.  Insert
    // those first-path computation paths explicitly and keep the result out
    // of the definitional compute-rule table.
    for (let index = 0; index < twoPathConstructors.length; index++) {
        const path = twoPathConstructors[index];
        const pathArguments = path.arguments.map(argument => sandboxVar(argument.name));
        const pathTerm = sandboxConstructorTerm(path.name, [...parameterVars, ...pathArguments]);
        const fiberMotive = sandboxHitFiberMotive(
            signature,
            motiveName,
            path.resultIndices
        );
        const fiberHitType = sandboxHitFiberType(signature, path.resultIndices);
        const dependentHead = sandboxHitHeadAtIndices(sandboxApply(
            sandboxVar(`ind_${signature.name}`),
            ...parameterVars,
            sandboxVar(motiveName),
            ...branchNames.map(name => sandboxVar(name)),
            ...pathMethodNames.map(name => sandboxVar(name)),
            ...dependentTwoPathMethodNames.map(name => sandboxVar(name)),
            ...dependentThreePathMethodNames.map(name => sandboxVar(name))
        ), path.resultIndices);
        const fullDependentHead = sandboxHitHeadAtIndices(sandboxApply(
            sandboxVar(`@ind_${signature.name}`),
            sandboxVar(motiveUniverseName),
            ...parameterVars,
            sandboxVar(motiveName),
            ...branchNames.map(name => sandboxVar(name)),
            ...pathMethodNames.map(name => sandboxVar(name)),
            ...dependentTwoPathMethodNames.map(name => sandboxVar(name)),
            ...dependentThreePathMethodNames.map(name => sandboxVar(name))
        ), path.resultIndices);
        const recursorHead = sandboxHitHeadAtIndices(sandboxApply(
            sandboxVar(`rec_${signature.name}`),
            ...parameterVars,
            sandboxVar(motiveName),
            ...recursorBranchNames.map(name => sandboxVar(name)),
            ...recursorPathMethodNames.map(name => sandboxVar(name)),
            ...recursorTwoPathMethodNames.map(name => sandboxVar(name)),
            ...recursorThreePathMethodNames.map(name => sandboxVar(name))
        ), path.resultIndices);
        const fullRecursorHead = sandboxHitHeadAtIndices(sandboxApply(
            sandboxVar(`@rec_${signature.name}`),
            sandboxVar(motiveUniverseName),
            ...parameterVars,
            sandboxVar(motiveName),
            ...recursorBranchNames.map(name => sandboxVar(name)),
            ...recursorPathMethodNames.map(name => sandboxVar(name)),
            ...recursorTwoPathMethodNames.map(name => sandboxVar(name)),
            ...recursorThreePathMethodNames.map(name => sandboxVar(name))
        ), path.resultIndices);
        const dependentMethodValue = sandboxApply(
            sandboxVar(dependentTwoPathMethodNames[index]), ...pathArguments
        );
        const recursorMethodValue = sandboxApply(
            sandboxVar(recursorTwoPathMethodNames[index]), ...pathArguments
        );

        type DependentOnePathComputation = {
            term: AST;
            sourcePoint: AST;
            targetPoint: AST;
            sourceValue: AST;
            targetValue: AST;
            type: AST;
            method: AST;
            computation: AST;
        };
        const makeDependentOnePathComputation = (
            expression: SandboxHitOnePathExpression,
            head: AST,
            full: boolean
        ): DependentOnePathComputation => {
            if (expression.kind === "compose") {
                const left = makeDependentOnePathComputation(expression.left, head, full);
                const right = makeDependentOnePathComputation(expression.right, head, full);
                const method = sandboxApply(
                    sandboxVar("hit_dep1_comp"),
                    Core.clone(fiberMotive),
                    Core.clone(left.sourceValue),
                    Core.clone(left.targetValue),
                    Core.clone(right.targetValue),
                    Core.clone(left.method),
                    Core.clone(right.method)
                );
                const term = sandboxCompose(left.term, right.term);
                return {
                    term,
                    sourcePoint: left.sourcePoint,
                    targetPoint: right.targetPoint,
                    sourceValue: left.sourceValue,
                    targetValue: right.targetValue,
                    type: sandboxEquality(
                        sandboxApply(
                            sandboxVar("trans"),
                            Core.clone(fiberMotive),
                            Core.clone(term),
                            Core.clone(left.sourceValue)
                        ),
                        Core.clone(right.targetValue)
                    ),
                    method,
                    computation: sandboxApply(
                        sandboxVar("@hit_apd1_corrected_comp"),
                        Core.clone(hitUniverseLevel),
                        full ? sandboxVar(motiveUniverseName) : sandboxVar("@0"),
                        Core.clone(fiberHitType),
                        Core.clone(left.sourcePoint),
                        Core.clone(left.targetPoint),
                        Core.clone(right.targetPoint),
                        Core.clone(left.term),
                        Core.clone(right.term),
                        Core.clone(fiberMotive),
                        Core.clone(head),
                        Core.clone(left.method),
                        Core.clone(right.method),
                        Core.clone(left.computation),
                        Core.clone(right.computation)
                    )
                };
            }
            if (expression.kind === "inverse") {
                const value = makeDependentOnePathComputation(expression.value, head, full);
                const term = sandboxApply(sandboxVar("inveq"), value.term);
                const method = sandboxApply(
                    sandboxVar("hit_dep1_inv"),
                    Core.clone(fiberMotive),
                    Core.clone(value.sourceValue),
                    Core.clone(value.targetValue),
                    Core.clone(value.method)
                );
                return {
                    term,
                    sourcePoint: value.targetPoint,
                    targetPoint: value.sourcePoint,
                    sourceValue: value.targetValue,
                    targetValue: value.sourceValue,
                    type: sandboxEquality(
                        sandboxApply(
                            sandboxVar("trans"),
                            Core.clone(fiberMotive),
                            Core.clone(term),
                            Core.clone(value.targetValue)
                        ),
                        Core.clone(value.sourceValue)
                    ),
                    method,
                    computation: sandboxApply(
                        sandboxVar("@hit_apd1_corrected_inv"),
                        Core.clone(hitUniverseLevel),
                        full ? sandboxVar(motiveUniverseName) : sandboxVar("@0"),
                        Core.clone(fiberHitType),
                        Core.clone(value.sourcePoint),
                        Core.clone(value.targetPoint),
                        Core.clone(value.term),
                        Core.clone(fiberMotive),
                        Core.clone(head),
                        Core.clone(value.method),
                        Core.clone(value.computation)
                    )
                };
            }
            const data = sandboxHitOnePathExpressionData(
                expression, signature.parameters, pathConstructors, path.name
            );
            if (data.pathIndex === undefined || !data.arguments_) {
                throw new Error(`二维 HIT 一阶路径端点 ${path.name} 缺少原子路径数据`);
            }
            const atom = pathConstructors[data.pathIndex];
            const sourceValue = sandboxHitBranchValue(
                data.sourcePoint, signature.parameters, signature.pointConstructors, branchNames
            );
            const targetValue = sandboxHitBranchValue(
                data.targetPoint, signature.parameters, signature.pointConstructors, branchNames
            );
            const method = sandboxApply(
                sandboxVar(pathMethodNames[data.pathIndex]),
                ...data.arguments_.map(argument => Core.clone(argument))
            );
            return {
                term: data.term,
                sourcePoint: data.sourcePoint,
                targetPoint: data.targetPoint,
                sourceValue,
                targetValue,
                type: sandboxEquality(
                    sandboxApply(
                        sandboxVar("trans"),
                        Core.clone(fiberMotive),
                        Core.clone(data.term),
                        Core.clone(sourceValue)
                    ),
                    Core.clone(targetValue)
                ),
                method,
                computation: sandboxApply(
                    sandboxVar(`${full ? "@" : ""}apd_${atom.name}`),
                    ...(full ? [sandboxVar(motiveUniverseName)] : []),
                    ...parameterVars,
                    sandboxVar(motiveName),
                    ...branchNames.map(name => sandboxVar(name)),
                    ...pathMethodNames.map(name => sandboxVar(name)),
                    ...dependentTwoPathMethodNames.map(name => sandboxVar(name)),
                    ...dependentThreePathMethodNames.map(name => sandboxVar(name)),
                    ...data.arguments_.map(argument => Core.clone(argument))
                )
            };
        };
        type RecursorOnePathComputation = {
            term: AST;
            sourcePoint: AST;
            targetPoint: AST;
            method: AST;
            computation: AST;
        };
        const makeRecursorOnePathComputation = (
            expression: SandboxHitOnePathExpression,
            head: AST,
            full: boolean
        ): RecursorOnePathComputation => {
            if (expression.kind === "compose") {
                const left = makeRecursorOnePathComputation(expression.left, head, full);
                const right = makeRecursorOnePathComputation(expression.right, head, full);
                const method = sandboxCompose(left.method, right.method);
                return {
                    term: sandboxCompose(left.term, right.term),
                    sourcePoint: left.sourcePoint,
                    targetPoint: right.targetPoint,
                    method,
                    computation: sandboxApply(
                        sandboxVar("@hit_ap1_corrected_comp"),
                        Core.clone(hitUniverseLevel),
                        full ? sandboxVar(motiveUniverseName) : sandboxVar("@0"),
                        Core.clone(fiberHitType),
                        sandboxVar(motiveName),
                        Core.clone(left.sourcePoint),
                        Core.clone(left.targetPoint),
                        Core.clone(right.targetPoint),
                        Core.clone(left.term),
                        Core.clone(right.term),
                        Core.clone(head),
                        Core.clone(left.method),
                        Core.clone(right.method),
                        Core.clone(left.computation),
                        Core.clone(right.computation)
                    )
                };
            }
            if (expression.kind === "inverse") {
                const value = makeRecursorOnePathComputation(expression.value, head, full);
                const method = sandboxApply(sandboxVar("inveq"), value.method);
                return {
                    term: sandboxApply(sandboxVar("inveq"), value.term),
                    sourcePoint: value.targetPoint,
                    targetPoint: value.sourcePoint,
                    method,
                    computation: sandboxApply(
                        sandboxVar("@hit_ap1_corrected_inv"),
                        Core.clone(hitUniverseLevel),
                        full ? sandboxVar(motiveUniverseName) : sandboxVar("@0"),
                        Core.clone(fiberHitType),
                        sandboxVar(motiveName),
                        Core.clone(value.sourcePoint),
                        Core.clone(value.targetPoint),
                        Core.clone(value.term),
                        Core.clone(head),
                        Core.clone(value.method),
                        Core.clone(value.computation)
                    )
                };
            }
            const data = sandboxHitOnePathExpressionData(
                expression, signature.parameters, pathConstructors, path.name
            );
            if (data.pathIndex === undefined || !data.arguments_) {
                throw new Error(`二维 HIT 一阶路径端点 ${path.name} 缺少原子路径数据`);
            }
            const atom = pathConstructors[data.pathIndex];
            const method = sandboxApply(
                sandboxVar(recursorPathMethodNames[data.pathIndex]),
                ...data.arguments_.map(argument => Core.clone(argument))
            );
            return {
                term: data.term,
                sourcePoint: data.sourcePoint,
                targetPoint: data.targetPoint,
                method,
                computation: sandboxApply(
                    sandboxVar(`${full ? "@" : ""}ap_${atom.name}`),
                    ...(full ? [sandboxVar(motiveUniverseName)] : []),
                    ...parameterVars,
                    sandboxVar(motiveName),
                    ...recursorBranchNames.map(name => sandboxVar(name)),
                    ...recursorPathMethodNames.map(name => sandboxVar(name)),
                    ...recursorTwoPathMethodNames.map(name => sandboxVar(name)),
                    ...recursorThreePathMethodNames.map(name => sandboxVar(name)),
                    ...data.arguments_.map(argument => Core.clone(argument))
                )
            };
        };
        const leftPathData = makeDependentOnePathComputation(
            path.leftExpression, dependentHead, false
        );
        const rightPathData = makeDependentOnePathComputation(
            path.rightExpression, dependentHead, false
        );
        const leftPathDataFull = makeDependentOnePathComputation(
            path.leftExpression, fullDependentHead, true
        );
        const rightPathDataFull = makeDependentOnePathComputation(
            path.rightExpression, fullDependentHead, true
        );
        const leftRecursorData = makeRecursorOnePathComputation(
            path.leftExpression, recursorHead, false
        );
        const rightRecursorData = makeRecursorOnePathComputation(
            path.rightExpression, recursorHead, false
        );
        const leftRecursorDataFull = makeRecursorOnePathComputation(
            path.leftExpression, fullRecursorHead, true
        );
        const rightRecursorDataFull = makeRecursorOnePathComputation(
            path.rightExpression, fullRecursorHead, true
        );
        const endpointValue = leftPathData.sourceValue;
        const transport2Value = sandboxApply(
            sandboxVar("trans2"),
            Core.clone(fiberMotive),
            pathTerm,
            endpointValue
        );
        // Generated path computation theorems retain the HIT's uniform
        // parameters before the motive. Omitting them only works for
        // unparameterized HITs; for `hit SurfaceP (A : U)`, the old
        // expression treated `C` as `A` and made the final `apd2` slot fail
        // type checking.
        const leftDependentComputation = leftPathData.computation;
        const rightDependentComputation = rightPathData.computation;
        const leftDependentComputationFull = leftPathDataFull.computation;
        const rightDependentComputationFull = rightPathDataFull.computation;
        const leftRecursorComputation = leftRecursorData.computation;
        const rightRecursorComputation = rightRecursorData.computation;
        const leftRecursorComputationFull = leftRecursorDataFull.computation;
        const rightRecursorComputationFull = rightRecursorDataFull.computation;
        const lambdaScope = new Set<string>([
            ...coherenceScope,
            ...path.arguments.map(argument => argument.name)
        ]);
        collectSandboxAstNames(transport2Value, lambdaScope);
        collectSandboxAstNames(rightPathData.type, lambdaScope);
        const pathValueName = sandboxFreshName("pathValue", lambdaScope);
        const correctedDependentMethod = sandboxCompose(
            sandboxCompose(leftDependentComputation, dependentMethodValue),
            sandboxApply(
                sandboxVar("inveq"),
                sandboxApply(
                    sandboxVar("ap"),
                    sandboxLambda(
                        pathValueName,
                        rightPathData.type,
                        sandboxCompose(
                            Core.clone(transport2Value),
                            sandboxVar(pathValueName)
                        )
                    ),
                    rightDependentComputation
                )
            )
        );
        const correctedDependentMethodFull = sandboxCompose(
            sandboxCompose(leftDependentComputationFull, Core.clone(dependentMethodValue)),
            sandboxApply(
                sandboxVar("inveq"),
                sandboxApply(
                    sandboxVar("ap"),
                    sandboxLambda(
                        pathValueName,
                        rightPathData.type,
                        sandboxCompose(
                            Core.clone(transport2Value),
                            sandboxVar(pathValueName)
                        )
                    ),
                    rightDependentComputationFull
                )
            )
        );

        let publicApd2Type = sandboxWrapPis(path.arguments, sandboxEquality(
            sandboxApply(sandboxVar("apd2"), dependentHead, pathTerm),
            correctedDependentMethod
        ));
        publicApd2Type = sandboxWrapPis(allDependentPathBinders, publicApd2Type);
        publicApd2Type = sandboxWrapPis(
            extractSandboxPiBinders(
                base.eliminator![1], signature.parameters.length + 1,
                signature.pointConstructors.length
            ),
            publicApd2Type
        );
        publicApd2Type = sandboxPi(
            motiveName,
            extractSandboxPiBinder(base.eliminator![1], signature.parameters.length).type,
            publicApd2Type
        );
        publicApd2Type = sandboxWrapPis(signature.parameters, publicApd2Type);

        let fullApd2Type = sandboxWrapPis(path.arguments, sandboxEquality(
            sandboxApply(sandboxVar("apd2"), fullDependentHead, pathTerm),
            correctedDependentMethodFull
        ));
        fullApd2Type = sandboxWrapPis(allDependentPathBinders, fullApd2Type);
        fullApd2Type = sandboxWrapPis(
            extractSandboxPiBinders(
                fullEliminatorEntry[1], 1 + signature.parameters.length + 1,
                signature.pointConstructors.length
            ),
            fullApd2Type
        );
        fullApd2Type = sandboxPi(
            motiveName,
            extractSandboxPiBinder(fullEliminatorEntry[1], 1 + signature.parameters.length).type,
            fullApd2Type
        );
        fullApd2Type = sandboxWrapPis(signature.parameters, fullApd2Type);
        fullApd2Type = sandboxPi(motiveUniverseName, sandboxVar("U@"), fullApd2Type);

        const leftRecursorAction = sandboxApply(
            sandboxVar("ap"),
            recursorHead,
            leftRecursorData.term
        );
        const rightRecursorAction = sandboxApply(
            sandboxVar("ap"),
            recursorHead,
            rightRecursorData.term
        );
        let publicAp2Type = sandboxWrapPis(path.arguments, sandboxEquality(
            leftRecursorAction,
            rightRecursorAction
        ));
        publicAp2Type = sandboxWrapPis(allRecursorPathBinders, publicAp2Type);
        publicAp2Type = sandboxWrapPis(
            extractSandboxPiBinders(
                base.recursor![1], signature.parameters.length + 1,
                signature.pointConstructors.length
            ),
            publicAp2Type
        );
        publicAp2Type = sandboxPi(
            motiveName,
            extractSandboxPiBinder(base.recursor![1], signature.parameters.length).type,
            publicAp2Type
        );
        publicAp2Type = sandboxWrapPis(signature.parameters, publicAp2Type);

        const leftFullRecursorAction = sandboxApply(
            sandboxVar("ap"),
            fullRecursorHead,
            leftRecursorDataFull.term
        );
        const rightFullRecursorAction = sandboxApply(
            sandboxVar("ap"),
            fullRecursorHead,
            rightRecursorDataFull.term
        );
        let fullAp2Type = sandboxWrapPis(path.arguments, sandboxEquality(
            leftFullRecursorAction,
            rightFullRecursorAction
        ));
        fullAp2Type = sandboxWrapPis(allRecursorPathBinders, fullAp2Type);
        fullAp2Type = sandboxWrapPis(
            extractSandboxPiBinders(
                fullRecursorEntry[1], 1 + signature.parameters.length + 1,
                signature.pointConstructors.length
            ),
            fullAp2Type
        );
        fullAp2Type = sandboxPi(
            motiveName,
            extractSandboxPiBinder(fullRecursorEntry[1], 1 + signature.parameters.length).type,
            fullAp2Type
        );
        fullAp2Type = sandboxWrapPis(signature.parameters, fullAp2Type);
        fullAp2Type = sandboxPi(motiveUniverseName, sandboxVar("U@"), fullAp2Type);

        const correctedRecursorMethod = sandboxCompose(
            sandboxCompose(leftRecursorComputation, recursorMethodValue),
            sandboxApply(sandboxVar("inveq"), rightRecursorComputation)
        );
        const correctedRecursorMethodFull = sandboxCompose(
            sandboxCompose(leftRecursorComputationFull, Core.clone(recursorMethodValue)),
            sandboxApply(sandboxVar("inveq"), rightRecursorComputationFull)
        );
        const strongRecursorAction = (head: AST) => sandboxApply(
            sandboxVar("hit_ap2"),
            head,
            Core.clone(pathTerm)
        );
        let publicStrongAp2Type = sandboxWrapPis(path.arguments, sandboxEquality(
            strongRecursorAction(Core.clone(recursorHead)),
            correctedRecursorMethod
        ));
        publicStrongAp2Type = sandboxWrapPis(allRecursorPathBinders, publicStrongAp2Type);
        publicStrongAp2Type = sandboxWrapPis(
            extractSandboxPiBinders(
                base.recursor![1], signature.parameters.length + 1,
                signature.pointConstructors.length
            ),
            publicStrongAp2Type
        );
        publicStrongAp2Type = sandboxPi(
            motiveName,
            extractSandboxPiBinder(base.recursor![1], signature.parameters.length).type,
            publicStrongAp2Type
        );
        publicStrongAp2Type = sandboxWrapPis(signature.parameters, publicStrongAp2Type);

        let fullStrongAp2Type = sandboxWrapPis(path.arguments, sandboxEquality(
            strongRecursorAction(Core.clone(fullRecursorHead)),
            correctedRecursorMethodFull
        ));
        fullStrongAp2Type = sandboxWrapPis(allRecursorPathBinders, fullStrongAp2Type);
        fullStrongAp2Type = sandboxWrapPis(
            extractSandboxPiBinders(
                fullRecursorEntry[1], 1 + signature.parameters.length + 1,
                signature.pointConstructors.length
            ),
            fullStrongAp2Type
        );
        fullStrongAp2Type = sandboxPi(
            motiveName,
            extractSandboxPiBinder(fullRecursorEntry[1], 1 + signature.parameters.length).type,
            fullStrongAp2Type
        );
        fullStrongAp2Type = sandboxWrapPis(signature.parameters, fullStrongAp2Type);
        fullStrongAp2Type = sandboxPi(motiveUniverseName, sandboxVar("U@"), fullStrongAp2Type);

        computationTypes.push(
            [`apd_${path.name}`, publicApd2Type],
            [`@apd_${path.name}`, fullApd2Type],
            [`ap_${path.name}`, publicAp2Type],
            [`@ap_${path.name}`, fullAp2Type],
            [`ap2_${path.name}`, publicStrongAp2Type],
            [`@ap2_${path.name}`, fullStrongAp2Type]
        );
    }

    for (let index = 0; index < threePathConstructors.length; index++) {
        const path = threePathConstructors[index];
        const pathArguments = path.arguments.map(argument => sandboxVar(argument.name));
        const pathTerm = sandboxConstructorTerm(path.name, [...parameterVars, ...pathArguments]);
        const fiberMotive = sandboxHitFiberMotive(signature, motiveName, path.resultIndices);
        const fiberHitType = sandboxHitFiberType(signature, path.resultIndices);
        const dependentHead = sandboxHitHeadAtIndices(sandboxApply(
            sandboxVar(`ind_${signature.name}`),
            ...parameterVars,
            sandboxVar(motiveName),
            ...branchNames.map(name => sandboxVar(name)),
            ...pathMethodNames.map(name => sandboxVar(name)),
            ...dependentTwoPathMethodNames.map(name => sandboxVar(name)),
            ...dependentThreePathMethodNames.map(name => sandboxVar(name))
        ), path.resultIndices);
        const fullDependentHead = sandboxHitHeadAtIndices(sandboxApply(
            sandboxVar(`@ind_${signature.name}`),
            sandboxVar(motiveUniverseName),
            ...parameterVars,
            sandboxVar(motiveName),
            ...branchNames.map(name => sandboxVar(name)),
            ...pathMethodNames.map(name => sandboxVar(name)),
            ...dependentTwoPathMethodNames.map(name => sandboxVar(name)),
            ...dependentThreePathMethodNames.map(name => sandboxVar(name))
        ), path.resultIndices);
        const recursorHead = sandboxHitHeadAtIndices(sandboxApply(
            sandboxVar(`rec_${signature.name}`),
            ...parameterVars,
            sandboxVar(motiveName),
            ...recursorBranchNames.map(name => sandboxVar(name)),
            ...recursorPathMethodNames.map(name => sandboxVar(name)),
            ...recursorTwoPathMethodNames.map(name => sandboxVar(name)),
            ...recursorThreePathMethodNames.map(name => sandboxVar(name))
        ), path.resultIndices);
        const fullRecursorHead = sandboxHitHeadAtIndices(sandboxApply(
            sandboxVar(`@rec_${signature.name}`),
            sandboxVar(motiveUniverseName),
            ...parameterVars,
            sandboxVar(motiveName),
            ...recursorBranchNames.map(name => sandboxVar(name)),
            ...recursorPathMethodNames.map(name => sandboxVar(name)),
            ...recursorTwoPathMethodNames.map(name => sandboxVar(name)),
            ...recursorThreePathMethodNames.map(name => sandboxVar(name))
        ), path.resultIndices);
        const methodValue = sandboxApply(
            sandboxVar(recursorThreePathMethodNames[index]),
            ...pathArguments
        );
        const dependentMethodValue = sandboxApply(
            sandboxVar(dependentThreePathMethodNames[index]),
            ...pathArguments
        );
        const leftTwoPathTerm = sandboxHitTwoPathExpressionTerm(
            path.leftExpression, signature.parameters, pathConstructors,
            twoPathConstructors, path.name
        );
        const rightTwoPathTerm = sandboxHitTwoPathExpressionTerm(
            path.rightExpression, signature.parameters, pathConstructors,
            twoPathConstructors, path.name
        );
        const onePathBoundary = sandboxHitTwoPathExpressionOnePathBoundary(
            path.leftExpression, signature.parameters, pathConstructors,
            twoPathConstructors, path.name
        );
        const sourcePath = makeSharedDependentOnePathComputation(
            onePathBoundary.source, dependentHead, false, path.name,
            fiberMotive, fiberHitType
        );
        const targetPath = makeSharedDependentOnePathComputation(
            onePathBoundary.target, dependentHead, false, path.name,
            fiberMotive, fiberHitType
        );
        const sourcePathFull = makeSharedDependentOnePathComputation(
            onePathBoundary.source, fullDependentHead, true, path.name,
            fiberMotive, fiberHitType
        );
        const targetPathFull = makeSharedDependentOnePathComputation(
            onePathBoundary.target, fullDependentHead, true, path.name,
            fiberMotive, fiberHitType
        );
        const sourceRecursorPath = makeSharedRecursorOnePathComputation(
            onePathBoundary.source, recursorHead, false, path.name, fiberHitType
        );
        const targetRecursorPath = makeSharedRecursorOnePathComputation(
            onePathBoundary.target, recursorHead, false, path.name, fiberHitType
        );
        const sourceRecursorPathFull = makeSharedRecursorOnePathComputation(
            onePathBoundary.source, fullRecursorHead, true, path.name, fiberHitType
        );
        const targetRecursorPathFull = makeSharedRecursorOnePathComputation(
            onePathBoundary.target, fullRecursorHead, true, path.name, fiberHitType
        );
        const sourceDependentMethod = sourcePath.method;
        const targetDependentMethod = targetPath.method;
        const endpointValue = sourcePath.sourceValue;
        const targetEndpointValue = sourcePath.targetValue;
        const leftDependentExpression = dependentTwoPathExpressionMethod(
            path.leftExpression, path.name, endpointValue, targetEndpointValue
        );
        const rightDependentExpression = dependentTwoPathExpressionMethod(
            path.rightExpression, path.name, endpointValue, targetEndpointValue
        );
        const leftDependentTwoPathMethod = leftDependentExpression.proof;
        const rightDependentTwoPathMethod = rightDependentExpression.proof;
        const makeDependentTwoPathComputation = (
            expression: SandboxHitTwoPathExpression,
            head: AST,
            full: boolean
        ): {
            term: AST;
            sourcePath: AST;
            targetPath: AST;
            sourceMethod: AST;
            targetMethod: AST;
            method: AST;
            sourceComputation: AST;
            targetComputation: AST;
            proof: AST;
        } => {
            if (expression.kind === "compose") {
                const left = makeDependentTwoPathComputation(expression.left, head, full);
                const right = makeDependentTwoPathComputation(expression.right, head, full);
                const method = sandboxApply(
                    sandboxVar("hit_dep2_comp"),
                    Core.clone(fiberMotive),
                    Core.clone(endpointValue),
                    Core.clone(targetEndpointValue),
                    Core.clone(left.sourceMethod),
                    Core.clone(left.targetMethod),
                    Core.clone(right.targetMethod),
                    Core.clone(left.term),
                    Core.clone(right.term),
                    Core.clone(left.method),
                    Core.clone(right.method)
                );
                return {
                    term: sandboxCompose(left.term, right.term),
                    sourcePath: left.sourcePath,
                    targetPath: right.targetPath,
                    sourceMethod: left.sourceMethod,
                    targetMethod: right.targetMethod,
                    method,
                    sourceComputation: left.sourceComputation,
                    targetComputation: right.targetComputation,
                    proof: sandboxApply(
                        sandboxVar("@hit_apd2_corrected_comp"),
                        Core.clone(hitUniverseLevel),
                        full ? sandboxVar(motiveUniverseName) : sandboxVar("@0"),
                        Core.clone(fiberHitType),
                        Core.clone(path.sourcePoint),
                        Core.clone(path.targetPoint),
                        Core.clone(left.sourcePath),
                        Core.clone(left.targetPath),
                        Core.clone(right.targetPath),
                        sandboxVar(motiveName),
                        Core.clone(head),
                        Core.clone(left.sourceMethod),
                        Core.clone(left.targetMethod),
                        Core.clone(right.targetMethod),
                        Core.clone(left.term),
                        Core.clone(right.term),
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
            if (expression.kind === "inverse") {
                const value = makeDependentTwoPathComputation(expression.value, head, full);
                const method = sandboxApply(
                    sandboxVar("hit_dep2_inv"),
                    Core.clone(fiberMotive),
                    Core.clone(endpointValue),
                    Core.clone(targetEndpointValue),
                    Core.clone(value.sourceMethod),
                    Core.clone(value.targetMethod),
                    Core.clone(value.term),
                    Core.clone(value.method)
                );
                return {
                    term: sandboxApply(sandboxVar("inveq"), value.term),
                    sourcePath: value.targetPath,
                    targetPath: value.sourcePath,
                    sourceMethod: value.targetMethod,
                    targetMethod: value.sourceMethod,
                    method,
                    sourceComputation: value.targetComputation,
                    targetComputation: value.sourceComputation,
                    proof: sandboxApply(
                        sandboxVar("@hit_apd2_corrected_inv"),
                        Core.clone(hitUniverseLevel),
                        full ? sandboxVar(motiveUniverseName) : sandboxVar("@0"),
                        Core.clone(fiberHitType),
                        Core.clone(path.sourcePoint),
                        Core.clone(path.targetPoint),
                        Core.clone(value.sourcePath),
                        Core.clone(value.targetPath),
                        Core.clone(fiberMotive),
                        Core.clone(head),
                        Core.clone(value.sourceMethod),
                        Core.clone(value.targetMethod),
                        Core.clone(value.term),
                        Core.clone(value.sourceComputation),
                        Core.clone(value.targetComputation),
                        Core.clone(value.method),
                        Core.clone(value.proof)
                    )
                };
            }
            if (expression.kind === "refl") {
                const data = sandboxHitReflExpressionPathData(
                    expression, signature.parameters, pathConstructors, path.name
                );
                const sourceData = makeSharedDependentOnePathComputation(
                    {
                        kind: "atom",
                        name: data.path.name,
                        arguments: data.arguments_.map(argument => Core.clone(argument))
                    },
                    head,
                    full,
                    path.name,
                    fiberMotive,
                    fiberHitType
                );
                const sourceMethod = sourceData.method;
                const sourceComputation = sourceData.computation;
                const method = sandboxApply(sandboxVar("refl"), sourceMethod);
                return {
                    term: sandboxApply(sandboxVar("refl"), data.pathTerm),
                    sourcePath: Core.clone(data.pathTerm),
                    targetPath: Core.clone(data.pathTerm),
                    sourceMethod: Core.clone(sourceMethod),
                    targetMethod: Core.clone(sourceMethod),
                    method,
                    sourceComputation: Core.clone(sourceComputation),
                    targetComputation: Core.clone(sourceComputation),
                    proof: sandboxApply(
                        sandboxVar("@hit_apd2_corrected_refl"),
                        Core.clone(hitUniverseLevel),
                        full ? sandboxVar(motiveUniverseName) : sandboxVar("@0"),
                        Core.clone(fiberHitType),
                        Core.clone(path.sourcePoint),
                        Core.clone(path.targetPoint),
                        Core.clone(data.pathTerm),
                        Core.clone(fiberMotive),
                        Core.clone(head),
                        Core.clone(sourceMethod),
                        Core.clone(sourceComputation)
                    )
                };
            }
            const pathIndex = twoPathConstructors.findIndex(item => item.name === expression.name);
            if (pathIndex < 0) throw new Error(`未知的三维 HIT 二阶路径端点：${expression.name}`);
            const atom = twoPathConstructors[pathIndex];
            const replacements = new Map<string, AST>();
            atom.arguments.forEach((argument, index) => {
                replacements.set(argument.name, expression.arguments[index]);
            });
            const mapArgument = (ast: AST) => substituteSandboxFreeVars(ast, replacements);
            const atomSourceExpression = sandboxMapHitOnePathExpression(
                atom.leftExpression, mapArgument
            );
            const atomTargetExpression = sandboxMapHitOnePathExpression(
                atom.rightExpression, mapArgument
            );
            const sourceData = makeSharedDependentOnePathComputation(
                atomSourceExpression, head, full, path.name,
                fiberMotive, fiberHitType
            );
            const targetData = makeSharedDependentOnePathComputation(
                atomTargetExpression, head, full, path.name,
                fiberMotive, fiberHitType
            );
            const method = sandboxApply(
                sandboxVar(dependentTwoPathMethodNames[pathIndex]),
                ...expression.arguments.map(argument => Core.clone(argument))
            );
            return {
                term: sandboxHitTwoPathExpressionTerm(
                    expression, signature.parameters, pathConstructors,
                    twoPathConstructors, path.name
                ),
                sourcePath: sourceData.term,
                targetPath: targetData.term,
                sourceMethod: sourceData.method,
                targetMethod: targetData.method,
                method,
                sourceComputation: sourceData.computation,
                targetComputation: targetData.computation,
                proof: sandboxApply(
                    sandboxVar(`${full ? "@" : ""}apd_${atom.name}`),
                    ...(full ? [sandboxVar(motiveUniverseName)] : []),
                    ...parameterVars,
                    sandboxVar(motiveName),
                    ...branchNames.map(name => sandboxVar(name)),
                    ...pathMethodNames.map(name => sandboxVar(name)),
                    ...dependentTwoPathMethodNames.map(name => sandboxVar(name)),
                    ...dependentThreePathMethodNames.map(name => sandboxVar(name)),
                    ...expression.arguments.map(argument => Core.clone(argument))
                )
            };
        };
        const sourceDependentComputation = sourcePath.computation;
        const targetDependentComputation = targetPath.computation;
        const sourceDependentComputationFull = sourcePathFull.computation;
        const targetDependentComputationFull = targetPathFull.computation;
        const leftDependentTwoPathComputation = makeDependentTwoPathComputation(
            path.leftExpression, dependentHead, false
        ).proof;
        const rightDependentTwoPathComputation = makeDependentTwoPathComputation(
            path.rightExpression, dependentHead, false
        ).proof;
        const leftDependentTwoPathComputationFull = makeDependentTwoPathComputation(
            path.leftExpression, fullDependentHead, true
        ).proof;
        const rightDependentTwoPathComputationFull = makeDependentTwoPathComputation(
            path.rightExpression, fullDependentHead, true
        ).proof;
        const dependentCorrectionScope = new Set<string>([
            ...coherenceScope,
            ...path.arguments.map(argument => argument.name)
        ]);
        const dependentTwoPathName = sandboxFreshName(
            "dependentTwoPathValue", dependentCorrectionScope
        );
        const dependentMethodName = sandboxFreshName(
            "dependentTwoPathMethod", dependentCorrectionScope
        );
        const dependentTargetPathName = sandboxFreshName(
            "dependentTargetPathValue", dependentCorrectionScope
        );
        const dependentTwoPathDomain = sandboxEquality(
            Core.clone(sourcePath.term),
            Core.clone(targetPath.term)
        );
        const rawDependentFamily = (twoPathValue: AST) => sandboxEquality(
            Core.clone(sourceDependentMethod),
            sandboxCompose(
                sandboxApply(
                    sandboxVar("trans2"),
                    Core.clone(fiberMotive),
                    twoPathValue,
                    Core.clone(endpointValue)
                ),
                Core.clone(targetDependentMethod)
            )
        );
        const actualDependentFamily = (head: AST, twoPathValue: AST) => sandboxEquality(
            sandboxApply(
                sandboxVar("apd"),
                Core.clone(head),
                Core.clone(sourcePath.term)
            ),
            sandboxCompose(
                sandboxApply(
                    sandboxVar("trans2"),
                    Core.clone(fiberMotive),
                    twoPathValue,
                    Core.clone(endpointValue)
                ),
                sandboxApply(
                    sandboxVar("apd"),
                    Core.clone(head),
                Core.clone(targetPath.term)
                )
            )
        );
        const dependentCorrection = (
            sourceComputation: AST,
            targetComputation: AST
        ) => {
            const twoPathValue = sandboxVar(dependentTwoPathName);
            const method = sandboxVar(dependentMethodName);
            const targetWhisker = sandboxLambda(
                dependentTargetPathName,
                Core.clone(targetPath.type),
                sandboxCompose(
                    sandboxApply(
                        sandboxVar("trans2"),
                        Core.clone(fiberMotive),
                        Core.clone(twoPathValue),
                        Core.clone(endpointValue)
                    ),
                    sandboxVar(dependentTargetPathName)
                )
            );
            return sandboxLambda(
                dependentTwoPathName,
                Core.clone(dependentTwoPathDomain),
                sandboxLambda(
                    dependentMethodName,
                    rawDependentFamily(Core.clone(twoPathValue)),
                    sandboxCompose(
                        sandboxCompose(Core.clone(sourceComputation), method),
                        sandboxApply(
                            sandboxVar("inveq"),
                            sandboxApply(
                                sandboxVar("ap"),
                                targetWhisker,
                                Core.clone(targetComputation)
                            )
                        )
                    )
                )
            );
        };
        const publicDependentCorrection = dependentCorrection(
            sourceDependentComputation,
            targetDependentComputation
        );
        const fullDependentCorrection = dependentCorrection(
            sourceDependentComputationFull,
            targetDependentComputationFull
        );
        const mappedDependentMethod = sandboxApply(
            sandboxVar("hit_map_transport"),
            publicDependentCorrection,
            Core.clone(leftTwoPathTerm),
            Core.clone(rightTwoPathTerm),
            Core.clone(pathTerm),
            Core.clone(leftDependentTwoPathMethod),
            Core.clone(rightDependentTwoPathMethod),
            Core.clone(dependentMethodValue)
        );
        const mappedDependentMethodFull = sandboxApply(
            sandboxVar("hit_map_transport"),
            fullDependentCorrection,
            Core.clone(leftTwoPathTerm),
            Core.clone(rightTwoPathTerm),
            Core.clone(pathTerm),
            Core.clone(leftDependentTwoPathMethod),
            Core.clone(rightDependentTwoPathMethod),
            Core.clone(dependentMethodValue)
        );
        const publicActualFamily = sandboxLambda(
            dependentTwoPathName,
            Core.clone(dependentTwoPathDomain),
            actualDependentFamily(dependentHead, sandboxVar(dependentTwoPathName))
        );
        const fullActualFamily = sandboxLambda(
            dependentTwoPathName,
            Core.clone(dependentTwoPathDomain),
            actualDependentFamily(fullDependentHead, sandboxVar(dependentTwoPathName))
        );
        const transportedComputation = (
            actualFamily: AST,
            leftComputation: AST
        ) => {
            const leftActualType = actualDependentFamily(
                actualFamily === publicActualFamily ? dependentHead : fullDependentHead,
                Core.clone(leftTwoPathTerm)
            );
            const valueName = sandboxFreshName(
                "dependentCorrectedValue", dependentCorrectionScope
            );
            return sandboxApply(
                sandboxVar("ap"),
                sandboxLambda(
                    valueName,
                    leftActualType,
                    sandboxApply(
                        sandboxVar("trans"),
                        Core.clone(actualFamily),
                        Core.clone(pathTerm),
                        sandboxVar(valueName)
                    )
                ),
                leftComputation
            );
        };
        const correctedDependentThreeMethod = sandboxCompose(
            sandboxCompose(
                transportedComputation(
                    publicActualFamily,
                    leftDependentTwoPathComputation
                ),
                mappedDependentMethod
            ),
            sandboxApply(
                sandboxVar("inveq"),
                rightDependentTwoPathComputation
            )
        );
        const correctedDependentThreeMethodFull = sandboxCompose(
            sandboxCompose(
                transportedComputation(
                    fullActualFamily,
                    leftDependentTwoPathComputationFull
                ),
                mappedDependentMethodFull
            ),
            sandboxApply(
                sandboxVar("inveq"),
                rightDependentTwoPathComputationFull
            )
        );
        const makeRecursorPathComputation = (
            data: ReturnType<typeof sandboxHitPathData>,
            full: boolean
        ) => sandboxApply(
            sandboxVar(`${full ? "@" : ""}ap_${data.path.name}`),
            ...(full ? [sandboxVar(motiveUniverseName)] : []),
            ...parameterVars,
            sandboxVar(motiveName),
            ...recursorBranchNames.map(name => sandboxVar(name)),
            ...recursorPathMethodNames.map(name => sandboxVar(name)),
            ...recursorTwoPathMethodNames.map(name => sandboxVar(name)),
            ...recursorThreePathMethodNames.map(name => sandboxVar(name)),
            ...data.arguments_
        );
        const correctionScope = new Set<string>([
            ...coherenceScope,
            ...path.arguments.map(argument => argument.name)
        ]);
        const makeStrongTwoPathComputation = (
            expression: SandboxHitTwoPathExpression,
            head: AST,
            full: boolean
        ): {
            term: AST;
            sourcePath: AST;
            targetPath: AST;
            sourceMethod: AST;
            targetMethod: AST;
            corrected: AST;
            sourceComputation: AST;
            targetComputation: AST;
            proof: AST;
        } => {
            if (expression.kind === "compose") {
                const left = makeStrongTwoPathComputation(expression.left, head, full);
                const right = makeStrongTwoPathComputation(expression.right, head, full);
                const corrected = sandboxCompose(left.corrected, right.corrected);
                return {
                    term: sandboxCompose(left.term, right.term),
                    sourcePath: left.sourcePath,
                    targetPath: right.targetPath,
                    sourceMethod: left.sourceMethod,
                    targetMethod: right.targetMethod,
                    corrected,
                    sourceComputation: left.sourceComputation,
                    targetComputation: right.targetComputation,
                    proof: sandboxApply(
                        sandboxVar("@hit_ap2_corrected_comp"),
                        Core.clone(hitUniverseLevel),
                        full ? sandboxVar(motiveUniverseName) : sandboxVar("@0"),
                        Core.clone(fiberHitType),
                        sandboxVar(motiveName),
                        Core.clone(path.sourcePoint),
                        Core.clone(path.targetPoint),
                        Core.clone(left.sourcePath),
                        Core.clone(left.targetPath),
                        Core.clone(right.targetPath),
                        Core.clone(head),
                        Core.clone(left.sourceMethod),
                        Core.clone(left.targetMethod),
                        Core.clone(right.targetMethod),
                        Core.clone(left.term),
                        Core.clone(right.term),
                        Core.clone(left.sourceComputation),
                        Core.clone(left.targetComputation),
                        Core.clone(right.targetComputation),
                        Core.clone(left.corrected),
                        Core.clone(right.corrected),
                        Core.clone(left.proof),
                        Core.clone(right.proof)
                    )
                };
            }
            if (expression.kind === "inverse") {
                const value = makeStrongTwoPathComputation(expression.value, head, full);
                return {
                    term: sandboxApply(sandboxVar("inveq"), value.term),
                    sourcePath: value.targetPath,
                    targetPath: value.sourcePath,
                    sourceMethod: value.targetMethod,
                    targetMethod: value.sourceMethod,
                    corrected: sandboxApply(sandboxVar("inveq"), value.corrected),
                    sourceComputation: value.targetComputation,
                    targetComputation: value.sourceComputation,
                    proof: sandboxApply(
                        sandboxVar("@hit_ap2_corrected_inv"),
                        Core.clone(hitUniverseLevel),
                        full ? sandboxVar(motiveUniverseName) : sandboxVar("@0"),
                        Core.clone(fiberHitType),
                        sandboxVar(motiveName),
                        Core.clone(path.sourcePoint),
                        Core.clone(path.targetPoint),
                        Core.clone(value.sourcePath),
                        Core.clone(value.targetPath),
                        Core.clone(head),
                        Core.clone(value.sourceMethod),
                        Core.clone(value.targetMethod),
                        Core.clone(value.term),
                        Core.clone(value.sourceComputation),
                        Core.clone(value.targetComputation),
                        Core.clone(value.corrected),
                        Core.clone(value.proof)
                    )
                };
            }
            if (expression.kind === "refl") {
                const data = sandboxHitReflExpressionPathData(
                    expression, signature.parameters, pathConstructors, path.name
                );
                const sourceMethod = sandboxApply(
                    sandboxVar(recursorPathMethodNames[data.pathIndex]),
                    ...data.arguments_
                );
                const sourcePathData = sandboxHitPathData(
                    data.pathTerm,
                    signature.parameters,
                    signature.pointConstructors,
                    pathConstructors,
                    motiveName,
                    recursorBranchNames,
                    path.name,
                    fiberMotive
                );
                const sourceComputation = makeRecursorPathComputation(sourcePathData, full);
                const corrected = sandboxApply(sandboxVar("refl"), sourceMethod);
                return {
                    term: sandboxApply(sandboxVar("refl"), data.pathTerm),
                    sourcePath: Core.clone(data.pathTerm),
                    targetPath: Core.clone(data.pathTerm),
                    sourceMethod: Core.clone(sourceMethod),
                    targetMethod: Core.clone(sourceMethod),
                    corrected,
                    sourceComputation: Core.clone(sourceComputation),
                    targetComputation: Core.clone(sourceComputation),
                    proof: sandboxApply(
                        sandboxVar("@hit_ap2_corrected_refl"),
                        Core.clone(hitUniverseLevel),
                        full ? sandboxVar(motiveUniverseName) : sandboxVar("@0"),
                        Core.clone(fiberHitType),
                        sandboxVar(motiveName),
                        Core.clone(path.sourcePoint),
                        Core.clone(path.targetPoint),
                        Core.clone(data.pathTerm),
                        Core.clone(head),
                        Core.clone(sourceMethod),
                        Core.clone(sourceComputation)
                    )
                };
            }
            const pathIndex = twoPathConstructors.findIndex(item => item.name === expression.name);
            if (pathIndex < 0) throw new Error(`未知的三维 HIT 二阶路径端点：${expression.name}`);
            const atom = twoPathConstructors[pathIndex];
            const proof = sandboxApply(
                sandboxVar(`${full ? "@" : ""}ap2_${atom.name}`),
                ...(full ? [sandboxVar(motiveUniverseName)] : []),
                ...parameterVars,
                sandboxVar(motiveName),
                ...recursorBranchNames.map(name => sandboxVar(name)),
                ...recursorPathMethodNames.map(name => sandboxVar(name)),
                ...recursorTwoPathMethodNames.map(name => sandboxVar(name)),
                ...recursorThreePathMethodNames.map(name => sandboxVar(name)),
                ...expression.arguments.map(argument => Core.clone(argument))
            );
            const boundary = sandboxHitTwoPathExpressionOnePathBoundary(
                expression, signature.parameters, pathConstructors,
                twoPathConstructors, path.name
            );
            const sourceData = makeSharedRecursorOnePathComputation(
                boundary.source, head, full, path.name, fiberHitType
            );
            const targetData = makeSharedRecursorOnePathComputation(
                boundary.target, head, full, path.name, fiberHitType
            );
            return {
                term: sandboxHitTwoPathExpressionTerm(
                    expression, signature.parameters, pathConstructors,
                    twoPathConstructors, path.name
                ),
                sourcePath: sourceData.term,
                targetPath: targetData.term,
                sourceMethod: sourceData.method,
                targetMethod: targetData.method,
                corrected: sandboxHitTwoPathExpressionMethodValue(
                    expression, signature.parameters, pathConstructors,
                    recursorPathMethodNames, twoPathConstructors,
                    recursorTwoPathMethodNames, path.name
                ),
                sourceComputation: sourceData.computation,
                targetComputation: targetData.computation,
                proof
            };
        };
        const leftPathComputation = sourceRecursorPath.computation;
        const rightPathComputation = targetRecursorPath.computation;
        const leftPathComputationFull = sourceRecursorPathFull.computation;
        const rightPathComputationFull = targetRecursorPathFull.computation;
        const leftStrongComputation = makeStrongTwoPathComputation(
            path.leftExpression, recursorHead, false
        ).proof;
        const rightStrongComputation = makeStrongTwoPathComputation(
            path.rightExpression, recursorHead, false
        ).proof;
        const leftStrongComputationFull = makeStrongTwoPathComputation(
            path.leftExpression, fullRecursorHead, true
        ).proof;
        const rightStrongComputationFull = makeStrongTwoPathComputation(
            path.rightExpression, fullRecursorHead, true
        ).proof;
        const sourceMethod = sourceRecursorPath.method;
        const targetMethod = targetRecursorPath.method;
        const methodName = sandboxFreshName("twoPathMethod", correctionScope);
        const correction = (
            leftComputation: AST,
            rightComputation: AST
        ) => sandboxLambda(
            methodName,
            sandboxEquality(Core.clone(sourceMethod), Core.clone(targetMethod)),
            sandboxCompose(
                sandboxCompose(leftComputation, sandboxVar(methodName)),
                sandboxApply(sandboxVar("inveq"), rightComputation)
            )
        );
        const correctedMethod = sandboxCompose(
            sandboxCompose(
                leftStrongComputation,
                sandboxApply(
                    sandboxVar("ap"),
                    correction(leftPathComputation, rightPathComputation),
                    methodValue
                )
            ),
            sandboxApply(sandboxVar("inveq"), rightStrongComputation)
        );
        const correctedMethodFull = sandboxCompose(
            sandboxCompose(
                leftStrongComputationFull,
                sandboxApply(
                    sandboxVar("ap"),
                    correction(leftPathComputationFull, rightPathComputationFull),
                    Core.clone(methodValue)
                )
            ),
            sandboxApply(sandboxVar("inveq"), rightStrongComputationFull)
        );

        let publicApd3Type = sandboxWrapPis(path.arguments, sandboxEquality(
            sandboxApply(sandboxVar("apd3"), dependentHead, pathTerm),
            correctedDependentThreeMethod
        ));
        publicApd3Type = sandboxWrapPis(allDependentPathBinders, publicApd3Type);
        publicApd3Type = sandboxWrapPis(
            extractSandboxPiBinders(
                base.eliminator![1], signature.parameters.length + 1,
                signature.pointConstructors.length
            ),
            publicApd3Type
        );
        publicApd3Type = sandboxPi(
            motiveName,
            extractSandboxPiBinder(base.eliminator![1], signature.parameters.length).type,
            publicApd3Type
        );
        publicApd3Type = sandboxWrapPis(signature.parameters, publicApd3Type);

        let fullApd3Type = sandboxWrapPis(path.arguments, sandboxEquality(
            sandboxApply(sandboxVar("apd3"), fullDependentHead, Core.clone(pathTerm)),
            correctedDependentThreeMethodFull
        ));
        fullApd3Type = sandboxWrapPis(allDependentPathBinders, fullApd3Type);
        fullApd3Type = sandboxWrapPis(
            extractSandboxPiBinders(
                fullEliminatorEntry[1], 1 + signature.parameters.length + 1,
                signature.pointConstructors.length
            ),
            fullApd3Type
        );
        fullApd3Type = sandboxPi(
            motiveName,
            extractSandboxPiBinder(fullEliminatorEntry[1], 1 + signature.parameters.length).type,
            fullApd3Type
        );
        fullApd3Type = sandboxWrapPis(signature.parameters, fullApd3Type);
        fullApd3Type = sandboxPi(motiveUniverseName, sandboxVar("U@"), fullApd3Type);

        let publicAp3Type = sandboxWrapPis(path.arguments, sandboxEquality(
            sandboxApply(sandboxVar("ap3"), recursorHead, pathTerm),
            correctedMethod
        ));
        publicAp3Type = sandboxWrapPis(allRecursorPathBinders, publicAp3Type);
        publicAp3Type = sandboxWrapPis(
            extractSandboxPiBinders(
                base.recursor![1], signature.parameters.length + 1,
                signature.pointConstructors.length
            ),
            publicAp3Type
        );
        publicAp3Type = sandboxPi(
            motiveName,
            extractSandboxPiBinder(base.recursor![1], signature.parameters.length).type,
            publicAp3Type
        );
        publicAp3Type = sandboxWrapPis(signature.parameters, publicAp3Type);

        let fullAp3Type = sandboxWrapPis(path.arguments, sandboxEquality(
            sandboxApply(sandboxVar("ap3"), fullRecursorHead, Core.clone(pathTerm)),
            correctedMethodFull
        ));
        fullAp3Type = sandboxWrapPis(allRecursorPathBinders, fullAp3Type);
        fullAp3Type = sandboxWrapPis(
            extractSandboxPiBinders(
                fullRecursorEntry[1], 1 + signature.parameters.length + 1,
                signature.pointConstructors.length
            ),
            fullAp3Type
        );
        fullAp3Type = sandboxPi(
            motiveName,
            extractSandboxPiBinder(fullRecursorEntry[1], 1 + signature.parameters.length).type,
            fullAp3Type
        );
        fullAp3Type = sandboxWrapPis(signature.parameters, fullAp3Type);
        fullAp3Type = sandboxPi(motiveUniverseName, sandboxVar("U@"), fullAp3Type);

        computationTypes.push(
            [`apd3_${path.name}`, publicApd3Type],
            [`@apd3_${path.name}`, fullApd3Type],
            [`ap3_${path.name}`, publicAp3Type],
            [`@ap3_${path.name}`, fullAp3Type]
        );
    }

    const generatedNames = [
        signature.name,
        ...signature.pointConstructors.map(constructor => constructor.name),
        ...pathConstructors.map(path => path.name),
        `ind_${signature.name}`,
        `@ind_${signature.name}`,
        `rec_${signature.name}`,
        `@rec_${signature.name}`,
        ...pathConstructors.flatMap(path => [
            `apd_${path.name}`,
            `@apd_${path.name}`,
            `ap_${path.name}`,
            `@ap_${path.name}`
        ]),
        ...twoPathConstructors.flatMap(path => [
            path.name,
            `apd_${path.name}`,
            `@apd_${path.name}`,
            `ap_${path.name}`,
            `@ap_${path.name}`,
            `ap2_${path.name}`,
            `@ap2_${path.name}`
        ]),
        ...threePathConstructors.flatMap(path => [
            path.name,
            `apd3_${path.name}`,
            `@apd3_${path.name}`,
            `ap3_${path.name}`,
            `@ap3_${path.name}`
        ])
    ];
    const metadataPathConstructors = pathConstructors.map(path => ({
        name: path.name,
        argumentTypes: path.arguments.map(argument => Core.clone(argument.type)),
        argumentNames: path.arguments.map(argument => argument.name),
        left: Core.clone(path.left),
        right: Core.clone(path.right),
        resultIndices: path.resultIndices.map(index => Core.clone(index)),
        computationName: `apd_${path.name}`
    }));
    const metadataTwoPathConstructors = twoPathConstructors.map(path => ({
        name: path.name,
        argumentTypes: path.arguments.map(argument => Core.clone(argument.type)),
        argumentNames: path.arguments.map(argument => argument.name),
        leftExpression: structuredClone(path.leftExpression),
        rightExpression: structuredClone(path.rightExpression),
        resultIndices: path.resultIndices.map(index => Core.clone(index)),
        computationName: `apd_${path.name}`,
        strongComputationName: `ap2_${path.name}`
    }));
    const metadataThreePathConstructors = threePathConstructors.map(path => ({
        name: path.name,
        argumentTypes: path.arguments.map(argument => Core.clone(argument.type)),
        argumentNames: path.arguments.map(argument => argument.name),
        leftExpression: structuredClone(path.leftExpression),
        rightExpression: structuredClone(path.rightExpression),
        resultIndices: path.resultIndices.map(index => Core.clone(index)),
        computationName: `apd3_${path.name}`,
        actionComputationName: `ap3_${path.name}`
    }));
    const metadataPathLevels: CoreHitPathLevels = createHitPathLevels(
        metadataPathConstructors,
        metadataTwoPathConstructors,
        metadataThreePathConstructors
    );
    const dimension = highestHitPathLevel(signature.pathLevels);
    return {
        type: [base.type[0], Core.clone(base.type[1])],
        constructors: base.constructors.map(([name, type]) => [name, Core.clone(type)]),
        auxiliaryTypes: [
            ...pathTypes,
            [`@ind_${signature.name}`, fullEliminatorType],
            [`@rec_${signature.name}`, fullRecursorType],
            ...computationTypes
        ],
        eliminator: [`ind_${signature.name}`, publicEliminatorType],
        recursor: [`rec_${signature.name}`, publicRecursorType],
        computeRules,
        metadata: {
            version: 8,
            kind: dimension === 3 ? "hit3" : dimension === 2 ? "hit2" : "hit1",
            dimension,
            ruleSchemaVersion: 1,
            typeName: signature.name,
            parameterCount: signature.parameters.length,
            indexCount: signature.indices.length,
            indices: signature.indices.map(index => ({
                name: index.name,
                type: Core.clone(index.type)
            })),
            eliminatorName: `ind_${signature.name}`,
            fullEliminatorName: `@ind_${signature.name}`,
            recursorName: `rec_${signature.name}`,
            fullRecursorName: `@rec_${signature.name}`,
            constructors: (base.metadata?.constructors ?? []).map(constructor => ({
                name: constructor.name,
                argumentTypes: constructor.argumentTypes.map(type => Core.clone(type)),
                argumentNames: constructor.argumentNames ? [...constructor.argumentNames] : undefined,
                recursiveArguments: constructor.recursiveArguments?.map(argument => ({
                    index: argument.index,
                    telescope: argument.telescope.map(binder => ({
                        name: binder.name,
                        type: Core.clone(binder.type)
                    })),
                    resultIndices: argument.resultIndices.map(index => Core.clone(index))
                })),
                resultIndices: constructor.resultIndices?.map(index => Core.clone(index))
            })),
            pathLevels: metadataPathLevels
        },
        generatedNames
    } as SandboxInductiveBundle;
}

function extractSandboxPiBinder(type: AST, depth: number): SandboxInductiveBinder {
    let cursor = type;
    for (let index = 0; index < depth; index++) {
        if ((cursor.type !== "P" && cursor.type !== "->") || !cursor.nodes?.[1]) {
            throw new Error("HIT 消去器 binder 结构不完整");
        }
        cursor = cursor.nodes[1];
    }
    if ((cursor.type !== "P" && cursor.type !== "->") || !cursor.nodes?.[0]) {
        throw new Error("HIT 消去器 binder 结构不完整");
    }
    return {
        name: cursor.type === "P" && cursor.name ? cursor.name : `x${depth}`,
        type: Core.clone(cursor.nodes[0]),
        typeSource: parser.stringify(cursor.nodes[0])
    };
}

function extractSandboxPiBinders(type: AST, depth: number, count: number) {
    return Array.from({ length: count }, (_, index) =>
        extractSandboxPiBinder(type, depth + index)
    );
}

function parseOrdinarySandboxAst(ast: AST): ParsedSandboxDeclaration {
    if ((ast.type !== ":" && ast.type !== ":=") || ast.nodes?.[0]?.type !== "var") {
        throw new Error("沙盒声明必须使用“名称 : 类型”或“名称 := 项”格式");
    }
    const name = ast.nodes[0].name;
    if (!/^(?:[A-Za-z_][A-Za-z0-9_']*|[0-9]+[A-Za-z_][A-Za-z0-9_']*)$/.test(name)) {
        throw new Error(`声明名称不合法：${name}`);
    }
    if (ast.type === ":=") {
        const rhs = ast.nodes[1];
        if (!rhs) throw new Error("定义缺少右侧项");
        if (rhs.type === ":") {
            if (!rhs.nodes?.[0] || !rhs.nodes?.[1]) throw new Error("定义类型注释不完整");
            return {
                ast,
                name,
                typeAst: rhs.nodes[1],
                typeSource: parser.stringify(rhs.nodes[1]),
                definitionAst: rhs.nodes[0]
            } satisfies ParsedSandboxDeclaration;
        }
        return {
            ast,
            name,
            typeSource: "",
            definitionAst: rhs
        } satisfies ParsedSandboxDeclaration;
    }
    return {
        ast,
        name,
        typeAst: ast.nodes[1],
        typeSource: parser.stringify(ast.nodes[1])
    } satisfies ParsedSandboxDeclaration;
}

export function parseSandboxDeclaration(source: string): ParsedSandboxDeclaration {
    const text = normalizeSandboxSource(source);
    if (!text) throw new Error("声明不能为空");
    if (/^hit\s/i.test(text)) {
        const hit = parseSandboxHit(text);
        const typeAst = sandboxWrapPis(
            [...hit.parameters, ...hit.indices],
            Core.clone(hit.universeAst)
        );
        return {
            ast: undefined,
            name: hit.name,
            typeAst,
            typeSource: parser.stringify(typeAst),
            hit
        };
    }
    if (/^inductive\s/i.test(text)) {
        const inductive = parseSandboxInductive(text);
        return {
            ast: undefined,
            name: inductive.name,
            typeAst: sandboxWrapPis(
                [...inductive.parameters, ...inductive.indices],
                Core.clone(inductive.universeAst)
            ),
            typeSource: parser.stringify(
                sandboxWrapPis(
                    [...inductive.parameters, ...inductive.indices],
                    Core.clone(inductive.universeAst)
                )
            ),
            inductive
        };
    }
    // This exported parser is also the compatibility boundary used by
    // migrated saves, workers, and existing programmatic fixtures. Strict
    // rejection belongs to the browser editor, not this low-level API.
    return parseOrdinarySandboxAst(parser.parse(text));
}

/** Parse a declaration entered through the new Unicode-facing editor. */
export function parseSandboxDeclarationSurface(source: string): ParsedSandboxDeclaration {
    // Pasted/user-entered aliases must be expanded before legacy detection.
    // Otherwise `\\*` is mistaken for the old `*` operator and rejected even
    // though it is the supported surface spelling for `▪`.
    const text = expandTypeTheoryAliasesInSurface(normalizeSandboxSource(source));
    if (!text) throw new Error("声明不能为空");
    if (hasLegacySurfaceSyntax(text)) {
        throw new Error("不再支持旧语法，请使用 Unicode 符号");
    }
    if (/^(?:hit|inductive)\s/i.test(text)) return parseSandboxDeclaration(text);
    return parseOrdinarySandboxAst(parser.parseSurface(text));
}

/** Parse a stored declaration at either the modern or legacy boundary. */
function parseSandboxStoredDeclaration(source: string): ParsedSandboxDeclaration {
    const text = normalizeSandboxSource(source);
    try {
        return parseSandboxDeclarationSurface(text);
    } catch (surfaceError) {
        try {
            return parseSandboxDeclaration(text);
        } catch {
            throw surfaceError;
        }
    }
}

function sandboxDraftName(source: string): string {
    const inductive = /^(?:hit|inductive)\s+([^\s(:\[]+)/i.exec(source);
    if (inductive) return inductive[1];
    return /^([^\s:]+)\s*(?::=|:)/.exec(source)?.[1] ?? "";
}

function sandboxDraftKind(source: string): SandboxDeclarationKind {
    if (/^hit\b/i.test(source)) return "hit";
    if (/^inductive\b/i.test(source)) return "inductive";
    if (/:=/.test(source)) return "definition";
    return "term";
}

/** Create an editable GUI draft without constructing ASTs or trusting derived declaration data. */
export function createSandboxDraftDeclaration(
    source: string,
    id: string,
    seed: Partial<SandboxSavedDeclaration> = {},
    maxSourceChars?: number
): SandboxDeclaration {
    const text = expandTypeTheoryAliasesInSurface(normalizeSandboxSource(String(source ?? "")));
    const enabled = seed.enabled !== false;
    const error = sandboxSourceLimitError(text, maxSourceChars);
    return {
        id,
        name: seed.name ?? sandboxDraftName(text),
        kind: seed.kind ?? sandboxDraftKind(text),
        source: text,
        typeSource: seed.typeSource ?? "",
        enabled,
        trusted: true,
        status: enabled ? "unchecked" : "disabled",
        ...(error ? { error } : {}),
        dependencies: [],
        folderId: seed.folderId ?? null
    };
}

export function createSandboxDeclaration(
    source: string,
    id: string,
    maxSourceChars?: number
): SandboxDeclaration {
    // Keep the creation path consistent with the strict editor boundary.
    // The keyboard normally expands aliases on Space, but pasted text can
    // reach this API directly (and the GUI passes the original input after
    // validation).  Expand it here before the compatibility parser sees it.
    const rawSource = String(source ?? "");
    const normalizedMaxSourceChars = normalizeSandboxLimit(maxSourceChars);
    const rawLimitError = sandboxSourceLimitError(rawSource, normalizedMaxSourceChars);
    if (rawLimitError) {
        return {
            id,
            name: "",
            kind: "term",
            source: rawSource,
            typeSource: "",
            enabled: true,
            trusted: true,
            status: "unchecked",
            error: rawLimitError,
            dependencies: [],
            folderId: null
        };
    }
    const text = expandTypeTheoryAliasesInSurface(normalizeSandboxSource(rawSource));
    const expandedLimitError = sandboxSourceLimitError(text, normalizedMaxSourceChars);
    if (expandedLimitError) {
        return {
            id,
            name: "",
            kind: "term",
            source: text,
            typeSource: "",
            enabled: true,
            trusted: true,
            status: "unchecked",
            error: expandedLimitError,
            dependencies: [],
            folderId: null
        };
    }
    try {
        // New declarations use the Unicode surface parser so names such as
        // `SurfaceX` and `Pfoo` survive the compact parser's historical
        // marker tokens.  Keep the compatibility parser as a fallback for
        // migrated saves and old programmatic fixtures.
        const parsed = parseSandboxStoredDeclaration(text);
        if (parsed.hit) {
            const generatedNames = sandboxHitGeneratedNames(parsed.hit);
            return {
                id,
                name: parsed.hit.name,
                kind: "hit",
                source: text,
                typeSource: parsed.hit.universe,
                enabled: true,
                trusted: true,
                status: "unchecked",
                dependencies: collectHitDependencies(parsed.hit),
                folderId: null,
                hit: parsed.hit,
                generatedNames
            };
        }
        if (parsed.inductive) {
            const generatedNames = sandboxInductiveGeneratedNames(parsed.inductive);
            return {
                id,
                name: parsed.inductive.name,
                kind: "inductive",
                source: text,
                typeSource: parsed.inductive.universe,
                enabled: true,
                trusted: true,
                status: "unchecked",
                dependencies: collectInductiveDependencies(parsed.inductive),
                folderId: null,
                inductive: parsed.inductive,
                generatedNames
            };
        }
        const definition = parsed.definitionAst;
        const dependencies = definition
            ? [
                ...collectFreeNames(definition),
                ...(parsed.typeAst ? collectFreeNames(parsed.typeAst) : [])
            ].filter((name, index, names) => names.indexOf(name) === index)
            : collectFreeNames(parsed.typeAst!);
        return {
            id,
            name: parsed.name,
            kind: parsed.definitionAst ? "definition" : declarationKind(parsed.typeAst!),
            source: text,
            typeSource: parsed.typeSource,
            enabled: true,
            trusted: true,
            status: "unchecked",
            dependencies,
            folderId: null,
            presentationAst: parsed.ast ? Core.clone(parsed.ast) : undefined
        };
    } catch (error) {
        return {
            id,
            name: "",
            kind: "term",
            source: text,
            typeSource: "",
            enabled: true,
            trusted: true,
            status: "unchecked",
            error: String(error),
            dependencies: [],
            folderId: null
        };
    }
}

function sandboxInductiveGeneratedNames(signature: SandboxInductiveDeclaration) {
    return [
        signature.name,
        ...signature.constructors.map(ctor => ctor.name),
        `ind_${signature.name}`,
        `@ind_${signature.name}`,
        `rec_${signature.name}`,
        `@rec_${signature.name}`
    ];
}

function sandboxHitGeneratedNames(signature: SandboxHitDeclaration) {
    const pathLevels = signature.pathLevels;
    const pathConstructors = hitPathConstructorsAt(pathLevels, 1);
    const twoPathConstructors = hitPathConstructorsAt(pathLevels, 2);
    const threePathConstructors = hitPathConstructorsAt(pathLevels, 3);
    return [
        signature.name,
        ...signature.pointConstructors.map(ctor => ctor.name),
        ...flattenHitPathLevels(pathLevels).map(ctor => ctor.name),
        `ind_${signature.name}`,
        `@ind_${signature.name}`,
        `rec_${signature.name}`,
        `@rec_${signature.name}`,
        ...pathConstructors.flatMap(path => [
            `apd_${path.name}`,
            `@apd_${path.name}`,
            `ap_${path.name}`,
            `@ap_${path.name}`
        ]),
        ...twoPathConstructors.flatMap(path => [
            `apd_${path.name}`,
            `@apd_${path.name}`,
            `ap_${path.name}`,
            `@ap_${path.name}`,
            `ap2_${path.name}`,
            `@ap2_${path.name}`
        ]),
        ...threePathConstructors.flatMap(path => [
            path.name,
            `apd3_${path.name}`,
            `@apd3_${path.name}`,
            `ap3_${path.name}`,
            `@ap3_${path.name}`
        ])
    ];
}

function collectInductiveDependencies(signature: SandboxInductiveDeclaration) {
    const own = new Set(sandboxInductiveGeneratedNames(signature));
    for (const parameter of signature.parameters) own.add(parameter.name);
    for (const index of signature.indices) own.add(index.name);
    const names = new Set<string>();
    const collect = (ast: AST) => {
        for (const name of collectFreeNames(ast)) {
            if (!own.has(name)) names.add(name);
        }
    };
    for (const parameter of signature.parameters) collect(parameter.type);
    for (const index of signature.indices) collect(index.type);
    collect(signature.universeAst);
    for (const ctor of signature.constructors) {
        collect(ctor.type);
    }
    return [...names];
}

function collectHitDependencies(signature: SandboxHitDeclaration) {
    const pathLevels = signature.pathLevels;
    const own = new Set(sandboxHitGeneratedNames(signature));
    for (const parameter of signature.parameters) own.add(parameter.name);
    const names = new Set<string>();
    const collect = (ast: AST) => {
        for (const name of collectFreeNames(ast)) {
            if (!own.has(name)) names.add(name);
        }
    };
    for (const parameter of signature.parameters) collect(parameter.type);
    collect(signature.universeAst);
    for (const constructor of signature.pointConstructors) collect(constructor.type);
    for (const path of flattenHitPathLevels(pathLevels)) collect(path.type);
    return [...names];
}

function normalizeSandboxLimit(value: unknown): number | undefined {
    if (value === undefined || value === null || value === "") return undefined;
    const numeric = Number(value);
    return Number.isFinite(numeric) && numeric >= 0
        ? Math.floor(numeric)
        : undefined;
}

export type SandboxHitSourceInspection = {
    sourceChars: number;
    maxPathLevel: number;
    firstUnsupportedPath?: {
        level: number;
        sectionIndex: number;
        offset: number;
    };
};

/** Linear preflight for resource and dimension checks; deliberately constructs no parser AST. */
export function inspectSandboxHitSource(source: string): SandboxHitSourceInspection {
    const text = String(source ?? "");
    const pattern = /(?:^|\|)\s*path([0-9]+)\b/gi;
    let maxPathLevel = 0;
    let sectionIndex = 0;
    let firstUnsupportedPath: SandboxHitSourceInspection["firstUnsupportedPath"];
    for (let match = pattern.exec(text); match; match = pattern.exec(text)) {
        sectionIndex++;
        const level = Number(match[1]);
        if (!Number.isSafeInteger(level)) continue;
        maxPathLevel = Math.max(maxPathLevel, level);
        if (level <= 3 || firstUnsupportedPath) continue;
        const pathOffset = match[0].toLowerCase().lastIndexOf("path");
        firstUnsupportedPath = {
            level,
            sectionIndex,
            offset: match.index + Math.max(0, pathOffset)
        };
    }
    return {
        sourceChars: text.length,
        maxPathLevel,
        ...(firstUnsupportedPath ? { firstUnsupportedPath } : {})
    };
}

export function sandboxSourceLimitError(source: string, maxSourceChars: number | undefined) {
    const normalizedMaxSourceChars = normalizeSandboxLimit(maxSourceChars);
    if (normalizedMaxSourceChars === undefined) return undefined;
    const sourceChars = String(source ?? "").length;
    return sourceChars > normalizedMaxSourceChars
        ? `沙盒验证资源上限：源码字符 ${sourceChars} 超过 ${normalizedMaxSourceChars}`
        : undefined;
}

/** Count source AST nodes without following parser back-references such as `origin`. */
function countSandboxSyntaxNodes(value: unknown): number {
    const seen = new WeakSet<object>();
    const stack: unknown[] = [value];
    let count = 0;
    while (stack.length) {
        const current = stack.pop();
        if (!current || typeof current !== "object") continue;
        if (seen.has(current)) continue;
        seen.add(current);
        if (Array.isArray(current)) {
            stack.push(...current);
            continue;
        }
        const record = current as Record<string, unknown>;
        if (typeof record.type === "string" && Array.isArray(record.nodes)) count++;
        for (const [key, child] of Object.entries(record)) {
            // `origin` can point back into the source tree and is presentation
            // metadata, not a unit of validation work.
            if (key === "origin") continue;
            if (child && typeof child === "object") stack.push(child);
        }
    }
    return count;
}

function estimateSandboxDeclarationNodes(source: string): number {
    try {
        return Math.max(1, countSandboxSyntaxNodes(parseSandboxStoredDeclaration(source)));
    } catch {
        // A malformed source is still bounded before the normal parser error
        // path. Character count is deterministic and avoids hiding the real
        // syntax diagnostic behind an estimator failure.
        return Math.max(1, String(source ?? "").length);
    }
}

/**
 * Stage-1 sandbox model. It deliberately owns a fresh TTCoreEngine and never
 * writes to TTGui, GameSaveLoad, unlock state, theorem rows, or map state.
 */
export class SandboxEnvironment {
    private readonly builtinNames = new Set<string>();
    private readonly systemRuleIds: readonly string[];
    private readonly semanticResourceScale: number | undefined;
    private readonly validationBudget: SandboxValidationBudget;
    private readonly validationCachePreludeKey: string;
    private engine: TTCoreEngine;
    /** Fully elaborated body-less declaration types used by the bridge. */
    private axiomTypes = new Map<string, AST>();
    /** Checked source bodies used for the read-only creative bridge. */
    private definitionBodies = new Map<string, AST>();
    private nextId = 1;
    private nextFolderId = 1;
    private dirtyFrom = 0;
    private validatedThrough = 0;
    private pendingValidationCache: unknown = null;
    /** The shared type-layer ordering/folder engine. */
    private workspace = new TheoremWorkspace();
    declarations: SandboxDeclaration[] = [];
    folders: SandboxFolder[] = [];
    order: string[] = [];
    lastValidationDurationMs = 0;
    lastValidationStats: SandboxValidationStats = {
        checkedDeclarations: 0,
        replayedDeclarations: 0,
        validatedThrough: 0
    };

    constructor(options: SandboxEnvironmentOptions = {}) {
        // Standalone callers retain the deliberately small stage-1 prelude so
        // names such as `base` remain available for experimentation. The
        // creative UI passes its complete unlocked system set, which lets a
        // sandbox definition use built-ins such as `nat`/`ind_nat` directly.
        this.systemRuleIds = Object.freeze([
            ...new Set(options.systemRuleIds ?? isolatedSandboxSystemRuleIds)
        ]);
        this.semanticResourceScale = options.semanticResourceScale;
        this.validationCachePreludeKey = sandboxValidationPreludeKey(
            this.systemRuleIds,
            this.semanticResourceScale
        );
        this.validationBudget = Object.freeze({
            maxDeclarations: normalizeSandboxLimit(options.validationMaxDeclarations),
            maxSourceChars: normalizeSandboxLimit(options.validationMaxSourceChars),
            maxNodes: normalizeSandboxLimit(options.validationMaxNodes),
            maxSteps: normalizeSandboxLimit(options.validationMaxSteps),
            timeoutMs: normalizeSandboxLimit(options.validationTimeoutMs)
        });
        this.engine = this.createEngine();
        for (const name of Object.keys(this.engine.core.state.sysTypes)) this.builtinNames.add(name);
        for (const name of Object.keys(this.engine.core.state.sysDefs)) this.builtinNames.add(name);
        this.builtinNames.add("U");
        this.builtinNames.add("U0");
    }

    private createEngine() {
        const engine = new TTCoreEngine();
        const config = {
            unlockedTypes: [...this.systemRuleIds],
            inferDisplayMode: "_" as const,
            semanticResourceScale: this.semanticResourceScale ?? 1
        };
        // Keep the process-wide Core.timeout untouched. The sandbox timeout
        // is enforced by validate() at declaration boundaries, so constructing
        // a bounded sandbox cannot leak its setting into the game Core.
        engine.configure(config);
        return engine;
    }

    add(source: string) {
        return this.addInFolder(source, null);
    }

    addInFolder(source: string, folderId: string | null) {
        if (folderId) {
            const folder = this.folders.find(item => item.id === folderId);
            if (!folder) throw new Error(`找不到沙盒文件夹：${folderId}`);
            if (!folder.open) throw new Error("折叠文件夹不能添加沙盒声明");
        }
        const before = this.validationSignatures();
        const id = `sandbox-${this.nextId++}`;
        const declaration = createSandboxDeclaration(
            source,
            id,
            this.validationBudget.maxSourceChars
        );
        declaration.folderId = folderId;
        this.declarations.push(declaration);
        this.order.push(id);
        this.syncWorkspaceFromState();
        if (folderId) {
            const mutation = this.workspace.move(id, `inside:${folderId}`);
            this.applyWorkspaceSnapshot(mutation.snapshot);
        }
        this.markWorkspaceChange(before);
        return this.validate();
    }

    replace(source: string, id: string) {
        const index = this.orderedDeclarationIndex(id);
        if (index < 0) throw new Error(`找不到沙盒声明：${id}`);
        const declarationIndex = this.declarations.findIndex(declaration => declaration.id === id);
        const previous = this.declarations[declarationIndex];
        const replacement = createSandboxDeclaration(
            source,
            id,
            this.validationBudget.maxSourceChars
        );
        replacement.folderId = previous.folderId;
        replacement.enabled = previous.enabled;
        this.declarations[declarationIndex] = replacement;
        this.markDirty(index);
        return this.validate();
    }

    addFolder(name = "新文件夹") {
        const folder: SandboxFolder = {
            kind: "folder",
            id: `sandbox-folder-${this.nextFolderId++}`,
            name: name.trim() || "新文件夹",
            length: 0,
            open: true,
            disabled: false
        };
        this.folders.push(folder);
        this.order.push(folder.id);
        this.syncWorkspaceFromState();
        return folder;
    }

    setFolder(id: string, folderId: string | null) {
        const declaration = this.find(id);
        if (folderId && !this.folders.some(folder => folder.id === folderId)) {
            throw new Error(`找不到沙盒文件夹：${folderId}`);
        }
        if (folderId) {
            const folder = this.folders.find(item => item.id === folderId);
            if (!folder.open) throw new Error("折叠文件夹不能接收沙盒声明");
        }
        const before = this.validationSignatures();
        this.syncWorkspaceFromState();
        const mutation = folderId
            ? this.workspace.move(id, `inside:${folderId}`)
            : this.workspace.move(id, " ");
        if (!mutation.changed && declaration.folderId !== folderId) {
            throw new Error(folderId
                ? "无法将沙盒声明移入该文件夹"
                : "无法将沙盒声明移出当前文件夹");
        }
        if (mutation.changed) this.applyWorkspaceSnapshot(mutation.snapshot);
        this.markWorkspaceChange(before);
        return this.validate();
    }

    setFolderOpen(id: string, open: boolean) {
        const folder = this.folders.find(item => item.id === id);
        if (!folder) throw new Error(`找不到沙盒文件夹：${id}`);
        this.syncWorkspaceFromState();
        const mutation = this.workspace.setFolderOpen(id, !!open);
        this.applyWorkspaceSnapshot(mutation.snapshot);
        // Folding is presentation-only.  Sandbox declarations are always
        // global (their folderId does not affect dependencies), so rerunning
        // Core here only wastes work and can race a caller's validation.
        return this.currentValidationResult();
    }

    setFolderDisabled(id: string, disabled: boolean) {
        const folder = this.folders.find(item => item.id === id);
        if (!folder) throw new Error(`找不到沙盒文件夹：${id}`);
        const before = this.validationSignatures();
        this.syncWorkspaceFromState();
        const mutation = this.workspace.setFolderDisabled(id, !!disabled);
        this.applyWorkspaceSnapshot(mutation.snapshot);
        this.markWorkspaceChange(before);
        return this.validate();
    }

    renameFolder(id: string, name: string) {
        const folder = this.folders.find(item => item.id === id);
        if (!folder) throw new Error(`找不到沙盒文件夹：${id}`);
        this.syncWorkspaceFromState();
        const mutation = this.workspace.renameFolder(id, name.trim() || folder.name);
        this.applyWorkspaceSnapshot(mutation.snapshot);
        // A folder label is not part of declaration order or scope.
        return this.currentValidationResult();
    }

    removeFolder(id: string) {
        const before = this.validationSignatures();
        this.syncWorkspaceFromState();
        const mutation = this.workspace.removeFolder(id);
        if (!mutation.changed) return this.validate();
        this.applyWorkspaceSnapshot(mutation.snapshot);
        this.markWorkspaceChange(before);
        // Removing an enabled folder only changes presentation/ownership; a
        // disabled folder, however, may re-enable its descendants and must
        // rebuild the affected suffix.  Compare the semantic signatures
        // after applying the shared workspace mutation instead of trusting
        // TheoremWorkspace's broader theorem-layer invalidation flag.
        const after = this.validationSignatures();
        if (before.length === after.length
            && before.every((signature, index) => signature === after[index])) {
            return this.currentValidationResult();
        }
        return this.validate();
    }

    setEnabled(id: string, enabled: boolean) {
        const declaration = this.find(id);
        const index = this.orderedDeclarationIndex(id);
        declaration.enabled = !!enabled;
        this.markDirty(index);
        return this.validate();
    }

    remove(id: string) {
        const before = this.validationSignatures();
        const declarationIndex = this.declarations.findIndex(declaration => declaration.id === id);
        if (declarationIndex >= 0) this.declarations.splice(declarationIndex, 1);
        if (declarationIndex >= 0) this.order = this.order.filter(item => item !== id);
        if (declarationIndex >= 0) {
            this.syncWorkspaceFromState();
            this.markWorkspaceChange(before);
        }
        return this.validate();
    }

    reorder(id: string, targetIndex: number) {
        if (!this.declarations.some(declaration => declaration.id === id)) {
            throw new Error(`找不到沙盒声明：${id}`);
        }
        const before = this.validationSignatures();
        this.syncWorkspaceFromState();
        const targetItemIndex = this.workspace.itemIndexForTheorem(Math.max(0, Math.floor(targetIndex)));
        const snapshot = this.workspace.snapshot();
        const destination = snapshot[targetItemIndex]?.id ?? " ";
        const mutation = this.workspace.move(id, destination);
        if (mutation.changed) this.applyWorkspaceSnapshot(mutation.snapshot);
        this.markWorkspaceChange(before);
        return this.validate();
    }

    /** Apply the same drag/drop destination grammar as the type-layer list. */
    moveItem(sourceId: string, destination: string): SandboxWorkspaceMutation {
        const before = this.validationSignatures();
        this.syncWorkspaceFromState();
        const mutation = this.workspace.move(sourceId, destination);
        if (mutation.changed) {
            this.applyWorkspaceSnapshot(mutation.snapshot);
            this.markWorkspaceChange(before);
        }
        return mutation;
    }

    workspaceLayout(): TheoremWorkspaceLayoutItem[] {
        this.syncWorkspaceFromState();
        return this.workspace.layout();
    }

    folderAppendIndex(folderId: string) {
        this.syncWorkspaceFromState();
        return this.workspace.folderAppendIndex(folderId);
    }

    validate(options: SandboxValidationOptions = {}): SandboxValidationResult {
        const started = performance.now();
        this.syncWorkspaceFromState();
        const workspaceItems = this.workspace.snapshot();
        const layout = new Map(this.workspace.layout().map(item => [item.id, item] as const));
        const orderedDeclarations = workspaceItems
            .filter((item): item is Extract<TheoremWorkspaceItem, { kind: "theorem" }> => item.kind === "theorem")
            .map(item => this.declarations.find(declaration => declaration.id === item.id))
            .filter((declaration): declaration is SandboxDeclaration => !!declaration);
        const budget = this.validationBudgetFor(options);
        const sourceChars = orderedDeclarations.reduce(
            (total, declaration) => total + declaration.source.length,
            0
        );
        if (budget.maxSourceChars !== undefined && sourceChars > budget.maxSourceChars) {
            return this.validationInterrupted(
                "budget-exhausted",
                started,
                0,
                0,
                `沙盒验证资源上限：源码字符 ${sourceChars} 超过 ${budget.maxSourceChars}`
            );
        }
        const estimatedNodes = budget.maxNodes === undefined && budget.maxSteps === undefined
            ? 0
            : orderedDeclarations.reduce(
                (total, declaration) => total + estimateSandboxDeclarationNodes(declaration.source),
                0
            );
        const estimatedSteps = orderedDeclarations.length + estimatedNodes;
        const budgetFailure = this.validationBudgetFailure(
            started,
            budget,
            orderedDeclarations.length,
            estimatedNodes,
            estimatedSteps
        );
        if (budgetFailure) return budgetFailure;
        if (options.shouldCancel?.()) {
            return this.validationInterrupted("cancelled", started, 0, 0);
        }
        let replayedDeclarations = 0;
        if (this.pendingValidationCache && this.dirtyFrom === 0) {
            const cacheReplay = this.restorePersistedValidationCache(
                this.pendingValidationCache,
                orderedDeclarations,
                layout,
                options,
                budget,
                started
            );
            this.pendingValidationCache = null;
            if (cacheReplay.status === "cancelled" || cacheReplay.status === "budget-exhausted") {
                return this.validationInterrupted(
                    cacheReplay.status,
                    started,
                    0,
                    cacheReplay.count
                );
            }
            if (cacheReplay.status === "restored") {
                this.validatedThrough = cacheReplay.count;
                this.dirtyFrom = cacheReplay.count;
                replayedDeclarations += cacheReplay.count;
            }
        } else {
            this.pendingValidationCache = null;
        }
        if (this.dirtyFrom < this.validatedThrough || this.validatedThrough > orderedDeclarations.length) {
            if (options.shouldCancel?.()) {
                return this.validationInterrupted("cancelled", started, 0, 0);
            }
            const prefixLength = Math.min(
                this.dirtyFrom,
                this.validatedThrough,
                orderedDeclarations.length
            );
            this.replayValidatedPrefix(orderedDeclarations, prefixLength, layout);
            this.validatedThrough = prefixLength;
            replayedDeclarations = prefixLength;
        }
        const allNames = new Set<string>();
        const declarationByName = new Map<string, SandboxDeclaration>();
        for (const candidate of this.declarations) {
            try {
                const parsed = parseSandboxStoredDeclaration(candidate.source);
                if (parsed.hit) {
                    for (const name of sandboxHitGeneratedNames(parsed.hit)) {
                        allNames.add(name);
                        declarationByName.set(name, candidate);
                    }
                } else if (parsed.inductive) {
                    for (const name of sandboxInductiveGeneratedNames(parsed.inductive)) {
                        allNames.add(name);
                        declarationByName.set(name, candidate);
                    }
                } else {
                    allNames.add(parsed.name);
                    declarationByName.set(parsed.name, candidate);
                }
            } catch {
                if (candidate.name) {
                    allNames.add(candidate.name);
                    declarationByName.set(candidate.name, candidate);
                }
            }
        }
        const seenNames = new Set<string>();
        let firstError: string | undefined;
        let checkedDeclarations = 0;

        for (let index = 0; index < this.validatedThrough; index++) {
            if (options.shouldCancel?.()) {
                return this.validationInterrupted("cancelled", started, checkedDeclarations, replayedDeclarations);
            }
            const declaration = orderedDeclarations[index];
            if (declaration.status === "invalid"
                && /未知的沙盒名称|禁止前向引用/.test(declaration.error ?? "")) {
                const unresolved = declaration.dependencies.find(dependency =>
                    !this.builtinNames.has(dependency) && !seenNames.has(dependency)
                );
                if (unresolved) {
                    declaration.error = String(new Error(allNames.has(unresolved)
                        ? `禁止前向引用：${declaration.name} 依赖 ${unresolved}`
                        : `未知的沙盒名称：${unresolved}`));
                }
            }
            if (declaration.status === "invalid") firstError ??= declaration.error;
            for (const name of declaration.generatedNames ?? (declaration.name ? [declaration.name] : [])) {
                seenNames.add(name);
            }
        }

        for (let index = this.validatedThrough; index < orderedDeclarations.length; index++) {
            if (options.shouldCancel?.()) {
                return this.validationInterrupted("cancelled", started, checkedDeclarations, replayedDeclarations);
            }
            if (budget.timeoutMs !== undefined && performance.now() - started >= budget.timeoutMs) {
                return this.validationInterrupted("budget-exhausted", started, checkedDeclarations, replayedDeclarations);
            }
            const declaration = orderedDeclarations[index];
            checkedDeclarations++;
            // A declaration may have been edited, disabled, or moved since
            // the previous validation. Never let its old transparent body
            // leak into the next bridge snapshot.
            if (declaration.name) this.axiomTypes.delete(declaration.name);
            if (declaration.name) this.definitionBodies.delete(declaration.name);
            declaration.error = undefined;
            declaration.dependencies = [];
            declaration.inductive = undefined;
            declaration.hit = undefined;
            declaration.generatedNames = undefined;
            declaration.presentationAst = undefined;
            const rowState = layout.get(declaration.id);
            if (rowState?.disabled) {
                declaration.status = "disabled";
                for (const name of declaration.name ? [declaration.name] : []) seenNames.add(name);
                continue;
            }
            if (!declaration.enabled) {
                declaration.status = "disabled";
                for (const name of declaration.name ? [declaration.name] : []) seenNames.add(name);
                continue;
            }

            let parsed: ReturnType<typeof parseSandboxDeclaration>;
            try {
                parsed = parseSandboxStoredDeclaration(declaration.source);
                declaration.name = parsed.name;
                declaration.typeSource = parsed.typeSource;
                declaration.presentationAst = parsed.ast ? Core.clone(parsed.ast) : undefined;
                if (parsed.hit) {
                    declaration.kind = "hit";
                    declaration.hit = parsed.hit;
                    declaration.generatedNames = sandboxHitGeneratedNames(parsed.hit);
                    declaration.dependencies = collectHitDependencies(parsed.hit);
                } else if (parsed.inductive) {
                    declaration.kind = "inductive";
                    declaration.inductive = parsed.inductive;
                    declaration.generatedNames = sandboxInductiveGeneratedNames(parsed.inductive);
                    declaration.dependencies = collectInductiveDependencies(parsed.inductive);
                } else if (parsed.definitionAst) {
                    declaration.kind = "definition";
                    declaration.dependencies = [
                        ...collectFreeNames(parsed.definitionAst),
                        ...(parsed.typeAst ? collectFreeNames(parsed.typeAst) : [])
                    ].filter((name, position, names) =>
                        names.indexOf(name) === position
                    );
                } else {
                    declaration.kind = declarationKind(parsed.typeAst);
                    declaration.dependencies = collectFreeNames(parsed.typeAst);
                }
            } catch (error) {
                this.markInvalid(declaration, error);
                firstError ??= declaration.error;
                if (declaration.name) seenNames.add(declaration.name);
                continue;
            }

            const ownedNames = declaration.generatedNames ?? [declaration.name];
            const conflict = ownedNames.find(name => seenNames.has(name)
                || this.builtinNames.has(name)
                || this.engine.core.hasConst(name));
            if (conflict) {
                this.markInvalid(declaration, new Error(`沙盒声明名称冲突：${conflict}`));
                firstError ??= declaration.error;
                for (const name of ownedNames) seenNames.add(name);
                continue;
            }

            let dependencyError: Error | undefined;
            for (const dependency of declaration.dependencies) {
                if (dependency === declaration.name) {
                    dependencyError = new Error(`不支持递归沙盒定义：${declaration.name}`);
                    break;
                }
                if (this.builtinNames.has(dependency)) continue;
                if (!seenNames.has(dependency)) {
                    dependencyError = new Error(allNames.has(dependency)
                        ? `禁止前向引用：${declaration.name} 依赖 ${dependency}`
                        : `未知的沙盒名称：${dependency}`);
                    break;
                }
                const dependencyDeclaration = declarationByName.get(dependency);
                if (!dependencyDeclaration || dependencyDeclaration.status !== "valid") {
                    dependencyError = new Error(`依赖声明无效：${dependency}`);
                    break;
                }
            }
            if (dependencyError) {
                this.markInvalid(declaration, dependencyError);
                firstError ??= declaration.error;
                for (const name of ownedNames) seenNames.add(name);
                continue;
            }

            try {
                if (parsed.hit) {
                    const bundle = lowerSandboxHit(parsed.hit);
                    this.engine.core.registerSystemInductive(bundle);
                    declaration.generatedNames = [...bundle.generatedNames];
                } else if (parsed.inductive) {
                    const bundle = lowerSandboxInductive(parsed.inductive);
                    this.engine.core.registerSystemInductive(bundle);
                    declaration.generatedNames = [...bundle.generatedNames];
                } else if (parsed.definitionAst) {
                    // Validate the source (including an optional type
                    // ascription) before installing its transparent body. The
                    // check is performed in the same Core so subsequent
                    // declarations can depend on this definition, while the
                    // explicit cleanup keeps a failed registration from
                    // leaving a stale system entry behind.
                    const definitionAst: AST = {
                        type: ":=",
                        name: "",
                        nodes: [
                            { type: "var", name: declaration.name, nodes: [] },
                            parsed.typeAst
                                ? {
                                    type: ":",
                                    name: "",
                                    nodes: [
                                        Core.clone(parsed.definitionAst),
                                        Core.clone(parsed.typeAst)
                                    ]
                                }
                                : Core.clone(parsed.definitionAst)
                        ]
                    };
                    const checked = this.engine.core.checkDefinition(definitionAst, []);
                    const body = checked.filledDefinition.type === ":"
                        ? checked.filledDefinition.nodes?.[0]
                        : checked.filledDefinition;
                    if (!body) throw new Error("定义体为空");
                    try {
                        this.engine.core.registerSystemDefinition(
                            declaration.name,
                            Core.clone(body)
                        );
                    } catch (error) {
                        this.engine.core.setSystemDefinition(declaration.name);
                        this.engine.core.clearDefinitionCache(declaration.name);
                        throw error;
                    }
                    const inferredType = parsed.typeAst
                        ?? this.engine.core.state.defTypes[declaration.name]?.type
                        ?? definitionAst.checked;
                    if (inferredType) {
                        declaration.typeSource = parser.stringify(inferredType);
                        declaration.kind = "definition";
                    }
                    this.definitionBodies.set(
                        declaration.name,
                        Core.clone(body)
                    );
                } else {
                    const type = this.engine.core.checkTypeFormation(parsed.typeAst, []);
                    this.engine.core.setSystemType(declaration.name, Core.clone(type));
                    this.engine.core.syncSemanticTypes();
                    this.axiomTypes.set(declaration.name, Core.clone(type));
                }
                declaration.status = "valid";
            } catch (error) {
                this.definitionBodies.delete(declaration.name);
                this.markInvalid(declaration, error);
                firstError ??= declaration.error;
            }
            for (const name of ownedNames) seenNames.add(name);
        }

        if (options.shouldCancel?.()) {
            return this.validationInterrupted("cancelled", started, checkedDeclarations, replayedDeclarations);
        }
        if (budget.timeoutMs !== undefined && performance.now() - started >= budget.timeoutMs) {
            return this.validationInterrupted("budget-exhausted", started, checkedDeclarations, replayedDeclarations);
        }

        this.validatedThrough = orderedDeclarations.length;
        this.dirtyFrom = this.validatedThrough;

        this.lastValidationDurationMs = performance.now() - started;
        this.lastValidationStats = {
            checkedDeclarations,
            replayedDeclarations,
            validatedThrough: this.validatedThrough
        };
        const validationCache = this.buildValidationCache();
        return {
            ok: !this.declarations.some(declaration => declaration.status === "invalid"),
            declarations: this.getDeclarations(),
            error: firstError,
            status: firstError ? "invalid" : "ok",
            bridge: this.bridge(),
            validationStats: { ...this.lastValidationStats },
            validationCache
        };
    }

    /**
     * Return the already-certified state after a presentation-only mutation.
     * Folder folding/renaming must keep the public result shape used by older
     * callers, but must not invoke validate() or rebuild the incremental Core.
     */
    private currentValidationResult(): SandboxValidationResult {
        const declarations = this.getDeclarations();
        const invalid = declarations.find(declaration => declaration.status === "invalid");
        const pending = declarations.find(declaration => declaration.status === "unchecked");
        const error = invalid?.error
            ?? (pending ? "沙盒声明尚未校验" : undefined);
        return {
            ok: !invalid && !pending,
            declarations,
            error,
            status: error ? "invalid" : "ok",
            bridge: this.bridge(),
            validationStats: { ...this.lastValidationStats }
        };
    }

    /** Return the enabled, validated, read-only creative-mode projection. */
    bridge(): SandboxBridge {
        const axioms: [string, AST][] = [];
        const inductives: SandboxInductiveBundle[] = [];
        const definitions: [string, AST][] = [];
        const order: TTTrustedDeclarationOrderEntry[] = [];
        const layout = new Map(this.workspace.layout().map(item => [item.id, item] as const));
        const ordered = this.workspace.snapshot()
            .filter((item): item is Extract<TheoremWorkspaceItem, { kind: "theorem" }> => item.kind === "theorem")
            .map(item => this.declarations.find(declaration => declaration.id === item.id))
            .filter((declaration): declaration is SandboxDeclaration => !!declaration);
        for (const declaration of ordered) {
            const state = layout.get(declaration.id);
            if (!declaration.enabled || declaration.status !== "valid" || state?.disabled) continue;
            if (declaration.hit) {
                try {
                    inductives.push(lowerSandboxHit(declaration.hit));
                    order.push({ kind: "inductive", name: declaration.name });
                } catch { }
                continue;
            }
            if (declaration.inductive) {
                try {
                    inductives.push(lowerSandboxInductive(declaration.inductive));
                    order.push({ kind: "inductive", name: declaration.name });
                } catch { }
                continue;
            }
            try {
                const parsed = parseSandboxStoredDeclaration(declaration.source);
                if (parsed.definitionAst) {
                    const body = this.definitionBodies.get(declaration.name) ?? parsed.definitionAst;
                    definitions.push([declaration.name, Core.clone(body)]);
                    order.push({ kind: "definition", name: declaration.name });
                } else if (!parsed.inductive && !parsed.hit && parsed.typeAst) {
                    const type = this.axiomTypes.get(declaration.name);
                    if (type) {
                        axioms.push([declaration.name, Core.clone(type)]);
                        order.push({ kind: "axiom", name: declaration.name });
                    }
                }
            } catch { }
        }
        return { axioms, inductives, definitions, order };
    }

    check(source: string): SandboxCheckResult {
        const started = performance.now();
        const normalized = normalizeSandboxSource(source);
        let ast: AST;
        try {
            // Use the shared surface/legacy boundary so generated sandbox
            // names (for example `SurfaceX`) stay intact in both modern UI
            // input and old saved queries.
            ast = parser.parseSurfaceOrLegacy(normalized);
        } catch (error) {
            return {
                ok: false,
                error: String(error),
                timeout: false,
                durationMs: performance.now() - started,
                source
            };
        }
        let result = this.engine.checkAst(ast);
        // A common sandbox query writes a telescope before a final type
        // assertion: `PA:U,...,term : T`.  The surface parser places `:`
        // outside the telescope, leaving T's binder names apparently free.
        // Retry with the assertion scoped under those binders; this changes
        // only the sandbox query convenience layer, not Core syntax.
        if (!result.ok) {
            try {
                if (ast.type === ":" && ast.nodes?.[0] && ast.nodes?.[1]) {
                    const binders: { type: "P" | "->"; name: string; domain: AST }[] = [];
                    let term = ast.nodes[0];
                    while ((term.type === "P" || term.type === "->")
                        && term.nodes?.[0] && term.nodes?.[1]) {
                        binders.push({
                            type: term.type,
                            name: term.name,
                            domain: Core.clone(term.nodes[0])
                        });
                        term = term.nodes[1];
                    }
                    if (binders.length) {
                        let lambda: AST = Core.clone(term);
                        let expected: AST = Core.clone(ast.nodes[1]);
                        for (let index = binders.length - 1; index >= 0; index--) {
                            const name = binders[index].name || `_sandbox${index}`;
                            lambda = {
                                type: "L",
                                name,
                                nodes: [Core.clone(binders[index].domain), lambda]
                            };
                            expected = {
                                type: "P",
                                name,
                                nodes: [Core.clone(binders[index].domain), expected]
                            };
                        }
                        const inferred = this.engine.checkAst(lambda);
                        if (inferred.ok && inferred.type) {
                            const equality = this.engine.checkAst({
                                type: "===",
                                name: "",
                                nodes: [Core.clone(inferred.type), expected]
                            });
                            if (equality.ok) result = inferred;
                        }
                    }
                }
            } catch { }
        }
        return { ...result, source };
    }

    getDeclarations() {
        return this.declarations.map(declaration => ({ ...declaration, dependencies: [...declaration.dependencies] }));
    }

    toJSON(): SandboxSave {
        this.syncWorkspaceFromState();
        const snapshot = this.workspace.snapshot();
        const validationCache = this.buildValidationCache();
        return {
            version: SANDBOX_SAVE_VERSION,
            declarations: this.declarations.map(toSandboxSavedDeclaration),
            folders: snapshot
                .filter((item): item is Extract<TheoremWorkspaceItem, { kind: "folder" }> => item.kind === "folder")
                .map(folder => ({ ...folder })),
            order: snapshot.map(item => item.id),
            ...(validationCache.entries.length ? { validationCache } : {})
        };
    }

    serialize() {
        return JSON.stringify(this.toJSON());
    }

    load(value: unknown, validationOptions: SandboxValidationOptions = {}) {
        const parsed = typeof value === "string" ? JSON.parse(value) : value;
        const rawDeclarations = (parsed as { declarations?: unknown } | null)?.declarations;
        const loadBudget = this.validationBudgetFor(validationOptions);
        if (Array.isArray(rawDeclarations) && loadBudget.maxSourceChars !== undefined) {
            const rawSourceChars = rawDeclarations.reduce((total, declaration) => {
                const source = declaration && typeof declaration === "object"
                    ? (declaration as { source?: unknown }).source
                    : "";
                return total + String(source ?? "").length;
            }, 0);
            if (rawSourceChars > loadBudget.maxSourceChars) {
                return this.validationInterrupted(
                    "budget-exhausted",
                    performance.now(),
                    0,
                    0,
                    `沙盒验证资源上限：源码字符 ${rawSourceChars} 超过 ${loadBudget.maxSourceChars}`
                );
            }
        }
        const save = migrateLegacySandboxSave(parsed) as Partial<SandboxSave> & {
            declarations?: Array<Partial<SandboxDeclaration>>;
        };
        if (!save || save.version !== SANDBOX_SAVE_VERSION || !Array.isArray(save.declarations)) {
            throw new Error("不支持的沙盒存档版本");
        }
        const beforeSignatures = this.validationSignatures();
        const previousDeclarations = new Map(
            this.declarations.map(declaration => [declaration.id, declaration] as const)
        );
        const cleanPrefix = Math.min(this.dirtyFrom, this.validatedThrough);
        this.folders = Array.isArray(save.folders)
            ? save.folders.map((raw: Partial<SandboxFolder>, index: number) => ({
                kind: "folder" as const,
                id: String(raw.id || `sandbox-folder-${index + 1}`),
                name: String(raw.name || "新文件夹"),
                // Older sandbox saves did not persist the flat subtree length.
                // Keep a marker until the order and declaration ownership are
                // available so it can be reconstructed below.
                length: Number.isFinite(Number(raw.length)) ? Number(raw.length) : -1,
                open: raw.open !== false,
                disabled: !!raw.disabled
            }))
            : [];
        const knownIds = new Set([
            ...this.folders.map(folder => folder.id),
            ...save.declarations.map(declaration => declaration.id)
        ]);
        const folderIds = new Set(this.folders.map(folder => folder.id));
        this.declarations = save.declarations.map((raw: Partial<SandboxDeclaration>, index: number) => {
            const source = String(raw.source ?? (raw.name && raw.typeSource ? `${raw.name} : ${raw.typeSource}` : ""));
            const declaration = createSandboxDeclaration(
                source,
                String(raw.id || `sandbox-${index + 1}`),
                this.validationBudget.maxSourceChars
            );
            declaration.enabled = raw.enabled !== false;
            declaration.folderId = raw.folderId && folderIds.has(raw.folderId) ? raw.folderId : null;
            return declaration;
        });
        this.order = (Array.isArray(save.order) ? save.order : [])
            .filter(id => knownIds.has(id));
        for (const id of [...this.folders.map(folder => folder.id), ...this.declarations.map(declaration => declaration.id)]) {
            if (!this.order.includes(id)) this.order.push(id);
        }
        this.repairLegacyFolderLengths();
        this.syncWorkspaceFromState();
        const afterSignatures = this.validationSignatures();
        const commonLimit = Math.min(beforeSignatures.length, afterSignatures.length, cleanPrefix);
        let commonPrefix = 0;
        while (commonPrefix < commonLimit
            && beforeSignatures[commonPrefix] === afterSignatures[commonPrefix]) {
            commonPrefix++;
        }
        const orderedIds = this.workspace.snapshot()
            .filter((item): item is Extract<TheoremWorkspaceItem, { kind: "theorem" }> => item.kind === "theorem")
            .map(item => item.id);
        for (let index = 0; index < commonPrefix; index++) {
            const id = orderedIds[index];
            const previous = previousDeclarations.get(id);
            const nextIndex = this.declarations.findIndex(declaration => declaration.id === id);
            if (!previous || nextIndex < 0) continue;
            previous.folderId = this.declarations[nextIndex].folderId;
            this.declarations[nextIndex] = previous;
        }
        const maxId = this.declarations.reduce((max, declaration) => {
            const match = declaration.id.match(/^sandbox-(\d+)$/);
            return match ? Math.max(max, Number(match[1])) : max;
        }, 0);
        this.nextId = maxId + 1;
        this.nextFolderId = this.folders.reduce((max, folder) => {
            const match = folder.id.match(/^sandbox-folder-(\d+)$/);
            return match ? Math.max(max, Number(match[1])) : max;
        }, 0) + 1;
        this.pendingValidationCache = save.validationCache ?? null;
        this.markDirty(commonPrefix);
        return this.validate(validationOptions);
    }

    private syncWorkspaceFromState() {
        const folders = new Map(this.folders.map(folder => [folder.id, folder] as const));
        const declarations = new Map(this.declarations.map(declaration => [declaration.id, declaration] as const));
        const items: TheoremWorkspaceItem[] = [];
        for (const id of this.order) {
            const folder = folders.get(id);
            if (folder) {
                items.push({
                    kind: "folder",
                    id: folder.id,
                    name: folder.name,
                    length: Math.max(0, Number(folder.length) || 0),
                    open: folder.open,
                    disabled: folder.disabled
                });
                continue;
            }
            const declaration = declarations.get(id);
            if (declaration) {
                items.push({ kind: "theorem", id: declaration.id, value: declaration.source, local: false });
            }
        }
        // Keep external/legacy array edits visible to the shared model.
        for (const folder of this.folders) {
            if (!items.some(item => item.id === folder.id)) {
                items.push({
                    kind: "folder",
                    id: folder.id,
                    name: folder.name,
                    length: Math.max(0, Number(folder.length) || 0),
                    open: folder.open,
                    disabled: folder.disabled
                });
                this.order.push(folder.id);
            }
        }
        for (const declaration of this.declarations) {
            if (!items.some(item => item.id === declaration.id)) {
                items.push({ kind: "theorem", id: declaration.id, value: declaration.source, local: false });
                this.order.push(declaration.id);
            }
        }
        this.workspace.replace(items);
    }

    /**
     * Recover the flat folder lengths used by the shared workspace from old
     * saves that only stored `folderId` on declarations.  Explicit lengths
     * remain authoritative; only the legacy `-1` marker is repaired.
     */
    private repairLegacyFolderLengths() {
        const positions = new Map(this.order.map((id, index) => [id, index] as const));
        for (const folder of this.folders) {
            if (folder.length >= 0) continue;
            const folderIndex = positions.get(folder.id);
            if (folderIndex === undefined) {
                folder.length = 0;
                continue;
            }
            let last = folderIndex;
            for (const declaration of this.declarations) {
                if (declaration.folderId !== folder.id) continue;
                const index = positions.get(declaration.id);
                if (index !== undefined && index > last) last = index;
            }
            folder.length = Math.max(0, last - folderIndex);
        }
    }

    private applyWorkspaceSnapshot(snapshot: readonly TheoremWorkspaceItem[]) {
        const folderById = new Map(this.folders.map(folder => [folder.id, folder] as const));
        const declarationById = new Map(this.declarations.map(declaration => [declaration.id, declaration] as const));
        const nextFolders: SandboxFolder[] = [];
        const nextDeclarations: SandboxDeclaration[] = [];
        this.workspace.replace(snapshot);
        const scopesById = this.workspace.folderScopesForItems(snapshot.map(item => item.id));
        for (const item of snapshot) {
            if (item.kind === "folder") {
                const previous = folderById.get(item.id);
                nextFolders.push({
                    kind: "folder",
                    id: item.id,
                    name: item.name,
                    length: item.length,
                    open: item.open,
                    disabled: item.disabled
                });
                if (previous) Object.assign(previous, nextFolders[nextFolders.length - 1]);
            } else {
                const declaration = declarationById.get(item.id);
                if (!declaration) continue;
                declaration.source = item.value;
                declaration.folderId = scopesById.get(item.id)?.at(-1)?.id ?? null;
                nextDeclarations.push(declaration);
            }
        }
        this.folders = nextFolders;
        this.declarations = nextDeclarations;
        this.order = snapshot.map(item => item.id);
    }

    private buildValidationCache(): SandboxValidationCache {
        this.syncWorkspaceFromState();
        const snapshot = this.workspace.snapshot();
        const layout = new Map(this.workspace.layout().map(item => [item.id, item] as const));
        const ordered = snapshot
            .filter((item): item is Extract<TheoremWorkspaceItem, { kind: "theorem" }> => item.kind === "theorem")
            .map(item => this.declarations.find(declaration => declaration.id === item.id))
            .filter((declaration): declaration is SandboxDeclaration => !!declaration);
        const signatures = this.validationSignatures();
        const entries: SandboxValidationCacheEntry[] = [];
        let prefixKey = this.validationCachePreludeKey;

        for (let index = 0; index < ordered.length; index++) {
            const declaration = ordered[index];
            const disabled = !declaration.enabled || !!layout.get(declaration.id)?.disabled;
            const expectedStatus = disabled ? "disabled" : "valid";
            if (declaration.status !== expectedStatus) break;

            prefixKey = sandboxValidationPrefixKey(prefixKey, signatures[index]);
            const entry: SandboxValidationCacheEntry = {
                id: declaration.id,
                prefixKey,
                kind: declaration.kind,
                status: expectedStatus
            };
            if (disabled) {
                entries.push(entry);
                continue;
            }

            if (declaration.hit) {
                entry.artifact = { kind: "hit" };
            } else if (declaration.inductive) {
                entry.artifact = { kind: "inductive" };
            } else if (declaration.kind === "definition") {
                let parsed: ParsedSandboxDeclaration;
                try {
                    parsed = parseSandboxStoredDeclaration(declaration.source);
                } catch {
                    break;
                }
                const body = this.engine.core.state.sysDefs[declaration.name]
                    ?? this.definitionBodies.get(declaration.name);
                const rawCache = this.engine.core.serializeDefinitionCache(declaration.name);
                if (!body
                    || !rawCache
                    || rawCache.kind !== "nbe"
                    || rawCache.metas.length
                    || sandboxAstHasInferenceHole(rawCache.type)
                    || sandboxAstHasInferenceHole(parsed.definitionAst)
                    || sandboxAstHasInferenceHole(parsed.typeAst)) break;
                entry.artifact = {
                    kind: "definition",
                    body: Core.clone(body),
                    cache: structuredClone(rawCache)
                };
            } else {
                const type = this.axiomTypes.get(declaration.name);
                if (!type) break;
                entry.artifact = { kind: "axiom", type: Core.clone(type) };
            }
            entries.push(entry);
        }

        return {
            version: SANDBOX_VALIDATION_CACHE_VERSION,
            semanticEpoch: SANDBOX_VALIDATION_SEMANTIC_EPOCH,
            preludeKey: this.validationCachePreludeKey,
            entries
        };
    }

    private restorePersistedValidationCache(
        rawCache: unknown,
        orderedDeclarations: readonly SandboxDeclaration[],
        layout: ReadonlyMap<string, TheoremWorkspaceLayoutItem>,
        options: SandboxValidationOptions,
        budget: SandboxValidationBudget,
        started: number
    ): SandboxValidationCacheReplayResult {
        if (!sandboxValidationCacheWithinLimits(rawCache)) return { status: "discarded", count: 0 };
        const cache = rawCache as Partial<SandboxValidationCache>;
        if (cache.version !== SANDBOX_VALIDATION_CACHE_VERSION
            || cache.semanticEpoch !== SANDBOX_VALIDATION_SEMANTIC_EPOCH
            || cache.preludeKey !== this.validationCachePreludeKey
            || !Array.isArray(cache.entries)
            || cache.entries.length > orderedDeclarations.length
            || cache.entries.length > SANDBOX_VALIDATION_CACHE_MAX_ENTRIES) {
            return { status: "discarded", count: 0 };
        }
        if (!cache.entries.length) return { status: "discarded", count: 0 };

        const signatures = this.validationSignatures();
        let prefixKey = this.validationCachePreludeKey;
        for (let index = 0; index < cache.entries.length; index++) {
            const entry = cache.entries[index] as Partial<SandboxValidationCacheEntry>;
            const declaration = orderedDeclarations[index];
            prefixKey = sandboxValidationPrefixKey(prefixKey, signatures[index]);
            const disabled = !declaration.enabled || !!layout.get(declaration.id)?.disabled;
            if (!entry
                || entry.id !== declaration.id
                || entry.prefixKey !== prefixKey
                || entry.status !== (disabled ? "disabled" : "valid")
                || typeof entry.kind !== "string"
                || (!disabled && (!entry.artifact || typeof entry.artifact !== "object"))) {
                return { status: "discarded", count: 0 };
            }
        }

        const nextEngine = this.createEngine();
        const nextAxiomTypes = new Map<string, AST>();
        const nextBodies = new Map<string, AST>();
        const patches: { target: SandboxDeclaration; value: SandboxDeclaration }[] = [];
        const statusByName = new Map<string, SandboxDeclarationStatus>();

        try {
            return nextEngine.core.withSilentErrors(() => {
                for (let index = 0; index < cache.entries!.length; index++) {
                    if (options.shouldCancel?.()) return { status: "cancelled", count: index };
                    if (budget.timeoutMs !== undefined && performance.now() - started >= budget.timeoutMs) {
                        return { status: "budget-exhausted", count: index };
                    }
                    const target = orderedDeclarations[index];
                    const entry = cache.entries![index];
                    const rowDisabled = !target.enabled || !!layout.get(target.id)?.disabled;
                    if (rowDisabled) {
                        patches.push({ target, value: { ...target, status: "disabled", error: undefined } });
                        for (const name of target.generatedNames ?? (target.name ? [target.name] : [])) {
                            statusByName.set(name, "disabled");
                        }
                        continue;
                    }

                    const parsed = parseSandboxStoredDeclaration(target.source);
                    const restored: SandboxDeclaration = {
                        ...target,
                        name: parsed.name,
                        typeSource: parsed.typeSource,
                        kind: parsed.hit
                            ? "hit"
                            : parsed.inductive
                                ? "inductive"
                                : parsed.definitionAst
                                    ? "definition"
                                    : declarationKind(parsed.typeAst!),
                        status: "unchecked",
                        error: undefined,
                        dependencies: [],
                        inductive: undefined,
                        hit: undefined,
                        generatedNames: undefined,
                        presentationAst: parsed.ast ? Core.clone(parsed.ast) : undefined
                    };
                    if (restored.kind !== entry.kind) throw new Error("沙盒验证缓存声明种类不匹配");

                    if (parsed.hit) {
                        restored.hit = parsed.hit;
                        restored.generatedNames = sandboxHitGeneratedNames(parsed.hit);
                        restored.dependencies = collectHitDependencies(parsed.hit);
                    } else if (parsed.inductive) {
                        restored.inductive = parsed.inductive;
                        restored.generatedNames = sandboxInductiveGeneratedNames(parsed.inductive);
                        restored.dependencies = collectInductiveDependencies(parsed.inductive);
                    } else if (parsed.definitionAst) {
                        restored.dependencies = [
                            ...collectFreeNames(parsed.definitionAst),
                            ...(parsed.typeAst ? collectFreeNames(parsed.typeAst) : [])
                        ].filter((name, position, names) => names.indexOf(name) === position);
                    } else {
                        restored.dependencies = collectFreeNames(parsed.typeAst!);
                    }

                    const ownedNames = restored.generatedNames ?? [restored.name];
                    const conflict = ownedNames.find(name => this.builtinNames.has(name)
                        || nextEngine.core.hasConst(name)
                        || statusByName.has(name));
                    if (conflict) throw new Error(`沙盒声明名称冲突：${conflict}`);
                    for (const dependency of restored.dependencies) {
                        if (dependency === restored.name) {
                            throw new Error(`不支持递归沙盒定义：${restored.name}`);
                        }
                        if (this.builtinNames.has(dependency)) continue;
                        if (statusByName.get(dependency) !== "valid") {
                            throw new Error(`依赖声明无效：${dependency}`);
                        }
                    }

                    const artifact = entry.artifact!;
                    if (parsed.hit) {
                        if (artifact.kind !== "hit") throw new Error("沙盒 HIT 缓存格式不匹配");
                        const bundle = lowerSandboxHit(parsed.hit);
                        nextEngine.core.registerSystemInductive(bundle);
                        restored.generatedNames = [...bundle.generatedNames];
                    } else if (parsed.inductive) {
                        if (artifact.kind !== "inductive") throw new Error("沙盒归纳缓存格式不匹配");
                        const bundle = lowerSandboxInductive(parsed.inductive);
                        nextEngine.core.registerSystemInductive(bundle);
                        restored.generatedNames = [...bundle.generatedNames];
                    } else if (parsed.definitionAst) {
                        if (artifact.kind !== "definition") throw new Error("沙盒定义缓存格式不匹配");
                        const body = this.restoreCachedDefinition(
                            nextEngine,
                            restored.name,
                            parsed.definitionAst,
                            parsed.typeAst,
                            artifact.body,
                            artifact.cache
                        );
                        nextBodies.set(restored.name, Core.clone(body));
                    } else {
                        if (artifact.kind !== "axiom") throw new Error("沙盒公理缓存格式不匹配");
                        const sourceType = nextEngine.core.checkTypeFormation(parsed.typeAst!, []);
                        const cachedType = nextEngine.core.checkTypeFormation(artifact.type, []);
                        const equality = nextEngine.checkAst({
                            type: "===",
                            name: "",
                            nodes: [Core.clone(sourceType), Core.clone(cachedType)]
                        });
                        if (!equality.ok) throw new Error("沙盒公理缓存与声明源不匹配");
                        nextEngine.core.setSystemType(restored.name, Core.clone(sourceType));
                        nextEngine.core.syncSemanticTypes();
                        nextAxiomTypes.set(restored.name, Core.clone(sourceType));
                    }

                    restored.status = "valid";
                    patches.push({ target, value: restored });
                    for (const name of ownedNames) statusByName.set(name, "valid");
                }

                for (const patch of patches) Object.assign(patch.target, patch.value);
                this.engine = nextEngine;
                this.axiomTypes = nextAxiomTypes;
                this.definitionBodies = nextBodies;
                return { status: "restored", count: cache.entries!.length };
            });
        } catch {
            return { status: "discarded", count: 0 };
        }
    }

    private restoreCachedDefinition(
        engine: TTCoreEngine,
        name: string,
        sourceBody: AST,
        expectedType: AST | undefined,
        cachedBody: AST,
        rawCache: DefinitionTypeCacheSnapshot
    ) {
        if (!rawCache
            || rawCache.kind !== "nbe"
            || rawCache.metas.length
            || sandboxAstHasInferenceHole(rawCache.type)
            || sandboxAstHasInferenceHole(sourceBody)
            || sandboxAstHasInferenceHole(expectedType)) {
            throw new Error("沙盒透明定义缓存不可安全恢复");
        }
        const cache = rawCache as SemanticDefinitionTypeCacheSnapshot;
        let verifiedBody: AST;
        let verifiedType: AST;
        if (expectedType) {
            const assertion: AST = {
                type: ":",
                name: "",
                nodes: [Core.clone(sourceBody), Core.clone(expectedType)]
            };
            verifiedType = engine.core.checkType(assertion, [], false, undefined, false, true, false);
            verifiedBody = assertion.nodes[0];
        } else {
            const equality: AST = {
                type: "===",
                name: "",
                nodes: [Core.clone(sourceBody), Core.clone(cachedBody)]
            };
            verifiedType = engine.core.checkType(equality, [], false, undefined, false, true, false);
            verifiedBody = equality.nodes[0];
        }
        engine.core.checkType({
            type: "===",
            name: "",
            nodes: [Core.clone(verifiedType), Core.clone(cache.type)]
        }, [], false, undefined, false, true, false);

        engine.core.setSystemDefinition(name, Core.clone(verifiedBody));
        engine.core.restoreCheckedDefinitionCache(name, cache);
        if (!engine.core.hasDefinitionCache(name)) {
            engine.core.setSystemDefinition(name);
            throw new Error("沙盒透明定义缓存未通过 NbE 编译");
        }
        return Core.clone(verifiedBody);
    }

    private replayValidatedPrefix(
        orderedDeclarations: readonly SandboxDeclaration[],
        prefixLength: number,
        layout: ReadonlyMap<string, TheoremWorkspaceLayoutItem>
    ) {
        const previousBodies = this.definitionBodies;
        const previousAxiomTypes = this.axiomTypes;
        const nextAxiomTypes = new Map<string, AST>();
        const nextBodies = new Map<string, AST>();
        const nextEngine = this.createEngine();
        try {
            for (let index = 0; index < prefixLength; index++) {
                const declaration = orderedDeclarations[index];
                const rowState = layout.get(declaration.id);
                if (declaration.status !== "valid" || !declaration.enabled || rowState?.disabled) continue;
                const parsed = parseSandboxStoredDeclaration(declaration.source);
                if (parsed.hit) {
                    nextEngine.core.registerSystemInductive(lowerSandboxHit(parsed.hit));
                    continue;
                }
                if (parsed.inductive) {
                    nextEngine.core.registerSystemInductive(lowerSandboxInductive(parsed.inductive));
                    continue;
                }
                if (parsed.definitionAst) {
                    const body = previousBodies.get(declaration.name);
                    if (!body) {
                        throw new Error(`缺少透明定义缓存：${declaration.name}`);
                    }
                    nextEngine.core.registerSystemDefinition(declaration.name, Core.clone(body));
                    nextBodies.set(declaration.name, Core.clone(body));
                    continue;
                }
                const type = previousAxiomTypes.get(declaration.name)
                    ?? nextEngine.core.checkTypeFormation(parsed.typeAst, []);
                nextEngine.core.setSystemType(declaration.name, Core.clone(type));
                nextEngine.core.syncSemanticTypes();
                nextAxiomTypes.set(declaration.name, Core.clone(type));
            }
        } catch (error) {
            throw new Error(`恢复沙盒增量前缀失败：${String(error)}`);
        }
        this.engine = nextEngine;
        this.axiomTypes = nextAxiomTypes;
        this.definitionBodies = nextBodies;
    }

    private validationSignatures() {
        this.syncWorkspaceFromState();
        return sandboxValidationSignatures({
            declarations: this.declarations,
            folders: this.folders,
            order: this.order
        });
    }

    private orderedDeclarationIndex(id: string) {
        this.syncWorkspaceFromState();
        return this.workspace.snapshot()
            .filter((item): item is Extract<TheoremWorkspaceItem, { kind: "theorem" }> => item.kind === "theorem")
            .findIndex(item => item.id === id);
    }

    private markWorkspaceChange(before: readonly string[]) {
        const after = this.validationSignatures();
        const commonLength = Math.min(before.length, after.length);
        let index = 0;
        while (index < commonLength && before[index] === after[index]) index++;
        if (index < before.length || index < after.length) this.markDirty(index);
    }

    private find(id: string) {
        const declaration = this.declarations.find(item => item.id === id);
        if (!declaration) throw new Error(`找不到沙盒声明：${id}`);
        return declaration;
    }

    private markDirty(index: number) {
        this.dirtyFrom = Math.min(this.dirtyFrom, Math.max(0, index));
    }

    private markInvalid(declaration: SandboxDeclaration, error: unknown) {
        declaration.status = "invalid";
        declaration.error = String(error);
    }

    private validationBudgetFor(options: SandboxValidationOptions): SandboxValidationBudget {
        return {
            maxDeclarations: normalizeSandboxLimit(
                options.maxDeclarations ?? this.validationBudget.maxDeclarations
            ),
            maxSourceChars: normalizeSandboxLimit(
                options.maxSourceChars ?? this.validationBudget.maxSourceChars
            ),
            maxNodes: normalizeSandboxLimit(options.maxNodes ?? this.validationBudget.maxNodes),
            maxSteps: normalizeSandboxLimit(options.maxSteps ?? this.validationBudget.maxSteps),
            timeoutMs: normalizeSandboxLimit(options.timeoutMs ?? this.validationBudget.timeoutMs)
        };
    }

    private validationBudgetFailure(
        started: number,
        budget: SandboxValidationBudget,
        declarationCount: number,
        estimatedNodes: number,
        estimatedSteps: number
    ): SandboxValidationResult | undefined {
        if (budget.maxDeclarations !== undefined && declarationCount > budget.maxDeclarations) {
            return this.validationInterrupted(
                "budget-exhausted",
                started,
                0,
                0,
                `沙盒验证资源上限：声明数量 ${declarationCount} 超过 ${budget.maxDeclarations}`
            );
        }
        if (budget.maxNodes !== undefined && estimatedNodes > budget.maxNodes) {
            return this.validationInterrupted(
                "budget-exhausted",
                started,
                0,
                0,
                `沙盒验证资源上限：语法节点 ${estimatedNodes} 超过 ${budget.maxNodes}`
            );
        }
        if (budget.maxSteps !== undefined && estimatedSteps > budget.maxSteps) {
            return this.validationInterrupted(
                "budget-exhausted",
                started,
                0,
                0,
                `沙盒验证资源上限：验证步骤 ${estimatedSteps} 超过 ${budget.maxSteps}`
            );
        }
        if (budget.timeoutMs !== undefined && budget.timeoutMs <= 0) {
            return this.validationInterrupted(
                "budget-exhausted",
                started,
                0,
                0,
                "沙盒验证资源上限：时间预算已耗尽"
            );
        }
        return undefined;
    }

    private validationInterrupted(
        status: "cancelled" | "budget-exhausted",
        started: number,
        checkedDeclarations: number,
        replayedDeclarations: number,
        error?: string
    ): SandboxValidationResult {
        // A validation run mutates the incremental Core as it walks the
        // suffix.  Leaving that partially-built Core behind would make the
        // next resumed run register the same names twice.  Mark the current
        // prefix dirty so the normal replay path rebuilds a clean suffix on
        // the next request; the last published bridge remains untouched.
        // Rebuild from the clean prelude on resume. The current run may have
        // registered a suffix declaration before cancellation, so merely
        // keeping `dirtyFrom === validatedThrough` would reuse a partially
        // mutated Core and cause duplicate-name failures on the next run.
        this.dirtyFrom = 0;
        this.lastValidationDurationMs = performance.now() - started;
        this.lastValidationStats = {
            checkedDeclarations,
            replayedDeclarations,
            validatedThrough: this.validatedThrough
        };
        return {
            ok: false,
            declarations: this.getDeclarations(),
            error: error ?? (status === "cancelled" ? "沙盒验证已取消" : "沙盒验证资源上限已耗尽"),
            status,
            validationStats: { ...this.lastValidationStats }
        };
    }
}

function declarationKind(type: AST): SandboxDeclarationKind {
    const rendered = parser.stringify(type).replaceAll(" ", "");
    if (/^U(?:[0-9]+)?$/.test(rendered)) return "type";
    if (type.type === "=" || type.type === "~=" || type.type === "~") return "proposition";
    return "term";
}

function collectFreeNames(ast: AST) {
    const names = new Set<string>();
    const visit = (node: AST, bound: Set<string>) => {
        if (!node) return;
        if (node.type === "var") {
            // `_` and `?meta` are elaboration holes, not declarations.  Keep
            // them out of dependency diagnostics so a valid definition can
            // infer them instead of being reported as an unknown sandbox
            // name.
            if (node.name && node.name !== "_" && !node.name.startsWith("?")
                && !bound.has(node.name) && !node.name.startsWith("@")) {
                names.add(node.name);
            }
            return;
        }
        if (node.type === "P" || node.type === "L" || node.type === "W" || node.type === "S") {
            visit(node.nodes?.[0], bound);
            const next = new Set(bound);
            if (node.name) next.add(node.name);
            visit(node.nodes?.[1], next);
            return;
        }
        for (const child of node.nodes ?? []) visit(child, bound);
    };
    visit(ast, new Set());
    return [...names];
}
