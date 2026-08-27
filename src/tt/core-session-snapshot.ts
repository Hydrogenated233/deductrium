import type { AST } from "./astparser.js";
import type { DefinitionTypeCacheSnapshot } from "./core.js";
import type { TTCoreConfig } from "./engine.js";

/** One ordered user-definition entry retained by a persistent core session. */
export type TTDefinitionSlot = [string, AST, DefinitionTypeCacheSnapshot?] | null;

/**
 * Engine options that can be reused without duplicating the ordered definition
 * prefix. User definitions and their type caches deliberately live only in
 * `definitions` below.
 */
export type TTCoreSessionConfig = Omit<
    TTCoreConfig,
    "userDefinitions" | "userDefinitionCaches"
>;

/**
 * A portable, serializable description of a configured `TTCoreSession`.
 * It contains no live `Core`, inference table, or proof-assistant state.
 */
export type TTCoreSessionSnapshot = {
    config: TTCoreSessionConfig;
    definitions: TTDefinitionSlot[];
    /** Exclusive definition slot already loaded into the persistent Core. */
    loadedThrough: number;
};

/**
 * Clone a definition term without retaining transient checker `checked`
 * subtrees. This intentionally matches `Core.clone(ast)`'s default shape so
 * recovery does not retain a second elaborated AST tree for each theorem.
 */
function cloneDefinitionAst(ast: AST): AST {
    const cloned: AST = {
        type: ast.type,
        name: ast.name,
        checked: null,
        err: ast.err,
        bondVarId: ast.bondVarId,
        displayExplicitAt: ast.displayExplicitAt
    };
    if (ast.nodes) cloned.nodes = ast.nodes.map(cloneDefinitionAst);
    return cloned;
}

export function cloneTTDefinitionSlot(definition: TTDefinitionSlot): TTDefinitionSlot {
    if (!definition) return null;
    return [
        definition[0],
        cloneDefinitionAst(definition[1]),
        definition[2] ? structuredClone(definition[2]) : undefined
    ];
}

/**
 * Convert the legacy embedded configuration prefix into the session's single
 * ordered definition representation.  An explicit `definitions` argument to
 * `configure` still wins; this is only the compatibility path for callers
 * that previously supplied `TTCoreConfig.userDefinitions` directly.
 */
export function definitionSlotsFromConfig(config: TTCoreConfig): TTDefinitionSlot[] {
    const definitions = config.userDefinitions ?? [];
    const caches = config.userDefinitionCaches ?? [];
    if (!definitions.length) return [];

    const definitionCounts = new Map<string, number>();
    const cacheCounts = new Map<string, number>();
    const cachesByName = new Map<string, DefinitionTypeCacheSnapshot[]>();
    for (const [name] of definitions) {
        definitionCounts.set(name, (definitionCounts.get(name) ?? 0) + 1);
    }
    for (const [name, cache] of caches) {
        cacheCounts.set(name, (cacheCounts.get(name) ?? 0) + 1);
        const group = cachesByName.get(name);
        if (group) group.push(cache);
        else cachesByName.set(name, [cache]);
    }

    // Match the engine's old configuration semantics: malformed duplicate
    // cache entries are ignored rather than attached to an arbitrary shadow.
    const ambiguousNames = new Set(
        [...definitionCounts].flatMap(([name, count]) =>
            (cacheCounts.get(name) ?? 0) === count ? [] : [name])
    );

    return definitions.map(([name, definition]) => {
        const cache = ambiguousNames.has(name) ? undefined : cachesByName.get(name)?.shift();
        return cloneTTDefinitionSlot([name, definition, cache]);
    });
}

export function cloneTTCoreSessionConfig(config: TTCoreConfig): TTCoreSessionConfig {
    const { userDefinitions, userDefinitionCaches, ...systemConfig } = config;
    return structuredClone(systemConfig) as TTCoreSessionConfig;
}

export function createTTCoreSessionSnapshot(
    config: TTCoreConfig,
    definitions?: TTDefinitionSlot[],
    loadedThrough?: number
): TTCoreSessionSnapshot {
    const slots = (definitions ?? definitionSlotsFromConfig(config)).map(cloneTTDefinitionSlot);
    return {
        config: cloneTTCoreSessionConfig(config),
        definitions: slots,
        loadedThrough: normalizeLoadedThrough(loadedThrough, slots.length)
    };
}

export function cloneTTCoreSessionSnapshot(
    snapshot: TTCoreSessionSnapshot
): TTCoreSessionSnapshot {
    const definitions = snapshot.definitions.map(cloneTTDefinitionSlot);
    return {
        config: cloneTTCoreSessionConfig(snapshot.config),
        definitions,
        loadedThrough: normalizeLoadedThrough(snapshot.loadedThrough, definitions.length)
    };
}

function normalizeLoadedThrough(value: unknown, definitionCount: number) {
    if (!Number.isFinite(value)) return definitionCount;
    return Math.min(definitionCount, Math.max(0, Math.floor(Number(value))));
}
