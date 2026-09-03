/**
 * Clone a definition term without retaining transient checker `checked`
 * subtrees. This intentionally matches `Core.clone(ast)`'s default shape so
 * recovery does not retain a second elaborated AST tree for each theorem.
 */
function cloneDefinitionAst(ast) {
    const cloned = {
        type: ast.type,
        name: ast.name,
        checked: null,
        err: ast.err,
        bondVarId: ast.bondVarId,
        displayExplicitAt: ast.displayExplicitAt,
        nbeGeneratedMeta: ast.nbeGeneratedMeta
    };
    if (ast.nodes)
        cloned.nodes = ast.nodes.map(cloneDefinitionAst);
    return cloned;
}
export function cloneTTDefinitionSlot(definition) {
    if (!definition)
        return null;
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
export function definitionSlotsFromConfig(config) {
    const definitions = config.userDefinitions ?? [];
    const caches = config.userDefinitionCaches ?? [];
    if (!definitions.length)
        return [];
    const definitionCounts = new Map();
    const cacheCounts = new Map();
    const cachesByName = new Map();
    for (const [name] of definitions) {
        definitionCounts.set(name, (definitionCounts.get(name) ?? 0) + 1);
    }
    for (const [name, cache] of caches) {
        cacheCounts.set(name, (cacheCounts.get(name) ?? 0) + 1);
        const group = cachesByName.get(name);
        if (group)
            group.push(cache);
        else
            cachesByName.set(name, [cache]);
    }
    // Match the engine's old configuration semantics: malformed duplicate
    // cache entries are ignored rather than attached to an arbitrary shadow.
    const ambiguousNames = new Set([...definitionCounts].flatMap(([name, count]) => (cacheCounts.get(name) ?? 0) === count ? [] : [name]));
    return definitions.map(([name, definition]) => {
        const cache = ambiguousNames.has(name) ? undefined : cachesByName.get(name)?.shift();
        return cloneTTDefinitionSlot([name, definition, cache]);
    });
}
export function cloneTTCoreSessionConfig(config) {
    const { userDefinitions, userDefinitionCaches, ...systemConfig } = config;
    return structuredClone(systemConfig);
}
export function createTTCoreSessionSnapshot(config, definitions, loadedThrough) {
    const slots = (definitions ?? definitionSlotsFromConfig(config)).map(cloneTTDefinitionSlot);
    return {
        config: cloneTTCoreSessionConfig(config),
        definitions: slots,
        loadedThrough: normalizeLoadedThrough(loadedThrough, slots.length)
    };
}
export function cloneTTCoreSessionSnapshot(snapshot) {
    const definitions = snapshot.definitions.map(cloneTTDefinitionSlot);
    return {
        config: cloneTTCoreSessionConfig(snapshot.config),
        definitions,
        loadedThrough: normalizeLoadedThrough(snapshot.loadedThrough, definitions.length)
    };
}
function normalizeLoadedThrough(value, definitionCount) {
    if (!Number.isFinite(value))
        return definitionCount;
    return Math.min(definitionCount, Math.max(0, Math.floor(Number(value))));
}
//# sourceMappingURL=core-session-snapshot.js.map