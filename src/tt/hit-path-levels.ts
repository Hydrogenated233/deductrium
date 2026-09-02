/** Path dimensions currently supported by the user-facing HIT sandbox. */
export const SUPPORTED_HIT_PATH_LEVELS = [1, 2, 3] as const;

export type SupportedHitPathLevel = typeof SUPPORTED_HIT_PATH_LEVELS[number];
export type SupportedHitDimension = 0 | SupportedHitPathLevel;

export type HitPathLevelEntry<Level extends number, Constructor> = {
    readonly level: Level;
    readonly constructors: readonly Constructor[];
};

/**
 * Canonical in-memory ordering for the currently supported path dimensions.
 * Point constructors remain separate because ordinary inductives and HITs
 * impose different restrictions on their zero-dimensional constructors.
 */
export type HitPathLevels<Path1, Path2, Path3> = readonly [
    HitPathLevelEntry<1, Path1>,
    HitPathLevelEntry<2, Path2>,
    HitPathLevelEntry<3, Path3>
];

/** Compatibility shape used by the existing sandbox and Core metadata. */
export type LegacyHitPathCollections<Path1, Path2, Path3> = {
    readonly pathConstructors?: readonly Path1[];
    readonly twoPathConstructors?: readonly Path2[];
    readonly threePathConstructors?: readonly Path3[];
};

export function createHitPathLevels<Path1, Path2, Path3>(
    path1: readonly Path1[] = [],
    path2: readonly Path2[] = [],
    path3: readonly Path3[] = []
): HitPathLevels<Path1, Path2, Path3> {
    return [
        { level: 1, constructors: [...path1] },
        { level: 2, constructors: [...path2] },
        { level: 3, constructors: [...path3] }
    ];
}

export function hitPathLevelsFromLegacy<Path1, Path2, Path3>(
    legacy: LegacyHitPathCollections<Path1, Path2, Path3>
): HitPathLevels<Path1, Path2, Path3> {
    return createHitPathLevels(
        legacy.pathConstructors ?? [],
        legacy.twoPathConstructors ?? [],
        legacy.threePathConstructors ?? []
    );
}

export function hitPathLevelsFromCanonicalOrLegacy<Path1, Path2, Path3>(
    value: LegacyHitPathCollections<Path1, Path2, Path3> & {
        readonly pathLevels?: HitPathLevels<Path1, Path2, Path3>;
    }
): HitPathLevels<Path1, Path2, Path3> {
    const levels = value.pathLevels ?? hitPathLevelsFromLegacy(value);
    assertCanonicalHitPathLevels(levels);
    return levels as HitPathLevels<Path1, Path2, Path3>;
}

export function legacyHitPathCollectionsFromLevels<Path1, Path2, Path3>(
    levels: HitPathLevels<Path1, Path2, Path3>
): Required<LegacyHitPathCollections<Path1, Path2, Path3>> {
    return {
        pathConstructors: [...levels[0].constructors],
        twoPathConstructors: [...levels[1].constructors],
        threePathConstructors: [...levels[2].constructors]
    };
}

export function hitPathConstructorsAt<Path1, Path2, Path3>(
    levels: HitPathLevels<Path1, Path2, Path3>,
    level: 1
): readonly Path1[];
export function hitPathConstructorsAt<Path1, Path2, Path3>(
    levels: HitPathLevels<Path1, Path2, Path3>,
    level: 2
): readonly Path2[];
export function hitPathConstructorsAt<Path1, Path2, Path3>(
    levels: HitPathLevels<Path1, Path2, Path3>,
    level: 3
): readonly Path3[];
export function hitPathConstructorsAt<Path1, Path2, Path3>(
    levels: HitPathLevels<Path1, Path2, Path3>,
    level: SupportedHitPathLevel
): readonly (Path1 | Path2 | Path3)[] {
    return levels[level - 1].constructors;
}

/** Flatten in eliminator order: all 1-paths, then 2-paths, then 3-paths. */
export function flattenHitPathLevels<Path1, Path2, Path3>(
    levels: HitPathLevels<Path1, Path2, Path3>
): (Path1 | Path2 | Path3)[] {
    return [
        ...levels[0].constructors,
        ...levels[1].constructors,
        ...levels[2].constructors
    ];
}

export function hitPathConstructorCount<Path1, Path2, Path3>(
    levels: HitPathLevels<Path1, Path2, Path3>
): number {
    return levels.reduce((count, entry) => count + entry.constructors.length, 0);
}

export function highestHitPathLevel<Path1, Path2, Path3>(
    levels: HitPathLevels<Path1, Path2, Path3>
): SupportedHitDimension {
    for (let index = levels.length - 1; index >= 0; index--) {
        if (levels[index].constructors.length) return levels[index].level;
    }
    return 0;
}

/** Return the first non-empty level whose immediately lower support is empty. */
export function firstHitPathLevelGap<Path1, Path2, Path3>(
    levels: HitPathLevels<Path1, Path2, Path3>
): SupportedHitPathLevel | undefined {
    let lowerLevelMissing = false;
    for (const entry of levels) {
        if (!entry.constructors.length) {
            lowerLevelMissing = true;
        } else if (lowerLevelMissing) {
            return entry.level;
        }
    }
    return undefined;
}

export function hitPathLevelsAreContiguous<Path1, Path2, Path3>(
    levels: HitPathLevels<Path1, Path2, Path3>
): boolean {
    return firstHitPathLevelGap(levels) === undefined;
}

/** Validate untrusted or structured-cloned pathLevels before using them. */
export function assertCanonicalHitPathLevels(
    value: unknown
): asserts value is HitPathLevels<unknown, unknown, unknown> {
    if (!Array.isArray(value) || value.length !== SUPPORTED_HIT_PATH_LEVELS.length) {
        throw new Error("HIT pathLevels 必须包含一至三阶三个层级");
    }
    for (let index = 0; index < SUPPORTED_HIT_PATH_LEVELS.length; index++) {
        const expectedLevel = SUPPORTED_HIT_PATH_LEVELS[index];
        const entry = value[index];
        if (!entry || typeof entry !== "object"
            || (entry as { level?: unknown }).level !== expectedLevel
            || !Array.isArray((entry as { constructors?: unknown }).constructors)) {
            throw new Error(`HIT pathLevels 第 ${expectedLevel} 阶结构无效`);
        }
    }
    const gap = firstHitPathLevelGap(
        value as unknown as HitPathLevels<unknown, unknown, unknown>
    );
    if (gap !== undefined) {
        throw new Error(`HIT pathLevels 第 ${gap} 阶不能越过空的低阶路径层级`);
    }
}
