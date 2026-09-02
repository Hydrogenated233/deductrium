/** Path dimensions currently supported by the user-facing HIT sandbox. */
export const SUPPORTED_HIT_PATH_LEVELS = [1, 2, 3];
export function createHitPathLevels(path1 = [], path2 = [], path3 = []) {
    return [
        { level: 1, constructors: [...path1] },
        { level: 2, constructors: [...path2] },
        { level: 3, constructors: [...path3] }
    ];
}
export function hitPathLevelsFromLegacy(legacy) {
    return createHitPathLevels(legacy.pathConstructors ?? [], legacy.twoPathConstructors ?? [], legacy.threePathConstructors ?? []);
}
export function legacyHitPathCollectionsFromLevels(levels) {
    return {
        pathConstructors: [...levels[0].constructors],
        twoPathConstructors: [...levels[1].constructors],
        threePathConstructors: [...levels[2].constructors]
    };
}
export function hitPathConstructorsAt(levels, level) {
    return levels[level - 1].constructors;
}
/** Flatten in eliminator order: all 1-paths, then 2-paths, then 3-paths. */
export function flattenHitPathLevels(levels) {
    return [
        ...levels[0].constructors,
        ...levels[1].constructors,
        ...levels[2].constructors
    ];
}
export function hitPathConstructorCount(levels) {
    return levels.reduce((count, entry) => count + entry.constructors.length, 0);
}
export function highestHitPathLevel(levels) {
    for (let index = levels.length - 1; index >= 0; index--) {
        if (levels[index].constructors.length)
            return levels[index].level;
    }
    return 0;
}
/** Return the first non-empty level whose immediately lower support is empty. */
export function firstHitPathLevelGap(levels) {
    let lowerLevelMissing = false;
    for (const entry of levels) {
        if (!entry.constructors.length) {
            lowerLevelMissing = true;
        }
        else if (lowerLevelMissing) {
            return entry.level;
        }
    }
    return undefined;
}
export function hitPathLevelsAreContiguous(levels) {
    return firstHitPathLevelGap(levels) === undefined;
}
/** Validate untrusted or structured-cloned pathLevels before using them. */
export function assertCanonicalHitPathLevels(value) {
    if (!Array.isArray(value) || value.length !== SUPPORTED_HIT_PATH_LEVELS.length) {
        throw new Error("HIT pathLevels 必须包含一至三阶三个层级");
    }
    for (let index = 0; index < SUPPORTED_HIT_PATH_LEVELS.length; index++) {
        const expectedLevel = SUPPORTED_HIT_PATH_LEVELS[index];
        const entry = value[index];
        if (!entry || typeof entry !== "object"
            || entry.level !== expectedLevel
            || !Array.isArray(entry.constructors)) {
            throw new Error(`HIT pathLevels 第 ${expectedLevel} 阶结构无效`);
        }
    }
    const gap = firstHitPathLevelGap(value);
    if (gap !== undefined) {
        throw new Error(`HIT pathLevels 第 ${gap} 阶不能越过空的低阶路径层级`);
    }
}
//# sourceMappingURL=hit-path-levels.js.map