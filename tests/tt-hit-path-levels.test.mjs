import assert from "node:assert/strict";

import {
    SUPPORTED_HIT_PATH_LEVELS,
    assertCanonicalHitPathLevels,
    createHitPathLevels,
    firstHitPathLevelGap,
    flattenHitPathLevels,
    highestHitPathLevel,
    hitPathConstructorCount,
    hitPathConstructorsAt,
    hitPathLevelsAreContiguous,
    hitPathLevelsFromCanonicalOrLegacy,
    hitPathLevelsFromLegacy,
    legacyHitPathCollectionsFromLevels
} from "../js/tt/hit-path-levels.js";

assert.deepEqual(SUPPORTED_HIT_PATH_LEVELS, [1, 2, 3]);

const path1 = [{ name: "loopA" }, { name: "loopB" }];
const path2 = [{ name: "face" }];
const path3 = [{ name: "cell" }];
const levels = createHitPathLevels(path1, path2, path3);

assert.deepEqual(levels, [
    { level: 1, constructors: path1 },
    { level: 2, constructors: path2 },
    { level: 3, constructors: path3 }
]);
assert.notEqual(levels[0].constructors, path1,
    "the adapter must own its arrays rather than aliasing caller collections");
assert.equal(levels[0].constructors[0], path1[0],
    "the structural adapter must not attempt to clone constructor payloads");
assert.deepEqual(hitPathConstructorsAt(levels, 1), path1);
assert.deepEqual(hitPathConstructorsAt(levels, 2), path2);
assert.deepEqual(hitPathConstructorsAt(levels, 3), path3);
assert.deepEqual(
    flattenHitPathLevels(levels).map(constructor => constructor.name),
    ["loopA", "loopB", "face", "cell"],
    "flattening must retain source order inside stable dimension order"
);
assert.equal(hitPathConstructorCount(levels), 4);
assert.equal(highestHitPathLevel(levels), 3);
assert.equal(firstHitPathLevelGap(levels), undefined);
assert.equal(hitPathLevelsAreContiguous(levels), true);
assert.doesNotThrow(() => assertCanonicalHitPathLevels(levels));
assert.equal(
    hitPathLevelsFromCanonicalOrLegacy({
        pathLevels: levels,
        pathConstructors: [{ name: "stale" }]
    }),
    levels,
    "canonical pathLevels must take precedence over legacy projections"
);

const legacy = hitPathLevelsFromLegacy({
    pathConstructors: path1,
    threePathConstructors: path3
});
assert.deepEqual(legacy, [
    { level: 1, constructors: path1 },
    { level: 2, constructors: [] },
    { level: 3, constructors: path3 }
]);
assert.equal(firstHitPathLevelGap(legacy), 3);
assert.equal(hitPathLevelsAreContiguous(legacy), false);
assert.throws(
    () => assertCanonicalHitPathLevels(legacy),
    /第 3 阶不能越过空的低阶路径层级/
);

const projected = legacyHitPathCollectionsFromLevels(levels);
assert.deepEqual(projected, {
    pathConstructors: path1,
    twoPathConstructors: path2,
    threePathConstructors: path3
});
assert.notEqual(projected.pathConstructors, levels[0].constructors);
assert.notEqual(projected.twoPathConstructors, levels[1].constructors);
assert.notEqual(projected.threePathConstructors, levels[2].constructors);

const empty = createHitPathLevels([], [], []);
assert.equal(highestHitPathLevel(empty), 0);
assert.equal(hitPathConstructorCount(empty), 0);
assert.equal(hitPathLevelsAreContiguous(empty), true,
    "requiring a first path remains a declaration-level policy");
assert.doesNotThrow(() => assertCanonicalHitPathLevels(empty));

const firstOnly = createHitPathLevels(path1, [], []);
assert.equal(highestHitPathLevel(firstOnly), 1);
assert.equal(hitPathLevelsAreContiguous(firstOnly), true);

const throughSecond = createHitPathLevels(path1, path2, []);
assert.equal(highestHitPathLevel(throughSecond), 2);
assert.equal(hitPathLevelsAreContiguous(throughSecond), true);

assert.throws(() => assertCanonicalHitPathLevels([]), /必须包含一至三阶三个层级/);
assert.throws(
    () => assertCanonicalHitPathLevels([
        { level: 1, constructors: [] },
        { level: 2, constructors: [] },
        { level: 3, constructors: [] },
        { level: 4, constructors: [] }
    ]),
    /必须包含一至三阶三个层级/,
    "the canonical adapter must not imply user-facing fourth-dimensional support"
);
assert.throws(
    () => assertCanonicalHitPathLevels([
        { level: 1, constructors: [] },
        { level: 3, constructors: [] },
        { level: 2, constructors: [] }
    ]),
    /第 2 阶结构无效/
);
assert.throws(
    () => assertCanonicalHitPathLevels([
        { level: 1, constructors: [] },
        { level: 2, constructors: null },
        { level: 3, constructors: [] }
    ]),
    /第 2 阶结构无效/
);

console.log("HIT pathLevels adapter regression passed");
