import assert from "node:assert/strict";

import { calcMaxReachOrd, lowerOrdinalBase } from "../js/hy/ordinal.js";
import { GameSaveLoad } from "../js/saveload.js";

// The stored base is zero-based: UI base 4 is stored as 3 and UI base 5 as 4.
// Rewards may be collected in either order, but collecting the less restrictive
// reward later must not raise the already lowered base.
assert.equal(lowerOrdinalBase(15, 3), 3);
assert.equal(lowerOrdinalBase(3, 4), 3,
    "base5 after base4 must not raise the stored ordinal base");
assert.equal(lowerOrdinalBase(4, 3), 3,
    "base4 after base5 must still lower the stored ordinal base");

const originalDocument = globalThis.document;
globalThis.document = { querySelectorAll: () => [] };
const loader = Object.create(GameSaveLoad.prototype);
function restore(rewards, savedBase, currentBase = 15) {
    const game = {
        rewards: [],
        ordBase: currentBase,
        fsGui: { skipRendering: false },
        ttGui: { skipRendering: false },
        hyperGui: { world: {
            getBlock: name => ({ name }),
            hitReward(tile) {
                game.rewards.push(tile.name);
                if (/^base[2-5]$/.test(tile.name)) {
                    game.ordBase = lowerOrdinalBase(game.ordBase, Number(tile.name.slice(4)) - 1);
                }
            }
        } },
        finishAchievement() {},
        updateProgressParam() { this.displayedBase = this.ordBase + 1; }
    };
    // Minimized global section from #36: base4 precedes base5, but the old
    // save stores 4 (display base 5). Exercise the real restoration boundary.
    const data = [rewards, 15189, 6696, 189, 3197, [1, 2, 3, 1, 2, 2], savedBase];
    loader.deserialize(game, JSON.stringify(data));
    assert.deepEqual(JSON.parse(loader.serialize(game)).slice(1, 6), data.slice(1, 6),
        "ordinal repair must preserve unrelated progress and the reached ordinal");
    assert.deepEqual(game.rewards, rewards);
    assert.deepEqual(game.nextOrd, calcMaxReachOrd(game.maxOrd, game.ordBase, rewards.includes("stepw")));
    return game;
}
try {
    const repaired = restore(["base4", "base5"], 4);
    assert.equal(repaired.displayedBase, 4,
        "#36: stale saved base must not override the earned base4 reward");
    assert.equal(restore(["base5", "base4"], 4).ordBase, 3);
    assert.equal(restore(["base4", "base5"], 3).ordBase, 3);
    for (const base of [2, 3, 4, 5]) {
        assert.equal(restore([`base${base}`], 15).ordBase, base - 1);
    }
    assert.equal(restore(["base2", "base3", "base4", "base5", "stepw"], 4).ordBase, 1);
    assert.equal(restore(["base5"], 2).ordBase, 2,
        "a saved base already below the reward limit must remain unchanged");
    assert.equal(restore([], 10, 1).ordBase, 10,
        "the previous game's lower base must not leak into a loaded save");
    assert.equal(restore(["base5"], 4, 1).ordBase, 4);
    assert.equal(restore(["base-1", "base-2"], 13).ordBase, 13,
        "incremental rewards must not be applied twice on load");
    loader.deserialize(repaired, loader.serialize(repaired));
    assert.equal(repaired.ordBase, 3, "the repaired save must remain stable on reload");
} finally {
    globalThis.document = originalDocument;
}

console.log("ordinal base reward monotonicity regression passed");
