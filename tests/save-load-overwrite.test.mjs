import assert from "node:assert/strict";

const { GameSaveLoad } = await import("../js/saveload.js");
const loader = Object.create(GameSaveLoad.prototype);

const reloadCalls = [];
const game = {
    creative: true,
    rewards: ["oldReward", "[ach]Old Achievement"],
    fsGui: { skipRendering: false },
    ttGui: { skipRendering: false },
    hyperGui: {
        world: {
            reload() { reloadCalls.push("map"); },
            getBlock(name) { return { name, text: "reward", type: 2 }; },
            hitReward(_block, hash) { game.rewards.push(hash); }
        }
    },
    finishAchievement(name) { game.rewards.push("[ach]" + name); },
    updateProgressParam() { }
};

loader.clearState(game);
assert.deepEqual(reloadCalls, ["map"], "importing a save must reset the map in creative mode");

const classChanges = [];
const achievementNode = {
    classList: {
        remove(name) { classChanges.push(["remove", name]); },
        add(name) { classChanges.push(["add", name]); }
    },
    parentElement: {
        classList: {
            add(name) { classChanges.push(["parent-add", name]); }
        }
    }
};
const previousDocument = globalThis.document;
globalThis.document = {
    querySelectorAll(selector) {
        assert.equal(selector, ".achievement div");
        return [achievementNode];
    }
};

try {
    loader.deserialize(game, JSON.stringify([
        ["newReward", "[ach]New Achievement", "[set]new-setting"],
        0, 0, 0, 1, [1], 15
    ]));
} finally {
    globalThis.document = previousDocument;
}

assert.deepEqual(game.rewards, ["newReward", "[ach]New Achievement", "[set]new-setting"],
    "importing a save must replace old rewards and achievements");
assert.deepEqual(classChanges, [["remove", "achieved"], ["parent-add", "locked"]],
    "importing a save must clear old achievement markers");

console.log("save import overwrite regression passed");
