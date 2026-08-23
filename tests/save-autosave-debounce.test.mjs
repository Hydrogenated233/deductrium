import assert from "node:assert/strict";

import { GameSaveLoad } from "../js/saveload.js";

const loader = Object.create(GameSaveLoad.prototype);
loader.stateChangeTimer = false;
loader.timeOut = 3_000;

const originalSetTimeout = globalThis.setTimeout;
const originalClearTimeout = globalThis.clearTimeout;
const scheduled = new Map();
let nextTimerId = 1;
let saveCalls = 0;

globalThis.setTimeout = (callback, delay) => {
    const id = nextTimerId++;
    scheduled.set(id, { callback, delay });
    return id;
};
globalThis.clearTimeout = id => {
    scheduled.delete(id);
};
loader.save = () => {
    saveCalls++;
};

try {
    const game = {};
    loader.stateChange(game);
    const firstTimer = loader.stateChangeTimer;
    loader.stateChange(game);
    const secondTimer = loader.stateChangeTimer;

    assert.notEqual(secondTimer, firstTimer,
        "continuous movement must postpone autosave instead of keeping the first deadline");
    assert.equal(scheduled.has(firstTimer), false,
        "the previous autosave timer must be cancelled when state changes again");
    assert.equal(scheduled.size, 1);
    assert.equal(scheduled.get(secondTimer)?.delay, loader.timeOut);

    scheduled.get(secondTimer).callback();
    assert.equal(saveCalls, 1);
    assert.equal(loader.stateChangeTimer, false);
    assert.equal(scheduled.size, 0);

    loader.stateChange(game);
    assert.notEqual(loader.stateChangeTimer, false);
    loader.flush(game);
    assert.equal(saveCalls, 2,
        "pagehide/visibility flush must still save a pending debounced change immediately");
    assert.equal(loader.stateChangeTimer, false);
    assert.equal(scheduled.size, 0);
} finally {
    globalThis.setTimeout = originalSetTimeout;
    globalThis.clearTimeout = originalClearTimeout;
}

console.log("autosave debounce regression passed");
