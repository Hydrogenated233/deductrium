import assert from "node:assert/strict";

import { TTWorkerMutationQueue } from "../js/tt/worker-mutation-queue.js";

const queue = new TTWorkerMutationQueue();
const events = [];
const pause = () => new Promise(resolve => setTimeout(resolve, 0));

const first = queue.enqueue(async () => {
    events.push("configure:start");
    await pause();
    events.push("configure:end");
});
const second = queue.enqueue(async () => {
    events.push("truncate");
});
const third = queue.enqueue(async () => {
    events.push("set-definition");
});

await Promise.all([first, second, third]);
assert.deepEqual(events, ["configure:start", "configure:end", "truncate", "set-definition"]);

await assert.rejects(queue.enqueue(async () => {
    throw new Error("simulated worker failure");
}));
await queue.enqueue(async () => {
    events.push("after-failure");
});
assert.equal(events.at(-1), "after-failure");

console.log("Worker mutation queue ordering regression passed");
