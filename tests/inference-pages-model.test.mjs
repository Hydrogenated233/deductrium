import assert from "node:assert/strict";
import { InferencePageStore } from "../js/fs/inference-pages.js";

const store = new InferencePageStore();
assert.equal(store.size, 1);
assert.equal(store.active.name, "主表");

store.appendProposition("main");
store.setCommandSnapshot({ input: "d", buffer: ["d"], state: { step: 1 } });
const mainId = store.activeId;

const second = store.create("第二表", { propositions: ["second"] });
assert.equal(store.activeId, mainId, "creating a page must not activate it");
assert.deepEqual(store.page("第二表").propositions, ["second"]);

store.activate("第二表");
assert.equal(store.active.name, "第二表");
store.setCommandSnapshot({ input: "newpage 第三表" });
const third = store.create("第三表");
assert.equal(store.active.name, "第二表");

store.reorder(third.id, mainId);
assert.deepEqual(store.pages.map(page => page.name), ["第三表", "主表", "第二表"]);
assert.equal(store.active.name, "第二表", "reordering must preserve active page");
store.reorder(third.id, third.id);
assert.deepEqual(store.pages.map(page => page.name), ["第三表", "主表", "第二表"], "reordering onto itself must be a no-op");

store.activate(mainId);
store.delete(mainId);
assert.equal(store.active.name, "第三表", "deleting first active page selects the next page");
store.activate("第二表");
store.delete("第二表");
assert.equal(store.active.name, "第三表", "deleting later active page selects the previous page");
assert.throws(() => store.delete("第三表"), /至少需要保留一个/);

const roundTrip = InferencePageStore.deserialize(new InferencePageStore([
    { id: "page-41", name: "主表", propositions: [1], command: { input: "x", buffer: ["d"], state: "paused" } },
    { id: "page-7", name: "子表", propositions: [2] }
], "page-7").serialize());
assert.deepEqual(roundTrip.pages.map(page => page.id), ["page-41", "page-7"]);
assert.equal(roundTrip.activeId, "page-7");
assert.deepEqual(roundTrip.page("主表").command, { input: "x", buffer: ["d"], state: "paused" });
const generated = roundTrip.create("新表");
assert.equal(generated.id, "page-42", "generated ids must continue after restored ids");

assert.throws(() => roundTrip.create("two words"), /名称必须/);
assert.throws(() => roundTrip.create("主表"), /已存在/);
assert.throws(() => roundTrip.activate("missing"), /不存在/);

console.log("inference page model regression passed");
