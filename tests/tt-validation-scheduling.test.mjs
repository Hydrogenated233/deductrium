import assert from "node:assert/strict";

import {
    canReuseTheoremResultOnBlur,
    theoremInputIndexBeforeItem,
    theoremValidationPositionMatches,
    TheoremValidationCoordinator
} from "../js/tt/theorem-validation.js";

const items = [
    { kind: "theorem" },
    { kind: "folder" },
    { kind: "theorem" },
    { kind: "folder" },
    { kind: "theorem" },
    { kind: "theorem" }
];

assert.equal(theoremInputIndexBeforeItem(items, 1), 1);
assert.equal(theoremInputIndexBeforeItem(items, 3), 2);
assert.equal(theoremInputIndexBeforeItem(items, items.length), 4);

const unchanged = {
    programmatic: false,
    canReuseRenderedResult: true,
    originalValue: "double:=ind_nat _ 0 _",
    currentValue: "double:=ind_nat _ 0 _",
    validationInvalidated: false,
    updateDefinitions: false
};
assert.equal(canReuseTheoremResultOnBlur(unchanged), true);
assert.equal(canReuseTheoremResultOnBlur({ ...unchanged, currentValue: unchanged.currentValue + " " }), false);
assert.equal(canReuseTheoremResultOnBlur({ ...unchanged, validationInvalidated: true }), false);
assert.equal(canReuseTheoremResultOnBlur({ ...unchanged, updateDefinitions: true }), false);
assert.equal(canReuseTheoremResultOnBlur({ ...unchanged, programmatic: true }), false);

const coordinator = new TheoremValidationCoordinator();
const firstRun = coordinator.request(4);
assert.deepEqual(firstRun, { id: 1, startIndex: 4 });
const queuedRun = coordinator.request(9);
assert.equal(queuedRun, null, "a second validation must wait for the in-flight run");
assert.equal(coordinator.isCurrent(firstRun.id), false, "the older run is cancelled immediately");
const promotedRun = coordinator.complete(firstRun.id);
assert.deepEqual(promotedRun, { id: 2, startIndex: 9 }, "the newest suffix starts after the old worker call settles");
assert.equal(coordinator.isCurrent(promotedRun.id), true);
assert.equal(coordinator.complete(promotedRun.id), null);

// A pending result must be rejected when a row is inserted before its input.
// The original input remains connected, so this identity/position check is
// the guard that prevents writing the result into the newly inserted slot.
const firstInput = {};
const pendingInput = {};
const insertedInput = {};
const itemIds = new Map([
    [firstInput, "first"],
    [pendingInput, "pending"],
    [insertedInput, "inserted"]
]);
assert.equal(
    theoremValidationPositionMatches(
        [firstInput, pendingInput],
        pendingInput,
        1,
        "pending",
        input => itemIds.get(input) ?? null
    ),
    true
);
assert.equal(
    theoremValidationPositionMatches(
        [firstInput, insertedInput, pendingInput],
        pendingInput,
        1,
        "pending",
        input => itemIds.get(input) ?? null
    ),
    false,
    "inserting a row before a pending theorem invalidates its old index"
);

console.log("theorem validation scheduling regression passed");
