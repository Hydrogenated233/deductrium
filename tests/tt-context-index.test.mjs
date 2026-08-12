import assert from "node:assert/strict";

import {
    findContextByName,
    findContextEntriesBeforeByName,
    findContextIndexByBondVarId,
    findContextIndexByName,
    hasContextName,
    wrapVar
} from "../js/tt/core.js";

const inner = ["x", wrapVar("A"), 11];
const outer = ["x", wrapVar("B"), 22];
const context = [inner, outer];

assert.equal(findContextByName(context, "x"), inner,
    "name lookup must prefer the nearest binding");
assert.equal(findContextIndexByName(context, "x"), 0,
    "name index must return the nearest position");
assert.equal(hasContextName(context, "x"), true);
assert.equal(hasContextName(context, "missing"), false);
assert.deepEqual(findContextEntriesBeforeByName(context, "x", 1), [inner],
    "duplicate-name lookup must preserve scope ordering");

assert.equal(findContextIndexByBondVarId(context, 22, (a, b) => a === b), 1,
    "exact binder IDs must use the indexed path");
assert.equal(findContextIndexByBondVarId(context, 99, (a, b) => a === 22 && b === 99), 1,
    "equivalent binder IDs must retain the alpha-union fallback");
assert.equal(findContextIndexByBondVarId(context, 99, (a, b) => a === b), -1);

// Context remains a normal mutable array for callers; structural mutations
// must cause a fresh index rather than returning stale positions.
const head = ["head", wrapVar("C"), 33];
context.unshift(head);
assert.equal(findContextIndexByName(context, "head"), 0);
assert.equal(findContextIndexByName(context, "x"), 1);
context.push(["tail", wrapVar("D"), 44]);
assert.equal(findContextIndexByBondVarId(context, 44, (a, b) => a === b), 3);

console.log("context name/binder index regression passed");
