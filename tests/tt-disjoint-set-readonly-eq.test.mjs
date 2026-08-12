import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { Core, findContextIndexByBondVarId } from "../js/tt/core.js";

const parser = new ASTParser();
const core = new Core();
const context = [
    ["x", parser.parse("True"), 123_456],
    ["y", parser.parse("True"), 123_457]
];

assert.equal(core.isBondVarIdEqual(123_456, 123_456), true,
    "a binder id must remain equal to itself without mutable union-find state");
assert.equal(core.isBondVarIdEqual(123_456, 123_457), false,
    "distinct binder ids must not compare equal");
assert.equal(findContextIndexByBondVarId(context, 123_456, (a, b) => a === b), 0,
    "context lookup must still find an exact binder id");
assert.equal(findContextIndexByBondVarId(context, 123_458, (a, b) => a === b), -1,
    "context lookup must not create or retain unknown binder ids");

console.log("disjoint-set read-only equality regression passed");
