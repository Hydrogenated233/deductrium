import assert from "node:assert/strict";

import { Core } from "../js/tt/core.js";

const target = {
    type: "apply",
    name: "",
    nodes: [
        { type: "var", name: "old" },
        { type: "var", name: "tail" }
    ],
    checked: { type: "var", name: "stale" },
    err: "target-error"
};
const source = {
    type: "var",
    name: "new",
    bondVarId: 42,
    checked: { type: "var", name: "ignored-by-clone" }
};

Core.assign(target, source);
assert.equal(target.type, "var");
assert.equal(target.name, "new");
assert.equal(target.nodes, undefined);
assert.equal(target.checked, null,
    "leaf assignment must preserve Core.clone's unchecked behavior");
assert.equal(target.err, "target-error",
    "leaf assignment must preserve Core.assign's existing error metadata behavior");
assert.equal(target.bondVarId, 42);

console.log("Core.assign leaf fast path regression passed");
