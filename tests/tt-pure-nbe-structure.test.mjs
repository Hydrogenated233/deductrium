import assert from "node:assert/strict";
import { existsSync } from "node:fs";

import * as coreModule from "../js/tt/core.js";

const { Core } = coreModule;
const removedMethods = [
    "check",
    "checkConst",
    "equal",
    "fillInfered",
    "lazyExpand",
    "markAndCheckInferedValue",
    "reduce",
    "registConstType",
    "showInfered",
    "whnf"
];

assert.equal("InferTable" in coreModule, false,
    "the production module must not export the legacy mutable InferTable");
for (const method of removedMethods) {
    assert.equal(method in Core.prototype, false,
        `Core.prototype.${method} must not survive the pure NbE migration`);
}

for (const flag of ["closureNbE", "semanticNbE", "semanticWhnf", "semanticTypeCheck"]) {
    assert.equal(flag in Core, false,
        `Core.${flag} must not allow the production NbE kernel to be disabled`);
}

assert.equal(
    existsSync(new URL("../js/tt/closure.js", import.meta.url)),
    false,
    "the abandoned closure evaluator must not be shipped beside the production NbE kernel"
);

const core = new Core();
for (const field of ["inferTable", "bondVarRel", "eagerInferRel"]) {
    assert.equal(field in core.state, false,
        `Core.state.${field} must not retain mutable legacy checker state`);
}

console.log("pure NbE production structure regression passed");
