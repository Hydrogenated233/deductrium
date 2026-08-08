import assert from "node:assert/strict";

import { isKnownTheoremIdentifier } from "../js/tt/theorem-validation.js";

const system = new Set(["True"]);
const macros = new Set();
const userDefinitions = new Set(["paireq", "bijporp"]);

assert.equal(
    isKnownTheoremIdentifier("paireq", system, macros, userDefinitions),
    true,
    "a checked user definition must remain classified when the macro set is rebuilt"
);
assert.equal(
    isKnownTheoremIdentifier("paireq'", system, macros, userDefinitions),
    true,
    "generated prime variants use the same base identifier"
);
assert.equal(
    isKnownTheoremIdentifier("unknown", system, macros, userDefinitions),
    false,
    "unknown names must not be classified as constants"
);

console.log("theorem identifier rendering regression passed");
