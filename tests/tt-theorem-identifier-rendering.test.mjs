import assert from "node:assert/strict";

import { isKnownTheoremIdentifier, theoremPreviewNeedsRefresh } from "../js/tt/theorem-validation.js";

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

assert.equal(
    theoremPreviewNeedsRefresh("f", "f", 2, 1, 4, 4),
    true,
    "a definition becoming valid must refresh an unchanged #t target"
);
assert.equal(
    theoremPreviewNeedsRefresh("f", "f", 2, 2, 5, 4),
    true,
    "a folder/scope change must refresh an unchanged #t target"
);
assert.equal(
    theoremPreviewNeedsRefresh("f", "f", 2, 2, 5, 5),
    false,
    "an unchanged target and context may reuse its preview"
);

console.log("theorem identifier rendering regression passed");
