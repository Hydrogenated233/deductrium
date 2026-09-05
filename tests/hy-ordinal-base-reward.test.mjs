import assert from "node:assert/strict";

import { lowerOrdinalBase } from "../js/hy/ordinal.js";

// The stored base is zero-based: UI base 4 is stored as 3 and UI base 5 as 4.
// Rewards may be collected in either order, but collecting the less restrictive
// reward later must not raise the already lowered base.
assert.equal(lowerOrdinalBase(15, 3), 3);
assert.equal(lowerOrdinalBase(3, 4), 3,
    "base5 after base4 must not raise the stored ordinal base");
assert.equal(lowerOrdinalBase(4, 3), 3,
    "base4 after base5 must still lower the stored ordinal base");

console.log("ordinal base reward monotonicity regression passed");
