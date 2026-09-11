import assert from "node:assert/strict";
import { ASTParser } from "../js/tt/astparser.js";
import { SemanticNbeKernel, tryNbeDefinitionalEqual, tryNbeNormalize } from "../js/tt/nbe-kernel.js";

const parser = new ASTParser();
const bare = { type: "var", name: "U" };
const zero = parser.parseSurface("U");
const one = parser.parseSurface("U1");
assert.equal(tryNbeDefinitionalEqual(bare, zero), true);
assert.equal(tryNbeDefinitionalEqual(bare, one), false);
assert.equal(tryNbeDefinitionalEqual(bare, parser.parseSurface("U@")), false);
assert.equal(parser.stringify(tryNbeNormalize(bare)), "U");
assert.equal(parser.stringify(tryNbeNormalize(one)), "(U@1)");
assert.equal(tryNbeDefinitionalEqual(parser.parseSurface("Uu"), parser.parseSurface("Uv")), false);
assert.equal(tryNbeDefinitionalEqual(bare, zero, [], { maxSteps: 1 }), null);

// Scope lookup precedes the universe shorthand. Locals named U remain local.
assert.equal(tryNbeDefinitionalEqual(
    { type: "var", name: "U", bondVarId: 7 }, zero, [["U", zero, 7]]
), false);
const identity = {
    type: "L", name: "U", bondVarId: 7,
    nodes: [zero, { type: "var", name: "U", bondVarId: 7 }]
};
assert.equal(tryNbeDefinitionalEqual(identity, parser.parseSurface("λA:U.A")), true);

// Explicit and bare universe arguments normalize equally under beta reduction.
const applied = {
    type: "apply", name: "",
    nodes: [{ type: "L", name: "A", nodes: [one, { type: "var", name: "A" }] }, bare]
};
assert.equal(tryNbeDefinitionalEqual(applied, zero), true);

// Rule patterns and values must use the same canonical universe encoding.
for (const pattern of [bare, zero]) {
    const kernel = new SemanticNbeKernel();
    kernel.replaceComputeRules({
        atZero: [{ pattern: [{ type: "var", name: "atZero" }, pattern],
            result: { type: "var", name: "true" } }]
    });
    const call = argument => ({ type: "apply", name: "",
        nodes: [{ type: "var", name: "atZero" }, argument] });
    assert.equal(parser.stringify(kernel.tryNormalize(call(bare))), "true");
    assert.equal(parser.stringify(kernel.tryNormalize(call(zero))), "true");
    assert.notEqual(parser.stringify(kernel.tryNormalize(call(one))), "true");
}
console.log("issue #47 bare universe kernel canonicalization regression passed");
