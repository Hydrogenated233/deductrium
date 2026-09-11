import assert from "node:assert/strict";
import {
    INFERENCE_SYMBOL_ALIASES,
    expandInferenceAliasAtCaret,
    expandInferenceAliasesInSurface
} from "../js/fs/symbol-aliases.js";
import { ASTParser } from "../js/fs/astparser.js";

assert.ok(INFERENCE_SYMBOL_ALIASES.length >= 20);
assert.equal(
    expandInferenceAliasesInSurface("\\forall x \\in Q \\to \\exists y (y \\le x)"),
    "∀ x ∈ Q → ∃ y (y ≤ x)"
);
assert.equal(
    expandInferenceAliasesInSurface("Q\\a and Q\\and -- \\to stays in comments"),
    "Q\\a and Q\\and -- \\to stays in comments"
);
assert.equal(
    expandInferenceAliasesInSurface('"\\lambda" `\\to` \\\\to'),
    '"\\lambda" `\\to` \\\\to'
);
assert.equal(expandInferenceAliasAtCaret("\\forall", 7)?.value, "∀");
assert.equal(expandInferenceAliasAtCaret("Q\\a", 3), null);
assert.equal(expandInferenceAliasAtCaret("Q \\to", 5)?.value, "Q →");

const parser = new ASTParser();
assert.equal(
    parser.stringifyTight(parser.parse("Q∖a")),
    "Q∖a"
);
assert.equal(
    parser.stringifyTight(parser.parse("x∧y")),
    "x∧y"
);
for (const method of ["stringify", "stringifyTight"]) {
    const unique = parser.parse("E!x:x=x");
    const printed = parser[method](unique);
    assert.match(printed, /∃!/);
    assert.deepEqual(parser.parse(printed), unique,
        "Unicode printing must preserve unique existence");
}

console.log("inference Unicode symbol alias regression passed");
