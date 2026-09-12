import assert from "node:assert/strict";
import {
    INFERENCE_SYMBOL_ALIASES,
    expandInferenceAliasAtCaret,
    expandInferenceAliasesInSurface,
    installInferenceSymbolAliases
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

for (const [source, expected, symbol] of [
    ["P\\r", "P→", "→"],
    ["Q\\and", "Q∧", "∧"],
    ["α\\and", "α∧", "∧"],
    ["$\\alpha", "$α", "α"],
    ["(P)\\r", "(P)→", "→"]
]) {
    assert.deepEqual(expandInferenceAliasAtCaret(source, source.length),
        { value: expected, caret: expected.length, symbol });
}
assert.equal(expandInferenceAliasesInSurface("P\\r"), "P\\r",
    "explicit Space must not change legacy parsing");
for (const source of ["P\\\\r"]) {
    assert.equal(expandInferenceAliasAtCaret(source, source.length), null);
}
assert.equal(expandInferenceAliasAtCaret("-- comment\nP\\r", 14)?.value, "-- comment\nP→");
assert.deepEqual(expandInferenceAliasAtCaret("P\\rQ", 3),
    { value: "P→Q", caret: 2, symbol: "→" });

class FormulaInput extends EventTarget {
    value = "P\\rQ";
    selectionStart = 3;
    selectionEnd = 3;
    setSelectionRange(start, end) {
        this.selectionStart = start;
        this.selectionEnd = end;
    }
}
const input = new FormulaInput();
installInferenceSymbolAliases(input);
installInferenceSymbolAliases(input);
let inputEvents = 0;
input.addEventListener("input", () => inputEvents++);
function space(properties = {}) {
    const event = new Event("keydown", { cancelable: true });
    Object.assign(event, { key: " ", ...properties });
    input.dispatchEvent(event);
    return event;
}
for (const properties of [
    { ctrlKey: true }, { altKey: true }, { metaKey: true }, { shiftKey: true },
    { isComposing: true }, { keyCode: 229 }
]) {
    assert.equal(space(properties).defaultPrevented, false);
    assert.equal(input.value, "P\\rQ");
}
input.dispatchEvent(new Event("compositionstart"));
assert.equal(space().defaultPrevented, false);
input.dispatchEvent(new Event("compositionend"));
input.selectionEnd = 4;
assert.equal(space().defaultPrevented, false);
input.selectionEnd = 3;
assert.equal(space().defaultPrevented, true);
assert.equal(input.value, "P→Q");
assert.equal(input.selectionStart, 2);
assert.equal(input.selectionEnd, 2);
assert.equal(inputEvents, 1);
assert.equal(space().defaultPrevented, false);

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
