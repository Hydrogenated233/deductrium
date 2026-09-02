import assert from "node:assert/strict";

import {
    TYPE_THEORY_SYMBOL_ALIASES,
    expandTypeTheoryAliasAtCaret,
    expandTypeTheoryAliasesInSurface,
    installTypeTheorySymbolAliases,
    typeTheorySymbolForAlias
} from "../js/tt/symbol-aliases.js";
import { ASTParser } from "../js/tt/astparser.js";

for (const [source, symbol] of [
    ["\\l", "λ"],
    ["\\L", "λ"],
    ["\\lambda", "λ"],
    ["\\LaMbDa", "λ"],
    ["\\p", "Π"],
    ["\\PI", "Π"],
    ["\\prod", "Π"],
    ["\\s", "Σ"],
    ["\\SIGMA", "Σ"],
    ["\\sum", "Σ"],
    ["\\x", "×"],
    ["\\TiMeS", "×"],
    ["\\to", "→"],
    ["\\eqv", "≃"],
    ["\\defeq", "≡"],
    ["\\*", "▪"],
    ["\\star", "▪"],
    ["\\comp", "▪"]
]) {
    assert.equal(typeTheorySymbolForAlias(source), symbol, `${source} should resolve`);
}
assert.equal(typeTheorySymbolForAlias("lambda"), "λ", "bare alias should also resolve for help/rendering");
assert.equal(typeTheorySymbolForAlias("\\unknown"), null);
assert.equal(typeTheorySymbolForAlias("\\lambda!"), null);

assert.equal(TYPE_THEORY_SYMBOL_ALIASES.length > 10, true,
    "the shared alias table should contain the common structural symbols");

assert.deepEqual(expandTypeTheoryAliasAtCaret("\\l", 2), {
    value: "λ",
    caret: 1,
    symbol: "λ"
});
assert.deepEqual(expandTypeTheoryAliasAtCaret("f \\*", 4), {
    value: "f ▪",
    caret: 3,
    symbol: "▪"
});
assert.deepEqual(expandTypeTheoryAliasAtCaret("A: \\LaMbDa x", 10), {
    value: "A: λ x",
    caret: 4,
    symbol: "λ"
});
assert.deepEqual(expandTypeTheoryAliasAtCaret("\\p rest", 1), null,
    "an incomplete alias must not consume text after the caret");
assert.equal(expandTypeTheoryAliasAtCaret("\\nope", 5), null);
assert.equal(expandTypeTheoryAliasAtCaret("\\l", 0), null);
assert.equal(expandTypeTheoryAliasAtCaret("\\l", 2, 1), null,
    "a non-collapsed selection must remain untouched");
assert.equal(expandTypeTheoryAliasAtCaret("\\\\l", 3), null,
    "a doubled backslash is treated as a literal escape");
assert.equal(expandTypeTheoryAliasesInSurface("a\\*b + \\lambda x"), "a▪b + λ x");
assert.equal(expandTypeTheoryAliasesInSurface("// \\*\n\"\\lambda\""), "// \\*\n\"\\lambda\"",
    "comments and quoted text remain literal");
assert.equal(expandTypeTheoryAliasesInSurface("\\\\*"), "\\\\*",
    "escaped backslashes remain literal");

// Exercise the DOM adapter without requiring jsdom.  The real controls expose
// the same small surface used below.
function fakeInput(value) {
    const listeners = new Map();
    const input = {
        value,
        selectionStart: value.length,
        selectionEnd: value.length,
        addEventListener(type, listener) {
            listeners.set(type, listener);
        },
        setSelectionRange(start, end) {
            this.selectionStart = start;
            this.selectionEnd = end;
        },
        dispatchEvent(event) {
            this.dispatched = event;
            listeners.get("input")?.(event);
            return true;
        },
        keydown(event) {
            listeners.get("keydown")?.(event);
        }
    };
    return input;
}

const input = fakeInput("A \\l");
let inputEvents = 0;
input.addEventListener("input", () => inputEvents++);
installTypeTheorySymbolAliases(input);
// Calling the installer again must not stack a second key handler.
installTypeTheorySymbolAliases(input);
let prevented = false;
input.keydown({
    key: " ",
    ctrlKey: false,
    altKey: false,
    metaKey: false,
    shiftKey: false,
    isComposing: false,
    keyCode: 32,
    preventDefault() { prevented = true; }
});
assert.equal(input.value, "A λ");
assert.equal(input.selectionStart, 3);
assert.equal(input.selectionEnd, 3);
assert.equal(prevented, true);
assert.equal(inputEvents, 1, "alias replacement must dispatch the normal input event");
assert.equal(input.dispatched?.bubbles, true);

const untouched = fakeInput("\\l");
installTypeTheorySymbolAliases(untouched);
untouched.keydown({
    key: " ",
    ctrlKey: true,
    altKey: false,
    metaKey: false,
    shiftKey: false,
    isComposing: false,
    keyCode: 32,
    preventDefault() { throw new Error("modified Space must not be consumed"); }
});
assert.equal(untouched.value, "\\l");

const parser = new ASTParser();
assert.doesNotThrow(() => parser.parse("λx:Πa:U,U.x"),
    "the inserted Unicode symbols must remain accepted by the parser");
assert.doesNotThrow(() => parser.parseSurface("\\lambda x:U.x"),
    "pasted backslash aliases must be accepted by the strict surface parser");
assert.doesNotThrow(() => parser.parseSurface("a\\*b"),
    "the composition alias must be accepted before keyboard expansion");

console.log("type-theory symbol alias regression passed");
