/** Lean-like keyboard aliases for deduction-layer formula syntax. */
import { COMMON_SYMBOL_ALIASES } from "../symbol-aliases.js";
export const INFERENCE_SYMBOL_ALIASES = Object.freeze([
    ...COMMON_SYMBOL_ALIASES,
    { alias: "forall", symbol: "∀" },
    { alias: "all", symbol: "∀" },
    { alias: "exists", symbol: "∃" },
    { alias: "ex", symbol: "∃" },
    { alias: "in", symbol: "∈" },
    { alias: "not", symbol: "¬" },
    { alias: "neg", symbol: "¬" },
    { alias: "iff", symbol: "↔" },
    { alias: "leftrightarrow", symbol: "↔" },
    { alias: "subset", symbol: "⊂" },
    { alias: "cup", symbol: "∪" },
    { alias: "union", symbol: "∪" },
    { alias: "cap", symbol: "∩" },
    { alias: "inter", symbol: "∩" },
    { alias: "intersection", symbol: "∩" },
    { alias: "and", symbol: "∧" },
    { alias: "an", symbol: "∧" },
    { alias: "wedge", symbol: "∧" },
    { alias: "or", symbol: "∨" },
    { alias: "v", symbol: "∨" },
    { alias: "vee", symbol: "∨" },
    { alias: "le", symbol: "≤" },
    { alias: "leq", symbol: "≤" },
    { alias: "ge", symbol: "≥" },
    { alias: "geq", symbol: "≥" },
    { alias: "mid", symbol: "∣" },
    { alias: "nat", symbol: "ℕ" },
    { alias: "int", symbol: "ℤ" },
    { alias: "rat", symbol: "ℚ" },
    { alias: "real", symbol: "ℝ" },
    { alias: "setminus", symbol: "∖" },
    { alias: "smallsetminus", symbol: "∖" }
]);
const aliasesByName = new Map(INFERENCE_SYMBOL_ALIASES.map(({ alias, symbol }) => [alias.toLowerCase(), symbol]));
export function inferenceSymbolForAlias(source) {
    const name = source.startsWith("\\") ? source.slice(1) : source;
    if (!/^[A-Za-z][A-Za-z0-9]*$/u.test(name))
        return null;
    return aliasesByName.get(name.toLowerCase()) ?? null;
}
function isNameChar(char) {
    return !!char && /[\p{L}\p{N}_$]/u.test(char);
}
function isAliasBoundary(source, start) {
    const previous = source[start - 1];
    let slashes = 0;
    for (let cursor = start - 1; cursor >= 0 && source[cursor] === "\\"; cursor--)
        slashes++;
    if (slashes % 2 === 1)
        return false;
    // In the inference grammar, backslash is set difference.  Requiring a
    // boundary prevents `Q\a` and `Q\and` from becoming aliases.
    return start === 0 || !isNameChar(previous);
}
function isCaretAliasBoundary(source, start) {
    let slashes = 0;
    for (let cursor = start - 1; cursor >= 0 && source[cursor] === "\\"; cursor--)
        slashes++;
    // An explicit Space is unambiguous user input, so permit aliases directly
    // after an identifier while retaining escaped-backslash protection.
    return slashes % 2 === 0;
}
function quotedEnd(source, start, quote) {
    let cursor = start + 1;
    while (cursor < source.length) {
        if (source[cursor] === "\\") {
            cursor += 2;
            continue;
        }
        if (source[cursor] === quote)
            return cursor + 1;
        cursor++;
    }
    return source.length;
}
/** Expand aliases in formulas, commands, and scripts without touching opaque text. */
export function expandInferenceAliasesInSurface(source) {
    if (typeof source !== "string" || !source)
        return source;
    let output = "";
    let cursor = 0;
    while (cursor < source.length) {
        const char = source[cursor];
        if (char === '"' || char === "`") {
            const end = quotedEnd(source, cursor, char);
            output += source.slice(cursor, end);
            cursor = end;
            continue;
        }
        if (char === "-" && source[cursor + 1] === "-") {
            const newline = source.indexOf("\n", cursor + 2);
            const end = newline < 0 ? source.length : newline;
            output += source.slice(cursor, end);
            cursor = end;
            continue;
        }
        if (char === "\\" && source[cursor + 1] !== "\\" && isAliasBoundary(source, cursor)) {
            let end = cursor + 1;
            if (/[A-Za-z]/u.test(source[end] ?? "")) {
                end++;
                while (end < source.length && /[A-Za-z0-9]/u.test(source[end]))
                    end++;
            }
            const alias = source.slice(cursor, end);
            const symbol = inferenceSymbolForAlias(alias);
            const next = source[end];
            if (symbol && !isNameChar(next)) {
                output += symbol;
                cursor = end;
                continue;
            }
        }
        output += char;
        cursor++;
    }
    return output;
}
export function expandInferenceAliasAtCaret(value, selectionStart, selectionEnd = selectionStart) {
    if (selectionStart !== selectionEnd)
        return null;
    const caret = Math.max(0, Math.min(value.length, selectionStart));
    const beforeCaret = value.slice(0, caret);
    const match = /\\([A-Za-z][A-Za-z0-9]*)$/u.exec(beforeCaret);
    if (!match || match.index === undefined || !isCaretAliasBoundary(beforeCaret, match.index))
        return null;
    const symbol = inferenceSymbolForAlias(match[0]);
    if (!symbol)
        return null;
    return {
        value: `${value.slice(0, match.index)}${symbol}${value.slice(caret)}`,
        caret: match.index + symbol.length,
        symbol
    };
}
const installedInputs = new WeakSet();
export function installInferenceSymbolAliases(input) {
    if (!input || installedInputs.has(input))
        return;
    installedInputs.add(input);
    let composing = false;
    input.addEventListener("compositionstart", () => composing = true);
    input.addEventListener("compositionend", () => composing = false);
    input.addEventListener("keydown", event => {
        const keyEvent = event;
        if (composing || keyEvent.isComposing || keyEvent.keyCode === 229
            || keyEvent.key !== " " || keyEvent.ctrlKey || keyEvent.altKey
            || keyEvent.metaKey || keyEvent.shiftKey)
            return;
        const expansion = expandInferenceAliasAtCaret(input.value, input.selectionStart ?? input.value.length, input.selectionEnd ?? input.selectionStart ?? input.value.length);
        if (!expansion)
            return;
        keyEvent.preventDefault();
        input.value = expansion.value;
        try {
            input.setSelectionRange(expansion.caret, expansion.caret);
        }
        catch { }
        input.dispatchEvent(new Event("input", { bubbles: true }));
    });
}
//# sourceMappingURL=symbol-aliases.js.map