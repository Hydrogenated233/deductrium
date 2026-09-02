/**
 * Lean-like keyboard aliases for the type-theory surface syntax.
 *
 * The parser deliberately keeps its compact ASCII token representation, but
 * users should not have to remember that representation while editing.  The
 * same alias table is also used for pasted text and save-boundary migration,
 * so input that arrives without a keydown event is normalized consistently.
 */

export type TypeTheorySymbolAlias = {
    /** Alias without the leading backslash, for compact display in help UI. */
    alias: string;
    /** Unicode surface symbol inserted into the input. */
    symbol: string;
};

/**
 * Supported aliases, ordered from the shortest/common spelling to the more
 * descriptive spellings.  Keep this list data-only so the progress/help page
 * can render the same source of truth as the editor.
 */
export const TYPE_THEORY_SYMBOL_ALIASES: readonly TypeTheorySymbolAlias[] = Object.freeze([
    { alias: "l", symbol: "λ" },
    { alias: "lam", symbol: "λ" },
    { alias: "lambda", symbol: "λ" },
    { alias: "p", symbol: "Π" },
    { alias: "pi", symbol: "Π" },
    { alias: "prod", symbol: "Π" },
    { alias: "s", symbol: "Σ" },
    { alias: "sig", symbol: "Σ" },
    { alias: "sigma", symbol: "Σ" },
    { alias: "sum", symbol: "Σ" },
    { alias: "x", symbol: "×" },
    { alias: "times", symbol: "×" },
    { alias: "cross", symbol: "×" },
    { alias: "w", symbol: "W" },
    { alias: "to", symbol: "→" },
    { alias: "arr", symbol: "→" },
    { alias: "arrow", symbol: "→" },
    { alias: "rarr", symbol: "→" },
    { alias: "eqv", symbol: "≃" },
    { alias: "simeq", symbol: "≃" },
    { alias: "defeq", symbol: "≡" },
    { alias: "identical", symbol: "≡" },
    { alias: "*", symbol: "▪" },
    { alias: "star", symbol: "▪" },
    { alias: "comp", symbol: "▪" },
    { alias: "concat", symbol: "▪" }
]);

const aliasesByName = new Map(
    TYPE_THEORY_SYMBOL_ALIASES.map(({ alias, symbol }) => [alias.toLowerCase(), symbol])
);

/** Resolve either `\\lambda` or `lambda` to its surface symbol. */
export function typeTheorySymbolForAlias(source: string): string | null {
    const name = source.startsWith("\\") ? source.slice(1) : source;
    if (!/^(?:[A-Za-z][A-Za-z0-9]*|\*)$/u.test(name)) return null;
    return aliasesByName.get(name.toLowerCase()) ?? null;
}

function isAliasNameChar(char: string | undefined): boolean {
    return !!char && /[A-Za-z0-9_]/u.test(char);
}

function aliasQuotedEnd(source: string, start: number, quote: string): number {
    let cursor = start + 1;
    while (cursor < source.length) {
        if (source[cursor] === "\\") {
            cursor += 2;
            continue;
        }
        if (source[cursor] === quote) return cursor + 1;
        cursor++;
    }
    return source.length;
}

/**
 * Expand backslash aliases in pasted/submitted surface text.  Keyboard input
 * normally expands an alias when Space is pressed, but pasted text and saved
 * drafts can reach the parser before that event.  Comments and quoted spans
 * stay opaque so a literal `\*` is not rewritten accidentally.
 */
export function expandTypeTheoryAliasesInSurface(source: string): string {
    if (!source || typeof source !== "string") return source;
    let output = "";
    let cursor = 0;
    while (cursor < source.length) {
        const char = source[cursor];
        if (char === '"' || char === "`"
            || (char === "'"
                && (cursor === 0 || !/[\p{L}\p{N}_$@?#'!-]/u.test(source[cursor - 1])))) {
            const end = aliasQuotedEnd(source, cursor, char);
            output += source.slice(cursor, end);
            cursor = end;
            continue;
        }
        if (char === "/" && source[cursor + 1] === "/") {
            const newline = source.indexOf("\n", cursor + 2);
            const end = newline < 0 ? source.length : newline;
            output += source.slice(cursor, end);
            cursor = end;
            continue;
        }
        if (char === "/" && source[cursor + 1] === "*") {
            const marker = source.indexOf("*/", cursor + 2);
            const end = marker < 0 ? source.length : marker + 2;
            output += source.slice(cursor, end);
            cursor = end;
            continue;
        }
        if (char === "\\" && source[cursor + 1] !== undefined) {
            let end = cursor + 1;
            if (source[end] === "*") {
                end++;
            } else if (/[A-Za-z]/u.test(source[end])) {
                end++;
                while (end < source.length && /[A-Za-z0-9]/u.test(source[end])) end++;
            }
            const alias = source.slice(cursor, end);
            const symbol = typeTheorySymbolForAlias(alias);
            const escaped = cursor > 0 && source[cursor - 1] === "\\";
            const next = source[end];
            if (symbol && !escaped && (alias === "\\*" || !isAliasNameChar(next))) {
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

export type TypeTheoryAliasExpansion = {
    value: string;
    caret: number;
    symbol: string;
};

/**
 * Replace the alias immediately before a collapsed selection/caret.
 *
 * Returning `null` means that no supported alias is present.  The helper is
 * intentionally pure so keyboard behavior can be regression-tested without a
 * browser DOM.
 */
export function expandTypeTheoryAliasAtCaret(
    value: string,
    selectionStart: number,
    selectionEnd = selectionStart
): TypeTheoryAliasExpansion | null {
    if (selectionStart !== selectionEnd) return null;
    const caret = Math.max(0, Math.min(value.length, selectionStart));
    const beforeCaret = value.slice(0, caret);
    const match = /\\((?:[A-Za-z][A-Za-z0-9]*|\*))$/u.exec(beforeCaret);
    if (!match || match.index === undefined) return null;

    // A doubled backslash is commonly used to type a literal backslash.  Do
    // not consume the second half of that escape as an input alias.
    if (match.index > 0 && beforeCaret[match.index - 1] === "\\") return null;
    const symbol = typeTheorySymbolForAlias(match[0]);
    if (!symbol) return null;
    const valueAfter = `${value.slice(0, match.index)}${symbol}${value.slice(caret)}`;
    return {
        value: valueAfter,
        caret: match.index + symbol.length,
        symbol
    };
}

type FormulaInput = HTMLInputElement | HTMLTextAreaElement;

// Rendering can recreate rows, but an input node may also be rebound by a
// restore path.  Avoid stacking duplicate key handlers in that case.
const installedInputs = new WeakSet<FormulaInput>();

/**
 * Install the Space-triggered alias expansion on one formula input.
 *
 * The generated `input` event is essential: theorem invalidation, autosave,
 * proof-session persistence, and syntax highlighting all subscribe to it.
 */
export function installTypeTheorySymbolAliases(input: FormulaInput | null | undefined): void {
    if (!input || installedInputs.has(input)) return;
    installedInputs.add(input);

    let composing = false;
    input.addEventListener("compositionstart", () => composing = true);
    input.addEventListener("compositionend", () => composing = false);
    input.addEventListener("keydown", event => {
        const keyEvent = event as KeyboardEvent;
        if (composing || keyEvent.isComposing || keyEvent.keyCode === 229) return;
        // Only a plain Space invokes an alias.  Modified spaces retain their
        // browser/editor meanings (for example, Shift+Space selection).
        if (keyEvent.key !== " " || keyEvent.ctrlKey || keyEvent.altKey
            || keyEvent.metaKey || keyEvent.shiftKey) return;
        const expansion = expandTypeTheoryAliasAtCaret(
            input.value,
            input.selectionStart ?? input.value.length,
            input.selectionEnd ?? input.selectionStart ?? input.value.length
        );
        if (!expansion) return;
        keyEvent.preventDefault();
        input.value = expansion.value;
        try {
            input.setSelectionRange(expansion.caret, expansion.caret);
        } catch {
            // A few embedded/custom controls expose selection properties but
            // reject setSelectionRange.  The value replacement still helps.
        }
        input.dispatchEvent(new Event("input", { bubbles: true }));
    });
}
