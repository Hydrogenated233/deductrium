import { expandTypeTheoryAliasesInSurface } from "./symbol-aliases.js";

/**
 * One-shot migration for the old ASCII type-theory surface syntax.
 *
 * The parser still has an internal ASCII representation (L/P/S/X), but new
 * saves should carry the Unicode surface form.  This module deliberately
 * works on source text instead of parsing/stringifying an AST: that keeps
 * whitespace, comments, and user spelling intact while allowing us to tell a
 * binder marker from a normal identifier such as `List` or `LiftU`.
 */

const BINDER_SYMBOLS: Readonly<Record<string, string>> = Object.freeze({
    L: "λ",
    P: "Π",
    S: "Σ"
});

const LEGACY_OPERATORS: readonly [string, string][] = Object.freeze([
    ["===", "≡"],
    ["~=", "≃"],
    ["->", "→"],
    ["*", "▪"]
]);

/** Names that the legacy parser protects as atomic built-ins. */
const PROTECTED_WORDS = new Set([
    "List", "LiftU", "Loop2", "Pushout", "Wedge", "South", "Sus", "Sum",
    "S1", "S2", "S3", "S4", "LEM"
]);

/**
 * Identifier characters accepted by the old tokenizer for a user name.
 * Keep syntax punctuation out of this set; apostrophes are included because
 * binder names such as `x'` and `x''` occur in existing saves.
 */
function isNameChar(char: string | undefined): boolean {
    return !!char && /[\p{L}\p{N}_$@?#'!-]/u.test(char);
}

function isWhitespace(char: string | undefined): boolean {
    return !!char && /\s/u.test(char);
}

function skipWhitespace(source: string, index: number): number {
    let cursor = index;
    while (cursor < source.length && isWhitespace(source[cursor])) cursor++;
    return cursor;
}

function isProtectedWordAt(source: string, index: number): boolean {
    if (index > 0 && isNameChar(source[index - 1])) return false;
    let end = index;
    while (end < source.length && isNameChar(source[end])) end++;
    return end > index && PROTECTED_WORDS.has(source.slice(index, end));
}

/**
 * Return the replacement for a legacy binder marker at `index`, or null when
 * the character is an ordinary part of a user name.
 */
export type LegacySurfaceMigrationOptions = {
    /** Allow descriptive old binder names such as `Ppath` during save migration. */
    allowLongBinders?: boolean;
};

function binderAt(
    source: string,
    index: number,
    options: LegacySurfaceMigrationOptions
): string | null {
    const marker = source[index];
    const replacement = marker ? BINDER_SYMBOLS[marker] : undefined;
    if (!replacement) return null;

    // A marker embedded in a name (`myLambda`, `@List`, ...) is never syntax.
    if (index > 0 && (isNameChar(source[index - 1]) || source[index - 1] === "\\")) {
        return null;
    }
    if (isProtectedWordAt(source, index)) return null;

    // Legacy binders are Lx:T.body and L x : T,body.  The variable is one
    // tokenizer word; requiring it and the following colon avoids rewriting a
    // standalone variable `L` or a command/constant named `List`.
    let cursor = skipWhitespace(source, index + 1);
    const variableStart = cursor;
    while (cursor < source.length && isNameChar(source[cursor])) cursor++;
    if (cursor === variableStart) return null;
    // A long marker-prefixed token is ambiguous with a user identifier (for
    // example `Pfoo` or `SurfaceX`). Keep it opaque on the strict surface
    // boundary; old-save migration opts in when it must preserve legacy
    // binder compatibility.
    if (!options.allowLongBinders && cursor - variableStart > 1) return null;
    cursor = skipWhitespace(source, cursor);
    if (source[cursor] !== ":") return null;

    // A declaration such as `Pfoo : U` has the same prefix as a compact
    // legacy binder, but it has no binder body delimiter. Require the
    // delimiter accepted by the parser before treating the marker as syntax.
    cursor = skipWhitespace(source, cursor + 1);
    let paren = 0;
    let bracket = 0;
    let brace = 0;
    while (cursor < source.length) {
        const next = source[cursor];
        if (next === '"' || next === "`"
            || (next === "'" && (cursor === 0 || !isNameChar(source[cursor - 1])))) {
            cursor = findQuotedEnd(source, cursor, next);
            continue;
        }
        if (next === "/" && source[cursor + 1] === "/") {
            cursor = findCommentEnd(source, cursor);
            continue;
        }
        if (next === "/" && source[cursor + 1] === "*") {
            const endMarker = source.indexOf("*/", cursor + 2);
            cursor = endMarker < 0 ? source.length : endMarker + 2;
            continue;
        }
        if (next === "(") paren++;
        else if (next === ")") paren = Math.max(0, paren - 1);
        else if (next === "[") bracket++;
        else if (next === "]") bracket = Math.max(0, bracket - 1);
        else if (next === "{") brace++;
        else if (next === "}") brace = Math.max(0, brace - 1);
        else if (paren === 0 && bracket === 0 && brace === 0
            && ((marker === "L" && (next === "." || next === ","))
                || (marker !== "L" && (next === "," || next === ".")))) {
            return replacement;
        }
        cursor++;
    }

    return null;
}

function isTermEnd(char: string | undefined): boolean {
    if (!char) return false;
    return isNameChar(char) || /[\)\]\}0-9]/u.test(char)
        || char === "λ" || char === "Π" || char === "Σ" || char === "W"
        || char === "⊤" || char === "⊥";
}

function isTermStart(char: string | undefined): boolean {
    if (!char) return false;
    return isNameChar(char) || /[\(\[\{0-9]/u.test(char)
        || char === "λ" || char === "Π" || char === "Σ" || char === "W"
        || char === "@" || char === "?";
}

/**
 * Names which occur as operands of compact products in the legacy sources.
 *
 * `X` was historically both an operator and a valid identifier character,
 * so a string such as `fooXbar` is intrinsically ambiguous.  Save migration
 * chooses the conservative interpretation for arbitrary multi-character
 * names and keeps them intact; known built-in type names retain the old
 * compact product spelling used by shipped definitions and saves.
 */
const LEGACY_PRODUCT_ATOMS = new Set([
    "nat", "Bool", "True", "False", "Type", "Unit", "List", "Option",
    "Fin", "Even", "Z", "I", "S1", "S2", "S3", "S4", "Ord", "Aleph",
    "LiftU", "Pushout", "Wedge", "Sum", "Sus", "U", "X"
]);

function compactIdentifierAround(
    source: string,
    index: number,
    direction: -1 | 1
): string {
    let cursor = index + direction;
    // In a chain such as `aXbXc`, the neighboring X is the previous/next
    // compact operator, not part of the operand token being inspected.
    while (cursor >= 0 && cursor < source.length
        && source[cursor] !== "X"
        // `-` is legal in names, but `->` is the legacy arrow operator and
        // must terminate the right operand of a compact product.
        && !(direction === 1 && source[cursor] === "-" && source[cursor + 1] === ">")
        && isNameChar(source[cursor])) {
        cursor += direction;
    }
    const start = direction < 0 ? cursor + 1 : index + 1;
    const end = direction < 0 ? index : cursor;
    return source.slice(start, end);
}

function isKnownLegacyProductAtom(name: string): boolean {
    return LEGACY_PRODUCT_ATOMS.has(name);
}

/**
 * Decide whether an ASCII X is the old product operator.
 *
 * The legacy tokenizer lists X in symChar without an identifier escape.
 * Thus compact products such as aXb and natXnat are valid legacy syntax.
 * Declaration names and command names are protected by their outer helpers.
 */
function productAt(source: string, index: number): boolean {
    if (source[index] !== "X") return false;
    const immediateLeft = source[index - 1];
    const immediateRight = source[index + 1];

    // A compact legacy product can be written as `aX(b)`, but a generated or
    // user-defined identifier such as `SurfaceX` is commonly applied as
    // `SurfaceX(foo)`.  At this boundary the identifier interpretation is
    // unambiguous for multi-character names; retain one-letter compact
    // products such as `aX(b)` for old saves.
    if (isNameChar(immediateLeft) && immediateRight === "(") {
        const leftName = compactIdentifierAround(source, index, -1);
        if (leftName.length > 1 && !isKnownLegacyProductAtom(leftName)) return false;
    }

    // `X` is also a perfectly valid character in a user identifier.  The
    // legacy tokenizer only treated it as a product operator when it was a
    // token boundary (or embedded between two term characters).  In
    // particular, do not rewrite the trailing X in names such as
    // `SurfaceX` when that name is followed by an application/annotation
    // separated by whitespace; doing so makes generated sandbox HIT names
    // unusable after save migration.
    if (isNameChar(immediateLeft)
        && (!immediateRight || isWhitespace(immediateRight))) return false;
    if ((!immediateLeft || isWhitespace(immediateLeft))
        && isNameChar(immediateRight)) return false;

    let left = index - 1;
    while (left >= 0 && isWhitespace(source[left])) left--;
    let right = index + 1;
    while (right < source.length && isWhitespace(source[right])) right++;

    if (!isTermEnd(source[left]) || !isTermStart(source[right])) return false;

    // When both operands are contiguous identifier text, the same bytes can
    // also be a perfectly valid user identifier.  Keep arbitrary names such
    // as `fooXbar` and `myXname`; compact products made from one-letter
    // operands (aXb) and shipped names such as natXnat remain migratable.
    if (isNameChar(immediateLeft) && isNameChar(immediateRight)) {
        const leftName = compactIdentifierAround(source, index, -1);
        const rightName = compactIdentifierAround(source, index, 1);
        if ((leftName.length > 1 || rightName.length > 1)
            && !(isKnownLegacyProductAtom(leftName) && isKnownLegacyProductAtom(rightName))) {
            return false;
        }
    }
    return true;
}

function findQuotedEnd(source: string, start: number, quote: string): number {
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

function findCommentEnd(source: string, start: number): number {
    const newline = source.indexOf("\n", start + 2);
    return newline < 0 ? source.length : newline;
}

/**
 * The interactive editor accepts `\\*` as the keyboard spelling for the
 * composition/path operator `▪`.  Save migration may see that spelling when
 * a draft was persisted before the Space-triggered alias expansion ran.  A
 * preceding backslash escapes the slash, so only an odd-free (single) slash
 * is treated as the alias; quoted and commented text is handled by the caller
 * before reaching this helper.
 */
function isCompositionAliasAt(source: string, index: number): boolean {
    if (source[index] !== "\\" || source[index + 1] !== "*") return false;
    let slashCount = 0;
    for (let cursor = index - 1; cursor >= 0 && source[cursor] === "\\"; cursor--) {
        slashCount++;
    }
    return slashCount % 2 === 0;
}

/** Migrate one expression while preserving all original layout. */
export function migrateLegacySurfaceExpression(
    source: string,
    options: LegacySurfaceMigrationOptions = {}
): string {
    if (!source || typeof source !== "string") return source;
    // A draft can be persisted before the editor's Space handler expands a
    // backslash alias. Reuse the shared alias scanner so migration covers all
    // aliases (`\lambda`, `\p`, `\s`, `\x`, `\*`, ...), not just composition.
    source = expandTypeTheoryAliasesInSurface(source);
    let output = "";
    let cursor = 0;
    while (cursor < source.length) {
        const char = source[cursor];

        // Keep comments and quoted literals opaque.  A single quote is only
        // treated as a literal delimiter at a token boundary; apostrophes in
        // names such as x' remain ordinary name characters.
        if (char === '"' || char === "`"
            || (char === "'" && (cursor === 0 || !isNameChar(source[cursor - 1])))) {
            const end = findQuotedEnd(source, cursor, char);
            output += source.slice(cursor, end);
            cursor = end;
            continue;
        }
        if (char === "/" && source[cursor + 1] === "/") {
            const end = findCommentEnd(source, cursor);
            output += source.slice(cursor, end);
            cursor = end;
            continue;
        }
        if (char === "/" && source[cursor + 1] === "*") {
            const endMarker = source.indexOf("*/", cursor + 2);
            const end = endMarker < 0 ? source.length : endMarker + 2;
            output += source.slice(cursor, end);
            cursor = end;
            continue;
        }

        // `\\*` is the Lean-like keyboard alias for the Unicode composition
        // operator.  Consume both bytes so migration never leaves the invalid
        // intermediate spelling `\\▪` in a loaded draft.
        if (isCompositionAliasAt(source, cursor)) {
            output += "▪";
            cursor += 2;
            continue;
        }

        let operatorMatched = false;
        for (const [legacy, modern] of LEGACY_OPERATORS) {
            if (source.startsWith(legacy, cursor)) {
                output += modern;
                cursor += legacy.length;
                operatorMatched = true;
                break;
            }
        }
        if (operatorMatched) continue;

        const binder = binderAt(source, cursor, options);
        if (binder) {
            output += binder;
            cursor++;
            continue;
        }
        if (char === "X" && productAt(source, cursor)) {
            output += "×";
            cursor++;
            continue;
        }

        output += char;
        cursor++;
    }
    return output;
}

function topLevelDelimiter(source: string, delimiter: ":" | ":="): number {
    let paren = 0;
    let bracket = 0;
    let brace = 0;
    let cursor = 0;
    while (cursor < source.length) {
        const char = source[cursor];
        if (char === '"' || char === "`"
            || (char === "'" && (cursor === 0 || !isNameChar(source[cursor - 1])))) {
            cursor = findQuotedEnd(source, cursor, char);
            continue;
        }
        if (char === "/" && source[cursor + 1] === "/") {
            cursor = findCommentEnd(source, cursor);
            continue;
        }
        if (char === "/" && source[cursor + 1] === "*") {
            const endMarker = source.indexOf("*/", cursor + 2);
            cursor = endMarker < 0 ? source.length : endMarker + 2;
            continue;
        }
        if (char === "(") paren++;
        else if (char === ")") paren = Math.max(0, paren - 1);
        else if (char === "[") bracket++;
        else if (char === "]") bracket = Math.max(0, bracket - 1);
        else if (char === "{") brace++;
        else if (char === "}") brace = Math.max(0, brace - 1);
        if (paren === 0 && bracket === 0 && brace === 0) {
            if (delimiter === ":=" && char === ":" && source[cursor + 1] === "=") return cursor;
            if (delimiter === ":" && char === ":" && source[cursor + 1] !== "=") return cursor;
        }
        cursor++;
    }
    return -1;
}

/** Migrate a declaration while leaving its name and separator byte-for-byte. */
export function migrateLegacyDeclarationSource(source: string): string {
    if (!source || typeof source !== "string") return source;
    const assignment = topLevelDelimiter(source, ":=");
    if (assignment >= 0) {
        const rhsStart = assignment + 2;
        return source.slice(0, rhsStart) + migrateLegacySurfaceExpression(
            source.slice(rhsStart),
            { allowLongBinders: true }
        );
    }
    const typeDelimiter = topLevelDelimiter(source, ":");
    if (typeDelimiter >= 0) {
        const rhsStart = typeDelimiter + 1;
        return source.slice(0, rhsStart) + migrateLegacySurfaceExpression(
            source.slice(rhsStart),
            { allowLongBinders: true }
        );
    }
    return migrateLegacySurfaceExpression(source);
}

/** Migrate command arguments, preserving the command/strategy name itself. */
export function migrateLegacyProofCommand(command: string): string {
    if (!command || typeof command !== "string") return command;
    let cursor = 0;
    while (cursor < command.length && isWhitespace(command[cursor])) cursor++;
    const commandStart = cursor;
    if (cursor >= command.length) return command;

    // Command names are a single leading token.  Punctuation-prefixed rules
    // (`.Erp`, `:dE!`, `#nf`) are handled by the same boundary rule.
    while (cursor < command.length && !isWhitespace(command[cursor])) cursor++;
    if (cursor === commandStart) return command;
    return command.slice(0, cursor) + migrateLegacySurfaceExpression(
        command.slice(cursor),
        { allowLongBinders: true }
    );
}

export function migrateLegacyProofHistory(history: readonly string[]): string[] {
    if (!Array.isArray(history)) return [];
    return history.map(command => typeof command === "string"
        ? migrateLegacyProofCommand(command)
        : command as unknown as string);
}

export function migrateLegacyProofScript(script: string): string {
    if (!script || typeof script !== "string") return script;
    return script.split(/(\r?\n)/u).map(part => /^\r?\n$/u.test(part)
        ? part
        : migrateLegacyProofCommand(part)).join("");
}

/** True when the source contains a legacy construct that this module migrates. */
export function hasLegacySurfaceSyntax(source: string): boolean {
    return typeof source === "string" && migrateLegacySurfaceExpression(source) !== source;
}

export function hasModernSurfaceSyntax(source: string): boolean {
    return typeof source === "string" && /[λΠΣ×→≃▪≡]/u.test(source);
}
