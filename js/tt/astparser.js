import { TR } from "../lang.js";
import { hasLegacySurfaceSyntax, migrateLegacySurfaceExpression } from "./surface-syntax-migration.js";
import { expandTypeTheoryAliasesInSurface } from "./symbol-aliases.js";
/**
 * Characters which separate surface identifiers from the parser's compact
 * token representation.  The legacy parser has to keep `L/P/S/W/X` in its
 * symbol table, so the strict surface entry point protects identifiers before
 * delegating to it (see `parseSurface`).
 */
const SURFACE_DELIMITERS = new Set([
    ".", ":", ",", "(", ")", "[", "]", "{", "}", "~", "*", "+", "=",
    "λ", "Π", "Σ", "→", "≃", "≡", "▪", "×"
]);
function isSurfaceDelimiter(char) {
    return !char || /\s/u.test(char) || SURFACE_DELIMITERS.has(char);
}
function previousSurfaceChar(source, index) {
    let cursor = index - 1;
    while (cursor >= 0 && /\s/u.test(source[cursor]))
        cursor--;
    return cursor >= 0 ? source[cursor] : undefined;
}
function skipSurfaceWhitespace(source, index) {
    let cursor = index;
    while (cursor < source.length && /\s/u.test(source[cursor]))
        cursor++;
    return cursor;
}
/**
 * The compact parser accepts `U0`, `U1`, ... and `U@0`, `U@1`, ... as
 * universe shorthand.  Other identifiers beginning with `U` must be shielded
 * before delegating to that parser; otherwise a user name such as `Ufoo` is
 * silently parsed as the application `U foo`.
 */
function isSurfaceUniverseToken(token) {
    return token === "U" || token === "U@" || token === "U@:"
        // Internal/generated source also uses one-letter symbolic levels such
        // as `Uu`, `Uv`, and `Uw`.  Keep those compatible while treating
        // longer names (`Ufoo`) as ordinary user identifiers.
        || /^U(?:[0-9]+|@[0-9]+|[a-z])$/u.test(token);
}
/**
 * `W` is the one ASCII binder which has no Unicode spelling in the current
 * language.  Keep it as syntax only when it is visibly followed by a binder
 * name and a type separator; otherwise it is protected as an identifier.
 */
function isSurfaceWBinder(source, start, end) {
    if (source.slice(start, end) !== "W")
        return false;
    // A W immediately following a Unicode binder is its variable name, not a
    // nested W binder (`λW:U.W`).
    const previous = previousSurfaceChar(source, start);
    if (previous === "λ" || previous === "Π" || previous === "Σ")
        return false;
    let cursor = skipSurfaceWhitespace(source, end);
    const nameStart = cursor;
    while (cursor < source.length && !isSurfaceDelimiter(source[cursor]))
        cursor++;
    if (cursor === nameStart)
        return false;
    cursor = skipSurfaceWhitespace(source, cursor);
    return source[cursor] === ":";
}
function shieldSurfaceIdentifiers(source) {
    const placeholders = new Map();
    const used = new Set();
    let output = "";
    let cursor = 0;
    let placeholderId = 0;
    // Avoid collisions even when a user deliberately chose our internal
    // placeholder-looking spelling as an identifier.
    for (let i = 0; i < source.length;) {
        if (isSurfaceDelimiter(source[i])) {
            i++;
            continue;
        }
        const start = i;
        while (i < source.length && !isSurfaceDelimiter(source[i]))
            i++;
        used.add(source.slice(start, i));
    }
    cursor = 0;
    while (cursor < source.length) {
        const char = source[cursor];
        // Keep quoted/commented text opaque.  The regular TT parser does not
        // assign special meaning to these spans, but preserving them here
        // prevents a reserved letter inside a diagnostic string from being
        // rewritten before the parser gets a chance to report its own error.
        if (char === '"' || char === "`"
            || (char === "'" && (cursor === 0 || !/[\p{L}\p{N}_$@?#'!-]/u.test(source[cursor - 1])))) {
            const quote = char;
            let end = cursor + 1;
            while (end < source.length) {
                if (source[end] === "\\") {
                    end += 2;
                    continue;
                }
                if (source[end] === quote) {
                    end++;
                    break;
                }
                end++;
            }
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
        if (isSurfaceDelimiter(char)) {
            output += char;
            cursor++;
            continue;
        }
        const start = cursor;
        while (cursor < source.length && !isSurfaceDelimiter(source[cursor]))
            cursor++;
        const token = source.slice(start, cursor);
        // U-prefixed tokens are the parser's universe shorthand (U, U0,
        // U@..., ...); changing them into ordinary variables would alter the
        // AST rather than merely protecting a spelling.
        const keep = isSurfaceUniverseToken(token)
            || (!token.startsWith("U") && !/[LPSXW]/u.test(token))
            || (token === "W" && isSurfaceWBinder(source, start, cursor));
        if (keep) {
            output += token;
            continue;
        }
        let placeholder;
        do {
            placeholder = `__surface_id_${placeholderId++}`;
        } while (used.has(placeholder) || placeholders.has(placeholder));
        placeholders.set(placeholder, token);
        output += placeholder;
    }
    return { source: output, placeholders };
}
function restoreSurfaceIdentifiers(ast, placeholders, seen = new Set()) {
    if (!ast || seen.has(ast))
        return;
    seen.add(ast);
    const replacement = placeholders.get(ast.name);
    if (replacement !== undefined)
        ast.name = replacement;
    ast.nodes?.forEach(node => restoreSurfaceIdentifiers(node, placeholders, seen));
    if (ast.checked && typeof ast.checked === "object") {
        restoreSurfaceIdentifiers(ast.checked, placeholders, seen);
    }
    if (ast.origin && typeof ast.origin === "object") {
        restoreSurfaceIdentifiers(ast.origin, placeholders, seen);
    }
}
export const debugBoundVarId = false;
export class ASTParser {
    keywords = [":=", "[[", "]]", "->", "~=", "==="];
    specialwords = ["Sum", "S1", "S2", "S3", "S4", "LiftU", "South", "Sus", "List", "LEM", "Pushout", "Wedge"];
    // keywords = [":=", "[[", "]]", "[", "]", "->", "~=", "===", "=", "@ind_Sum", "ind_Sum", "@Sum", "Sum", "@rec_S1", "rec_S1", "@ind_S1", "ind_S1", "S1", "@ind_Prod", "ind_Prod", "@Prod", "Prod", "@ind_LiftU", "ind_LiftU", "@LiftU", "LiftU", "@South", "@ind_Sus", "ind_Sus", "@Sus", "South", "Sus"];
    symChar = ".:,()PWSLX~*+=[]";
    ast;
    cursor = 0;
    tokens;
    token;
    stringify(ast, omitParenthese) {
        if (!ast)
            return TR('表达式丢失');
        const nd = ast.nodes;
        if (ast.type === "[]") {
            return `[${this.stringify(nd[0])}]`;
        }
        if (ast.type === "[[]]") {
            return `[[${this.stringify(nd[0])}]]`;
        }
        if (ast.type === "->") {
            return `(${this.stringify(nd[0])}→${this.stringify(nd[1])})`;
        }
        if (ast.type === "===") {
            return `(${this.stringify(nd[0])} ≡ ${this.stringify(nd[1])})`;
        }
        if (ast.type === "=") {
            return `(${this.stringify(nd[0])}=${this.stringify(nd[1])})`;
        }
        if (ast.type === ":") {
            return `(${this.stringify(nd[0])} : ${this.stringify(nd[1])})`;
        }
        if (ast.type === ":=") {
            return `(${this.stringify(nd[0])} := ${this.stringify(nd[1])})`;
        }
        if (ast.type === "~") {
            return `(${this.stringify(nd[0])}~${this.stringify(nd[1])})`;
        }
        if (ast.type === "*") {
            return `(${this.stringify(nd[0])}▪${this.stringify(nd[1])})`;
        }
        if (ast.type === ",") {
            return `(${this.stringify(nd[0])},${this.stringify(nd[1])})`;
        }
        if (ast.type === "+") {
            return `(${this.stringify(nd[0])}+${this.stringify(nd[1])})`;
        }
        if (ast.type === "~=") {
            return `(${this.stringify(nd[0])}≃${this.stringify(nd[1])})`;
        }
        if (ast.type === "X") {
            return `(${this.stringify(nd[0])}×${this.stringify(nd[1])})`;
        }
        if (ast.type === "L") {
            let s = "";
            if (debugBoundVarId && ast.bondVarId)
                s = "{" + ast.bondVarId + "}";
            return `(λ${ast.name + s}:${this.stringify(nd[0], true)}.${this.stringify(nd[1], true)})`;
        }
        if (ast.type === "P") {
            let s = "";
            if (debugBoundVarId && ast.bondVarId)
                s = "{" + ast.bondVarId + "}";
            return `(Π${ast.name + s}:${this.stringify(nd[0], true)},${this.stringify(nd[1], true)})`;
        }
        if (ast.type === "W") {
            let s = "";
            if (debugBoundVarId && ast.bondVarId)
                s = "{" + ast.bondVarId + "}";
            return `(W${ast.name + s}:${this.stringify(nd[0], true)},${this.stringify(nd[1], true)})`;
        }
        if (ast.type === "S") {
            let s = "";
            if (debugBoundVarId && ast.bondVarId)
                s = "{" + ast.bondVarId + "}";
            return `(Σ${ast.name + s}:${this.stringify(nd[0], true)},${this.stringify(nd[1], true)})`;
        }
        if (ast.type === "var") {
            let s = "";
            if (debugBoundVarId && ast.bondVarId)
                s = "{" + ast.bondVarId + "}";
            return ast.name + s;
        }
        if (ast.type === "apply") {
            if (ast.nodes[0].name === "U" && ast.nodes[1].name === "@0")
                return `U`;
            if (ast.nodes[0].name === "U")
                return `(${this.stringify(nd[0])}${this.stringify(nd[1])})`;
            if (omitParenthese)
                return `${this.stringify(nd[0], omitParenthese)} ${this.stringify(nd[1])}`;
            return `(${this.stringify(nd[0], true)} ${this.stringify(nd[1])})`;
        }
    }
    parse(s) {
        this.cursor = 0;
        this.tokenise(s.replaceAll("Σ", " S ").replaceAll("λ", " L ").replaceAll("Π", " P ").replaceAll("≃", "~=").replaceAll("▪", "*").replaceAll("≡", "===").replaceAll("→", "->").replaceAll("×", "X"));
        this.nextSym();
        const ret = this.type();
        if (this.tokens.length !== this.cursor - 1) {
            if (this.token === ":" || this.token === "===" || this.token === ":=") {
                const token = this.token;
                this.nextSym();
                const postfix = this.type();
                if (!postfix)
                    throw TR("不完整的表达式");
                if (this.tokens.length !== this.cursor - 1) {
                    if (token === ":=" && this.token === ":") {
                        // def := expr : type
                        this.nextSym();
                        const type = this.type();
                        if (!type)
                            throw TR("不完整的表达式");
                        return {
                            type: token, name: "", nodes: [ret, {
                                    type: ":", name: "", nodes: [postfix, type]
                                }]
                        };
                    }
                    throw TR("未知的语法错误");
                }
                return { type: token, name: "", nodes: [ret, postfix] };
            }
            else {
                throw TR("未知的语法错误");
            }
        }
        return ret;
    }
    /**
     * Parse the user-facing Unicode surface syntax.
     *
     * `parse()` remains intentionally backwards-compatible for internal
     * rules, fixtures, and one-shot save migration.  New editor/load paths
     * should call this method: valid legacy ASCII operators/binders are
     * rejected, while names containing the legacy marker letters are shielded
     * from the compact tokenizer and restored on the resulting AST.
     */
    parseSurface(source) {
        const normalized = expandTypeTheoryAliasesInSurface(source);
        if (hasLegacySurfaceSyntax(normalized)) {
            throw TR("不再支持旧语法，请使用 Unicode 符号");
        }
        const shielded = shieldSurfaceIdentifiers(normalized);
        const ast = this.parse(shielded.source);
        restoreSurfaceIdentifiers(ast, shielded.placeholders);
        return ast;
    }
    /**
     * Parse an interactive/user expression while retaining old-history
     * compatibility. New Unicode input goes through the strict surface path;
     * legacy ASCII is migrated once and then parsed through that same path.
     * The final compatibility fallback is intentionally kept for internal
     * replay strings that are not surface expressions.
     */
    parseSurfaceOrLegacy(source) {
        const normalized = expandTypeTheoryAliasesInSurface(String(source ?? ""));
        try {
            return this.parseSurface(normalized);
        }
        catch (surfaceError) {
            const migrated = migrateLegacySurfaceExpression(normalized, {
                allowLongBinders: true
            });
            if (migrated !== normalized) {
                try {
                    return this.parseSurface(migrated);
                }
                catch { }
            }
            try {
                return this.parse(normalized);
            }
            catch {
                throw surfaceError;
            }
        }
    }
    tokenise(s) {
        for (let i = 0; i < this.keywords.length; i++) {
            s = s.replaceAll(this.keywords[i], " #keyword" + i + " ");
        }
        for (let i = 0; i < this.specialwords.length; i++) {
            s = s.replaceAll(this.specialwords[i], "#specialword" + this.specialwords[i]);
        }
        let word = "";
        const arr = [];
        for (let i = 0; i < s.length; i++) {
            const c = s[i];
            if (this.symChar.includes(c)) {
                if ((c === "P" || c === "L" || c === "S" || c === "W")) {
                    const lastword = word[word.length - 1];
                    if (lastword && !this.symChar.includes(lastword)) {
                        word += c;
                        continue;
                    }
                }
                if (word !== "") {
                    arr.push(word);
                    word = "";
                }
                arr.push(c);
                continue;
            }
            if (c === " ") {
                if (word !== "") {
                    arr.push(word);
                    word = "";
                }
                continue;
            }
            word += c;
        }
        if (word !== "") {
            arr.push(word);
        }
        this.tokens = arr.map(token => token.startsWith("#keyword") ? this.keywords[token.slice(8)] : token.replace("：", ":").replaceAll("#specialword", ""));
    }
    prevToken(index) {
        return this.tokens[this.cursor - index - 1];
    }
    nextSym() {
        this.token = this.tokens[this.cursor++];
    }
    moveCursor(cursor) {
        this.cursor = cursor;
        this.token = this.tokens[this.cursor - 1];
    }
    typeTerm3() {
        let val;
        if (this.acceptSym("[[")) {
            val = { type: "[[]]", nodes: [this.type()], name: "" };
            if (this.tokens[this.cursor - 1] !== "]]") {
                if (!this.acceptSym("]"))
                    throw TR("语法错误：未找到符号“]]”");
                if (this.tokens[this.cursor - 1] === "]]")
                    this.token = this.tokens[this.cursor - 1] = "]";
                else if (!this.acceptSym("]"))
                    throw TR("语法错误：未找到符号“]]”");
            }
            else
                this.nextSym();
        }
        else if (this.acceptSym("[")) {
            val = { type: "[]", nodes: [this.type()], name: "" };
            if (this.tokens[this.cursor - 1] === "]")
                this.nextSym();
            else if (this.tokens[this.cursor - 1] === "]]")
                this.token = this.tokens[this.cursor - 1] = "]";
        }
        else if (this.acceptSym("(")) {
            val = this.type();
            if (val.type === "var" && this.acceptSym(":")) {
                const t = this.type();
                this.expectSym(")");
                this.expectSym("->");
                val = { type: "P", name: val.name, nodes: [t, this.type()] };
            }
            else {
                while (this.token === ",") {
                    this.nextSym();
                    val = {
                        type: ",", name: "", nodes: [
                            val, this.type()
                        ]
                    };
                }
                this.expectSym(")");
            }
        }
        else if (this.acceptSym("L")) {
            this.expectVar();
            const param = this.prevToken(1);
            this.expectSym(":");
            const paramType = this.type();
            if (!(this.acceptSym(".") || this.acceptSym(",")))
                throw TR("λ(L)未匹配“.”号");
            const fnbody = this.type();
            val = { type: "L", name: param, nodes: [paramType, fnbody] };
        }
        else if (this.acceptSym("P")) {
            this.expectVar();
            const param = this.prevToken(1);
            this.expectSym(":");
            const paramType = this.type();
            if (!(this.acceptSym(".") || this.acceptSym(",")))
                throw TR("Π(P)未匹配“,”号");
            const fnbody = this.type();
            val = { type: "P", name: param, nodes: [paramType, fnbody] };
        }
        else if (this.acceptSym("S")) {
            this.expectVar();
            const param = this.prevToken(1);
            this.expectSym(":");
            const paramType = this.type();
            if (!(this.acceptSym(".") || this.acceptSym(",")))
                throw TR("Σ(S)未匹配“,”号");
            const fnbody = this.type();
            val = { type: "S", name: param, nodes: [paramType, fnbody] };
        }
        else if (this.acceptSym("W")) {
            this.expectVar();
            const param = this.prevToken(1);
            this.expectSym(":");
            const paramType = this.type();
            if (!(this.acceptSym(".") || this.acceptSym(",")))
                throw TR("W未匹配“,”号");
            const fnbody = this.type();
            val = { type: "W", name: param, nodes: [paramType, fnbody] };
        }
        else if (this.acceptVar()) {
            const name = this.prevToken(1);
            const isapply = this.prevToken(0);
            if (name === "U" && isapply !== "(") {
                val = {
                    type: "apply", name: "", nodes: [
                        { type: "var", name: "U" }, { type: "var", name: "@0" }
                    ]
                };
            }
            else if (name.startsWith("U") && name !== "U@" && isapply !== "(") {
                val = {
                    type: "apply", name: "", nodes: [
                        { type: "var", name: "U" },
                        { type: "var", name: ("0123456789".includes(name[1]) ? "@" : "") + name.slice(1) }
                    ]
                };
            }
            else {
                val = { type: "var", name: this.prevToken(1) };
            }
        }
        else {
            throw TR("表达式不完整");
        }
        return val;
    }
    typeTerm2() {
        let val = this.typeTerm();
        while (this.token === "*") {
            const token = this.token;
            this.nextSym();
            val = { type: token, name: "", nodes: [val, this.typeTerm()] };
        }
        return val;
    }
    typeTerm1() {
        let val = this.typeTerm2();
        while (this.token === "~" || this.token === "~=" || this.token === "=") {
            const token = this.token;
            this.nextSym();
            val = { type: token, name: "", nodes: [val, this.typeTerm2()] };
        }
        return val;
    }
    typeTerm0half() {
        let val = this.typeTerm1();
        while (this.token === "X") {
            const token = this.token;
            this.nextSym();
            val = { type: token, name: "", nodes: [val, this.typeTerm1()] };
        }
        return val;
    }
    typeTerm0() {
        let val = this.typeTerm0half();
        while (this.token === "+") {
            const token = this.token;
            this.nextSym();
            val = { type: token, name: "", nodes: [val, this.typeTerm0half()] };
        }
        return val;
    }
    type() {
        const arr = [this.typeTerm0()];
        while (this.token === "->") {
            this.nextSym();
            arr.push(this.typeTerm0());
        }
        let val = arr.pop();
        let val1;
        while (val1 = arr.pop()) {
            val = { type: "->", name: "", nodes: [val1, val] };
        }
        return val;
    }
    typeTerm() {
        let val = this.typeTerm3();
        while (this.token && this.token !== "]]" && this.token !== "]" && this.token !== ")" && this.token !== ":" && this.token !== "." && this.token !== "," && this.token !== ":=" && this.token !== "===" && this.token !== "=" && this.token !== "~=" && this.token !== "X" && this.token !== "*" && this.token !== "->" && this.token !== "+") {
            val = { type: "apply", name: "", nodes: [val, this.typeTerm3()] };
        }
        if (!val)
            throw TR("表达式不完整");
        return val;
    }
    acceptVar() {
        if (!this.symChar.includes(this.token) || this.token.length > 1) {
            if (!this.token)
                return false; //eof
            this.nextSym();
            return true;
        }
        return false;
    }
    expectVar() {
        if (this.acceptVar())
            return true;
        throw TR(`语法错误：未找到变量`);
    }
    acceptSym(s) {
        if (s === this.token) {
            this.nextSym();
            return true;
        }
        return false;
    }
    expectSym(s) {
        if (this.acceptSym(s))
            return true;
        throw TR(`语法错误：未找到符号"`) + s + `"`;
    }
}
//# sourceMappingURL=astparser.js.map