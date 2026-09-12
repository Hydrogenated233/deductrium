import assert from "node:assert/strict";
import { COMMON_SYMBOL_ALIASES } from "../js/symbol-aliases.js";
import {
    INFERENCE_SYMBOL_ALIASES, inferenceSymbolForAlias,
    expandInferenceAliasesInSurface, expandInferenceAliasAtCaret
} from "../js/fs/symbol-aliases.js";
import {
    TYPE_THEORY_SYMBOL_ALIASES, typeTheorySymbolForAlias,
    expandTypeTheoryAliasesInSurface, expandTypeTheoryAliasAtCaret
} from "../js/tt/symbol-aliases.js";
import {
    SYMBOL_ALIAS_HELP_GROUPS, groupSymbolAliases, renderSymbolAliases
} from "../js/symbol-alias-help.js";
import { ASTParser as FSParser } from "../js/fs/astparser.js";
import { ASTParser as TTParser } from "../js/tt/astparser.js";
import { FSCmd } from "../js/fs/cmd.js";

for (const [aliases, resolve, expand, caret] of [
    [INFERENCE_SYMBOL_ALIASES, inferenceSymbolForAlias, expandInferenceAliasesInSurface, expandInferenceAliasAtCaret],
    [TYPE_THEORY_SYMBOL_ALIASES, typeTheorySymbolForAlias, expandTypeTheoryAliasesInSurface, expandTypeTheoryAliasAtCaret]
]) {
    assert.equal(new Set(aliases.map(({ alias }) => alias.toLowerCase())).size, aliases.length);
    for (const { alias, symbol } of aliases) {
        const source = `\\${alias}`;
        assert.equal(resolve(source), symbol);
        assert.equal(resolve(source.toUpperCase()), symbol);
        assert.equal(expand(source), symbol, `pasted ${source}`);
        assert.deepEqual(caret(source, source.length), { value: symbol, caret: symbol.length, symbol });
        assert.equal(expand(`"${source}" \`${source}\` \\${source}`), `"${source}" \`${source}\` \\${source}`);
        assert.equal(caret(source, source.length, 0), null);
        assert.equal(caret(`\\${source}`, source.length + 1), null);
        if (alias !== "*") assert.equal(expand(`${source}_tail`), `${source}_tail`);
    }
}
for (const { alias, symbol } of COMMON_SYMBOL_ALIASES) {
    assert.equal(inferenceSymbolForAlias(alias), symbol);
    assert.equal(typeTheorySymbolForAlias(alias), symbol);
}
for (const { alias, symbol } of INFERENCE_SYMBOL_ALIASES) {
    const tt = typeTheorySymbolForAlias(alias);
    if (tt !== null) assert.equal(tt, symbol, `shared spelling ${alias}`);
}
for (const alias of ["and", "or", "not", "setminus", "forall", "exists", "in", "cup", "cap", "nat"]) {
    assert.equal(typeTheorySymbolForAlias(alias), null, `${alias} is inference-only`);
    assert.equal(expandTypeTheoryAliasesInSurface(`\\${alias}`), `\\${alias}`);
}
for (const alias of ["lambda", "pi", "sigma", "equiv", "defeq", "comp"]) {
    assert.equal(inferenceSymbolForAlias(alias), null, `${alias} is type-theory-only`);
}
for (const text of ["Q\\and", "α\\and", "$\\alpha", "Q\\a", "\\unknown"]) {
    assert.equal(expandInferenceAliasesInSurface(text), text, "legacy differences stay literal");
}
for (const text of ["Q\\a", "\\unknown"]) {
    assert.equal(expandInferenceAliasAtCaret(text, text.length), null);
}
for (const [text, expected] of [["Q\\and", "Q∧"], ["α\\and", "α∧"], ["$\\alpha", "$α"]]) {
    assert.equal(expandInferenceAliasAtCaret(text, text.length)?.value, expected);
}
assert.equal(typeTheorySymbolForAlias("l"), "λ");
assert.equal(typeTheorySymbolForAlias("pi"), "Π");
assert.equal(typeTheorySymbolForAlias("sigma"), "Σ");
assert.equal(typeTheorySymbolForAlias("*"), "▪");
assert.equal(inferenceSymbolForAlias("setminus"), "∖");
assert.equal(inferenceSymbolForAlias("smallsetminus"), "∖");
assert.equal(typeTheorySymbolForAlias("la"), "λ");
assert.equal(typeTheorySymbolForAlias("equiv"), "≃");
assert.equal(inferenceSymbolForAlias("all"), "∀");
assert.equal(inferenceSymbolForAlias("leq"), "≤");
assert.equal(expandInferenceAliasesInSurface("-- \\all\n\\all"), "-- \\all\n∀");
assert.equal(expandTypeTheoryAliasesInSurface("/* \\la */ \\la"), "/* \\la */ λ");

const fsParser = new FSParser();
assert.equal(fsParser.stringifyTight(fsParser.parse(
    expandInferenceAliasesInSurface("\\alpha \\rightarrow \\beta")
)), "α→β");
assert.equal(fsParser.stringifyTight(fsParser.parse(
    expandInferenceAliasesInSurface("Q \\smallsetminus a")
)), "Q∖a");
const ttParser = new TTParser();
assert.deepEqual(
    ttParser.parseSurface("\\la \\alpha:U.\\alpha"),
    ttParser.parseSurface("λ α:U.α")
);
assert.deepEqual(
    ttParser.parseSurface("A \\equiv B"),
    ttParser.parseSurface("A ≃ B")
);
assert.equal(expandTypeTheoryAliasesInSurface("rcases h with \\langle a, b \\rangle"), "rcases h with ⟨ a, b ⟩");
assert.equal(expandInferenceAliasesInSurface("rcases h with \\langle a, b \\rangle"), "rcases h with ⟨ a, b ⟩");

// Exercise the renderer itself so list completeness cannot drift from editor data.
class Element {
    children = [];
    textContent = "";
    classList = { add() {} };
    constructor(tag) { this.tag = tag; }
    appendChild(child) { this.children.push(child); return child; }
    replaceChildren() { this.children = []; }
    createCaption() { return this.appendChild(new Element("caption")); }
    createTHead() { return this.appendChild(new Element("thead")); }
    createTBody() { return this.appendChild(new Element("tbody")); }
    insertRow() { return this.appendChild(new Element("tr")); }
    insertCell() { return this.appendChild(new Element("td")); }
    find(tag) {
        return this.children.flatMap(child => [
            ...(child.tag === tag ? [child] : []), ...child.find(tag)
        ]);
    }
}
const oldDocument = globalThis.document;
try {
    globalThis.document = {
        createElement: tag => new Element(tag),
        getElementById(id) {
            assert.equal(id, "autocomplete-list");
            return { style: { display: "none" }, querySelectorAll() { return []; } };
        }
    };
    const root = new Element("div");
    renderSymbolAliases(null);
    renderSymbolAliases(root);
    renderSymbolAliases(root);
    assert.equal(root.children.length, 2, "re-render must not duplicate tables");
    for (const [i, { title, aliases }] of SYMBOL_ALIAS_HELP_GROUPS.entries()) {
        const table = root.find("table")[i];
        assert.equal(table.find("caption")[0].textContent, title);
        assert.deepEqual(table.find("code").map(e => e.textContent).sort(),
            aliases.map(({ alias }) => `\\${alias}`).sort());
        assert.equal(table.find("tbody")[0].children.length, groupSymbolAliases(aliases).size);
    }
    for (const [source, expected] of [
        ["Q \\smallsetminus a", "Q ∖ a"],
        ["\\alpha \\rightarrow \\beta", "α → β"],
        ["α\\and", "α\\and"]
    ]) {
        const command = Object.create(FSCmd.prototype);
        Object.assign(command, {
            gui: { actionInput: { value: source } },
            cmdBuffer: [],
            expansionBusy: false,
            autoCompleteIdx: -1,
            showhints() {},
            execCmdBuffer() {}
        });
        // The footer's OK button takes this same path without a keyboard event.
        command.actionInputKeydown({ key: "Enter" });
        assert.deepEqual(command.cmdBuffer, [expected]);
        assert.equal(command.gui.actionInput.value, "");
    }
} finally {
    if (oldDocument === undefined) delete globalThis.document;
    else globalThis.document = oldDocument;
}
console.log("layer-scoped symbol alias synchronization and complete help regression passed");
