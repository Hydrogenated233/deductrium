import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

const css = await readFile(new URL("../gui.css", import.meta.url), "utf8");
const gui = await readFile(new URL("../src/tt/gui.ts", import.meta.url), "utf8");
const html = await readFile(new URL("../index.html", import.meta.url), "utf8");

for (const selector of [".inhabitat-div", "#tactic-hint", "#tactic-state", "#tactic-list"]) {
    assert.match(css, new RegExp(`${selector.replace(/[.#]/g, "\\$&")}[^}]*overflow-wrap\\s*:\\s*anywhere`),
        `${selector} must allow long generated proof terms to wrap`);
    assert.match(css, new RegExp(`${selector.replace(/[.#]/g, "\\$&")}[^}]*white-space\\s*:\\s*normal`),
        `${selector} must use normal whitespace layout`);
}

assert.match(gui, /document\.createElement\("textarea"\)/,
    "theorem editors must use a wrapping control rather than a single-line input");
assert.match(gui, /input\.addEventListener\("input", \(\) => \{\s*resizeTheoremInput\(\)/,
    "theorem editors must resize while the user edits a long proof term");
assert.match(gui, /for \(let pass = 0; pass < 3; pass\+\+\) \{[\s\S]*?textarea\.clientHeight >= nextHeight[\s\S]*?nextHeight \+ borderHeight/,
    "theorem editor resizing must settle after a list scrollbar narrows the wrapping area");
assert.match(gui, /output\.dispatchEvent\(new Event\("input"\)\)/,
    "qed must run the theorem editor's normal resize path after inserting the generated proof term");
assert.match(gui, /\? `\$\{qedName\}:=\$\{result\.proof\}:\$\{result\.theorem\}`/,
    "named qed output must keep the name:=proof:theorem format");
assert.match(gui, /if \(ev\.key === "Enter" \|\| ev\.key === "Escape"\) \{\s*ev\.preventDefault\(\);\s*input\.blur\(\)/,
    "wrapping editors must preserve the original Enter/Escape submit behavior without inserting a newline");
assert.match(gui, /theorem\.input\.value = String\(item\.value \?\? ""\)/,
    "save restore must put long proof terms back into the wrapping theorem editor");
assert.match(gui, /input\.addEventListener\("focus", \(\) => \{[\s\S]*?resizeTheoremInput\(\)/,
    "a restored long proof term must resize when the user opens it for editing");
assert.match(html, /<textarea id="tactic-input"[^>]*rows="1"/,
    "the active proof command must use a selectable wrapping textarea");
assert.doesNotMatch(html, /class="[^"]*list-wrapper[^"]*tactic-assist-wrapper[^"]*"/,
    "proof-assistant controls must not add the black list-wrapper frame");
assert.match(css, /#tactic-state \.blocked\s*\{[^}]*white-space:\s*pre-wrap[^}]*overflow-wrap:\s*anywhere/,
    "historical proof commands must wrap while preserving their command text");
assert.match(gui, /input\.addEventListener\("input", \(\) => this\.resizeTacticInput\(\)\)/,
    "the active proof command must resize as it is typed");
assert.match(gui, /input\.addEventListener\("keydown", \(ev\) => \{[\s\S]*?ev\.preventDefault\(\);[\s\S]*?getElementById\("tactic-begin"\)\.click\(\)/,
    "textarea input must keep Enter/Escape command submission without inserting a newline");
assert.match(gui, /this\.addSpan\(statediv, command\)\.className = "blocked"/,
    "a selected history line must contain the exact replayable command");
assert.doesNotMatch(gui, /command \+ " \. "/,
    "display-only tactic separators must not be copied into the command");

console.log("proof-term wrapping stylesheet regression passed");
