import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

const html = await readFile(new URL("../index.html", import.meta.url), "utf8");
const css = await readFile(new URL("../gui.css", import.meta.url), "utf8");
const ttGui = await readFile(new URL("../src/tt/gui.ts", import.meta.url), "utf8");
const fsGui = await readFile(new URL("../src/fs/gui.ts", import.meta.url), "utf8");
const renderer = await readFile(new URL("../src/proof-state.ts", import.meta.url), "utf8");

assert.match(html, /id="tactic-state" class="proof-assistant-state"/);
for (const source of [ttGui, fsGui]) {
    assert.match(source, /import \{ clearProofState, renderProofState \} from "\.\.\/proof-state\.js"/);
    assert.match(source, /renderProofState\(/);
    assert.doesNotMatch(source, /--proof-goal-depth/,
        "goal queue positions are not proof-tree depth");
}
assert.match(renderer, /document\.createElement\("details"\)/);
assert.match(renderer, /document\.createElement\("summary"\)/);
assert.match(renderer, /"proof-goal-current" : "proof-goal-secondary"/);
assert.match(renderer, /options\.goals\.forEach/,
    "render goals in engine order, current goal first");
const secondaryRule = css.match(/\.proof-goal-secondary\s*\{([^}]*)\}/);
assert.ok(secondaryRule, "all modes share one secondary goal style");
assert.match(secondaryRule[1], /background:\s*transparent/);
assert.match(secondaryRule[1], /border-left:\s*0/);
assert.match(secondaryRule[1], /margin-left:\s*0/);
assert.match(css, /\.proof-goals:has\(\.proof-goal-emphasized\) \.proof-goal-secondary\s*\{[^}]*opacity:\s*0\.65/);
assert.doesNotMatch(secondaryRule[1], /display:\s*none|visibility:\s*hidden/,
    "secondary goals remain visible unless explicitly collapsed");

console.log("shared Lean-style secondary proof-goal styling regression passed");
