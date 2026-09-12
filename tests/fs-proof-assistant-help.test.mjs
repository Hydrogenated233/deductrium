import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

const html = await readFile(new URL("../index.html", import.meta.url), "utf8");
const css = await readFile(new URL("../gui.css", import.meta.url), "utf8");

const inferenceHelp = html.match(/<details id="fs-proof-help"[\s\S]*?<\/details>/);
assert.ok(inferenceHelp, "the inference proof assistant must expose collapsible help");
assert.match(inferenceHelp[0], /<summary>策略介绍<\/summary>/);
assert.doesNotMatch(inferenceHelp[0], /<details[^>]*\bopen(?:\s|=|>)/,
    "inference help should start collapsed");
for (const tactic of ["intro", "intros", "exact", "apply", "use", "assumption", "constructor", "left", "right", "symm", "rfl", "rw", "nth_rw", "simp", "contradiction", "by_contra", "by_cases", "contrapose", "have", "obtain", "revert", "qed"]) {
    assert.match(inferenceHelp[0], new RegExp(`<code>${tactic}(?:</code>|\\s)`),
        `inference help should describe ${tactic}`);
}
assert.match(inferenceHelp[0], /apply &gt;rule/,
    "inference help should describe deduction-metatheorem rule names");
assert.match(inferenceHelp[0], /底层规则仍须在当前作用域可用/,
    "inference help should describe generated-rule scope checks");

const inferenceAssistantStart = html.indexOf('<div id="fs-proof-assistant"');
const inferenceTextModeStart = html.indexOf('<div id="fs-proof-text-mode"', inferenceAssistantStart);
const inferenceHelpStart = html.indexOf('<details id="fs-proof-help"', inferenceAssistantStart);
assert.ok(inferenceAssistantStart >= 0 && inferenceTextModeStart > inferenceAssistantStart && inferenceHelpStart > inferenceTextModeStart,
    "inference assistant help and text mode must be present in the assistant container");
const beforeInferenceHelp = html.slice(inferenceTextModeStart, inferenceHelpStart);
const openedDivs = (beforeInferenceHelp.match(/<div\b/g) || []).length;
const closedDivs = (beforeInferenceHelp.match(/<\/div>/g) || []).length;
assert.equal(openedDivs, closedDivs,
    "inference strategy help must be outside the hidden text-mode container");

const typeHelp = html.match(/<details id="tactic-help"[\s\S]*?<\/details>/);
assert.ok(typeHelp, "the type-theory proof assistant must expose collapsible help");
assert.match(typeHelp[0], /<summary>策略介绍<\/summary>/);
assert.doesNotMatch(typeHelp[0], /<details[^>]*\bopen(?:\s|=|>)/,
    "type-theory help should start collapsed");
for (const tactic of ["intro", "intros", "clear", "revert", "exact", "apply", "refine", "cases", "rcases", "obtain", "have", "use", "rw", "simp", "rfl", "qed"]) {
    assert.match(typeHelp[0], new RegExp(`<code>${tactic}(?:</code>|\\s)`),
        `type-theory help should describe ${tactic}`);
}
const refineHelp = typeHelp[0].match(/<p>(?:(?!<\/p>)[\s\S])*<code>refine t<\/code>[\s\S]*?<\/p>/)?.[0];
assert.ok(refineHelp, "type-theory help should explain refine separately from exact and apply");
for (const example of ["refine succ _", "refine λx:nat._", "refine (_,_)"]) {
    assert.ok(refineHelp.includes(`<code>${example}</code>`), `refine help should include ${example}`);
}
assert.match(refineHelp, /任意.*项/);
assert.match(refineHelp, /<code>_<\/code>.*<code>\?_<\/code>/);
assert.match(refineHelp, /推断.*不.*目标/);
assert.match(refineHelp, /作用域/);
assert.match(refineHelp, /依赖顺序/);
assert.match(refineHelp, /不支持命名孔位/);
assert.match(refineHelp, /随 <code>apply<\/code> 解锁/);
assert.doesNotMatch(inferenceHelp[0], /<code>refine(?:\s|<\/code>)/,
    "type-theory refine must not be advertised as an inference-layer command");
assert.match(css, /\.fs-proof-help\s*,\s*\.tactic-help\s*\{[^}]*max-width:\s*100%/);
assert.match(css, /\.fs-proof-help-content\s*,[\s\S]*overflow-wrap:\s*anywhere/);

console.log("proof-assistant strategy help regression passed");
