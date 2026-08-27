import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

const html = await readFile(new URL("../index.html", import.meta.url), "utf8");
const css = await readFile(new URL("../gui.css", import.meta.url), "utf8");

const inferenceHelp = html.match(/<details id="fs-proof-help"[\s\S]*?<\/details>/);
assert.ok(inferenceHelp, "the inference proof assistant must expose collapsible help");
assert.match(inferenceHelp[0], /<summary>策略介绍<\/summary>/);
assert.doesNotMatch(inferenceHelp[0], /<details[^>]*\bopen(?:\s|=|>)/,
    "inference help should start collapsed");
for (const tactic of ["intro", "exact", "apply", "assumption", "constructor", "symm", "contradiction", "have", "qed"]) {
    assert.match(inferenceHelp[0], new RegExp(`<code>${tactic}(?:</code>|\\s)`),
        `inference help should describe ${tactic}`);
}

const typeHelp = html.match(/<details id="tactic-help"[\s\S]*?<\/details>/);
assert.ok(typeHelp, "the type-theory proof assistant must expose collapsible help");
assert.match(typeHelp[0], /<summary>策略介绍<\/summary>/);
assert.doesNotMatch(typeHelp[0], /<details[^>]*\bopen(?:\s|=|>)/,
    "type-theory help should start collapsed");
for (const tactic of ["intro", "exact", "apply", "destruct", "rw", "simpl", "rfl", "qed"]) {
    assert.match(typeHelp[0], new RegExp(`<code>${tactic}(?:</code>|\\s)`),
        `type-theory help should describe ${tactic}`);
}
assert.match(css, /\.fs-proof-help\s*,\s*\.tactic-help\s*\{[^}]*max-width:\s*100%/);
assert.match(css, /\.fs-proof-help-content\s*,[\s\S]*overflow-wrap:\s*anywhere/);

console.log("proof-assistant strategy help regression passed");
