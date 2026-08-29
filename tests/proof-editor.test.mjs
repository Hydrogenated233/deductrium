import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { computeProofEditorGutters, highlightProofScript, scriptThroughCaret } from "../js/proof-editor.js";

const highlighted = highlightProofScript("intro ha\napply f _\n-- note");
assert.match(highlighted, /proof-token-command[^>]*>intro<\/span>/);
assert.match(highlighted, /proof-token-identifier[^>]*>ha<\/span>/);
assert.match(highlighted, /proof-token-hole[^>]*>_<\/span>/);
assert.match(highlighted, /proof-token-comment[^>]*>-- note<\/span>/);
assert.match(highlightProofScript("use 1"), /proof-token-command[^>]*>use<\/span>/,
    "use should be highlighted as a proof command");
assert.doesNotMatch(highlightProofScript("<script>"), /<script>/,
    "highlighting must escape user text before inserting HTML");

const textarea = { value: "intro h\napply f\nexact h\n", selectionStart: 12 };
assert.equal(scriptThroughCaret(textarea), "intro h\napply f");
textarea.selectionStart = textarea.value.length;
assert.equal(scriptThroughCaret(textarea), "intro h\napply f\nexact h\n");

// The mirror has no scrollbar of its own.  Reserve the textarea's native
// scrollbar gutter so wrapped lines and the caret remain aligned on systems
// with classic (non-overlay) scrollbars.
assert.deepEqual(computeProofEditorGutters({
    offsetWidth: 420,
    clientWidth: 405,
    offsetHeight: 240,
    clientHeight: 225,
    borderHorizontal: 2,
    borderVertical: 2
}), { right: 13, bottom: 13 });
assert.deepEqual(computeProofEditorGutters({
    offsetWidth: 420,
    clientWidth: 418,
    offsetHeight: 240,
    clientHeight: 238,
    borderHorizontal: 2,
    borderVertical: 2
}), { right: 0, bottom: 0 });

const html = await readFile(new URL("../index.html", import.meta.url), "utf8");
const css = await readFile(new URL("../gui.css", import.meta.url), "utf8");
for (const id of [
    "tactic-script-highlight", "fs-proof-script-highlight",
    "tactic-script-run-cursor", "fs-proof-script-run-cursor", "fs-proof-close"
]) assert.match(html, new RegExp(`id="${id}"`), `${id} must exist`);
const fsHeader = html.match(/<div id="fs-proof-assistant"[\s\S]*?<div id="fs-proof-session"/);
assert.ok(fsHeader, "inference proof header must be present");
assert.ok(fsHeader[0].indexOf('id="fs-proof-target"') < fsHeader[0].indexOf('id="fs-proof-close"')
    && fsHeader[0].indexOf('id="fs-proof-close"') < fsHeader[0].indexOf('id="fs-proof-text-toggle"'),
    "inference exit button must sit between target input and text-mode toggle");
assert.match(fsHeader[0], /id="fs-proof-close"[^>]*class="[^"]*inhabitat-modify[^"]*"/,
    "inference exit button must retain the shared inhabitat-modify styling");
assert.match(css, /\.proof-code-editor\s*\{/);
assert.match(css, /\.proof-token-command\s*\{/);
assert.match(css, /\.proof-code-editor textarea\s*\{[\s\S]*color:\s*transparent/);
const proofEditor = await readFile(new URL("../src/proof-editor.ts", import.meta.url), "utf8");
assert.match(proofEditor, /computeProofEditorGutters/);
assert.match(proofEditor, /this\.highlight\.style\.right/);
assert.match(proofEditor, /new ResizeObserver/);

const ttGui = await readFile(new URL("../src/tt/gui.ts", import.meta.url), "utf8");
const fsGui = await readFile(new URL("../src/fs/gui.ts", import.meta.url), "utf8");
assert.match(ttGui, /replayTacticText\(true, true\)/);
assert.match(ttGui, /scriptThroughCaret\(script\)/);
assert.match(ttGui, /replayTacticText\(false, true\)/,
    "type-theory automatic replay must stop at the caret");
assert.match(ttGui, /addEventListener\("selectionchange", scheduleTacticCaretReplay\)/);
assert.match(fsGui, /replayInferenceProofText\(true, true\)/);
assert.match(fsGui, /scriptThroughCaret\(script\)/);
assert.match(fsGui, /replayInferenceProofText\(false, true\)/,
    "inference automatic replay must stop at the caret");
assert.match(fsGui, /addEventListener\("selectionchange", scheduleInferenceCaretReplay\)/);
assert.match(fsGui, /TR\("量词变量"\)/,
    "inference universal binders should be labeled without borrowing the quantified body as a type");
const fsAssistant = await readFile(new URL("../src/fs/proof-assistant.ts", import.meta.url), "utf8");
assert.match(fsAssistant, /case "intros"/);

console.log("proof editor highlighting and cursor execution regression passed");
