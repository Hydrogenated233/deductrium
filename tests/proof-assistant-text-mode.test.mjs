import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

const html = await readFile(new URL("../index.html", import.meta.url), "utf8");
const css = await readFile(new URL("../gui.css", import.meta.url), "utf8");
const ttGui = await readFile(new URL("../src/tt/gui.ts", import.meta.url), "utf8");
const fsGui = await readFile(new URL("../src/fs/gui.ts", import.meta.url), "utf8");

for (const id of [
    "tactic-text-toggle",
    "tactic-text-mode",
    "tactic-script",
    "tactic-script-state",
    "tactic-script-error",
    "tactic-script-recommendations",
    "tactic-script-run",
    "fs-proof-text-toggle",
    "fs-proof-text-mode",
    "fs-proof-script",
    "fs-proof-script-state",
    "fs-proof-script-error",
    "fs-proof-script-recommendations",
    "fs-proof-script-run"
]) {
    assert.match(html, new RegExp(`id="${id}"`), `text mode control ${id} must exist`);
}
assert.doesNotMatch(html, /class="list-wrapper tactic-assist-wrapper"/,
    "proof assistants must not add the black list-wrapper frame");
assert.doesNotMatch(html, /id="fs-proof-session" class="[^"]*list-wrapper/,
    "inference proof session must not use list-wrapper");
assert.doesNotMatch(html, /id="fs-proof-text-mode" class="[^"]*list-wrapper/,
    "inference text mode must not use list-wrapper");
assert.match(html, /id="fs-proof-assistant" class="proof-assistant fs-proof-assistant"/,
    "inference assistant must use the shared proof-assistant surface");
assert.match(html, /id="tactic-div" class="proof-assistant hide"/,
    "type-theory assistant must use the shared proof-assistant surface");

assert.match(css, /\.proof-assistant\s*\{[\s\S]*min-width:\s*0/);
assert.match(css, /\.proof-text-mode\s*\{[\s\S]*grid-template-columns/);
assert.match(css, /\.proof-text-output\s*\{[\s\S]*display:\s*flex/);
assert.match(css, /\.proof-text-output \.fs-proof-goal,[\s\S]*\.proof-text-output \.proof-text-goal/);
assert.match(css, /@media\s*\(max-width:\s*700px\)[\s\S]*\.proof-text-mode/);
assert.match(css, /@media\s*\(max-width:\s*700px\)[\s\S]*#fs-proof-target/);
assert.match(css, /@media\s*\(max-width:\s*700px\)[\s\S]*#tactic-input/);
assert.doesNotMatch(css, /#9b7bb5|border-left:\s*2px\s+solid/,
    "proof goals must not restore the removed purple guide line");
assert.match(ttGui, /replayTacticText\(explicitRun: boolean\)/);
assert.match(ttGui, /第 \$\{errorLine\} 行/);
assert.match(ttGui, /event\.key === "Enter" && event\.ctrlKey/);
assert.match(ttGui, /deductrium-tt-proof-text-mode/);
assert.match(fsGui, /replayInferenceProofText\(explicitRun: boolean\)/);
assert.match(fsGui, /第 \$\{errorLine\} 行/);
assert.match(fsGui, /event\.key === "Enter" && event\.ctrlKey/);
assert.match(fsGui, /deductrium-fs-proof-text-mode/);
assert.match(ttGui, /renderTacticTextRecommendations/);
assert.match(fsGui, /renderInferenceProofTextRecommendations/);
assert.match(ttGui, /createTextNode\("  \|  "\)/);
assert.match(fsGui, /createTextNode\("  \|  "\)/);

console.log("proof-assistant text-mode UI regression passed");
