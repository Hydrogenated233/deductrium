import assert from "node:assert/strict";
import fs from "node:fs";

for (const path of ["../src/fs/gui.ts", "../js/fs/gui.js"]) {
    const gui = fs.readFileSync(new URL(path, import.meta.url), "utf8");
    const inputHandler = gui.match(
        /input\.addEventListener\("keydown", event => \{([\s\S]*?)\n\s*\}\);/
    );

    assert.ok(inputHandler, `${path}: the inference proof assistant input keydown handler must exist`);
    assert.match(
        inputHandler[1],
        /else if \(event\.key === "Escape"\) \{\s*event\.preventDefault\(\);\s*input\.value = "";/,
        `${path}: Escape must clear the active inference strategy input`
    );
    assert.doesNotMatch(
        inputHandler[1],
        /closeInferenceProofAssistant\(/,
        `${path}: Escape must not close the inference proof assistant`
    );
    assert.match(
        gui,
        /recommendations\(\{[\s\S]*?ruleNames:\s*this\.deductions,[\s\S]*?canTauto:\s*this\.metarules\.includes\("cpt"\)/,
        `${path}: recommendations must use visible rules and the unlocked CPT state`
    );
    const assistantConstructors = gui.match(/new InferenceProofAssistant\(/g) ?? [];
    const assistantCapabilities = gui.match(
        /allowMcpt:\s*this\.metarules\.includes\("cpt"\)/g
    ) ?? [];
    assert.equal(
        assistantCapabilities.length,
        assistantConstructors.length,
        `${path}: every inference proof-assistant entry must use the unlocked CPT state`
    );
    const fastMetaCapabilities = gui.match(
        /fastMetaRules:\s*this\.formalSystem\.fastmetarules/g
    ) ?? [];
    assert.equal(
        fastMetaCapabilities.length,
        assistantConstructors.length,
        `${path}: every inference proof-assistant entry must use the unlocked fast metarules`
    );
}

const html = fs.readFileSync(new URL("../index.html", import.meta.url), "utf8");
const toolbar = html.match(/<div class="fs-proof-toolbar">([\s\S]*?)<\/div>/)?.[1] ?? "";
assert.doesNotMatch(toolbar, /fs-proof-commands/, "recommendation buttons must not remain in the top toolbar");
assert.match(
    html,
    /<div class="proof-assistant-input-row fs-proof-input-row">[\s\S]*?<\/div>\s*<div id="fs-proof-commands" class="proof-assistant-recommendations fs-proof-recommendations"/,
    "recommendation buttons must render below the strategy input row"
);

console.log("inference proof assistant Escape regression passed");
