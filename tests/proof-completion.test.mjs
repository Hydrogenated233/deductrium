import assert from "node:assert/strict";
import { completeProofInput } from "../js/proof-completion.js";
import { highlightProofScript } from "../js/proof-editor.js";
import { isTTAssistTacticUnlocked, TT_ASSIST_COMMANDS } from "../js/tt/assist-engine.js";

const context = { commands: ["exact", "intro", "cases"], locals: ["h", "hyp", "α"],
    constants: ["hello", "h", "f"], aliases: [{ alias: "to", symbol: "→" }] };
const complete = source => completeProofInput(source, source.length, context);
assert.deepEqual(complete("  · exa").items.map(item => item.insert), ["exact"]);
assert.deepEqual(complete("have k : True := by exa").items.map(item => item.insert), ["exact"]);
assert.deepEqual(complete("exact h").items.map(item => item.insert), ["h", "hyp", "hello"]);
assert.deepEqual(complete("cases f").items.map(item => item.insert), ["f"]);
assert.deepEqual(complete("cases f gen").items.map(item => item.insert), ["generalizing"]);
assert.deepEqual(complete("cases f generalizing h").items.map(item => item.insert), ["h", "hyp"]);
assert.deepEqual(complete("exact α").items.map(item => item.insert), ["α"]);
assert.deepEqual(complete("exact ").items.map(item => item.insert), ["h", "hyp", "α", "hello", "f"]);
assert.deepEqual(complete("rw h at ").items.map(item => item.insert), ["h", "hyp", "α"]);
for (const command of ["clear", "revert"]) {
    assert.deepEqual(complete(`${command} h`).items.map(item => item.insert), ["h", "hyp"]);
    assert.deepEqual(complete(`${command} h `).items.map(item => item.insert), ["h", "hyp", "α"]);
}
assert.deepEqual(complete("cases f with x generalizing h").items.map(item => item.insert), ["h", "hyp"]);
assert.equal(complete("\\to").items[0].insert, "→");
assert.equal(completeProofInput("\\l", 2, { ...context, aliases: [
    { alias: "langle", symbol: "⟨" }, { alias: "l", symbol: "λ" }
] }).items[0].insert, "λ", "an exact alias must precede longer prefix matches");
for (const source of ["intro h", "have h", "-- exact h", '"exact h', "\\\\to", "Q\\to", "  "]) {
    assert.equal(complete(source).items.length, 0, source);
}
const middle = completeProofInput("exact hello", 9, context);
assert.equal(middle.start, 6);
assert.equal(middle.end, 11, "acceptance replaces the token suffix too");
assert.deepEqual(completeProofInput("exact h", 7, { ...context, locals: [], constants: [] }).items, [],
    "removed scope names must not be offered");
const typeContext = unlocked => ({
    ...context,
    commands: TT_ASSIST_COMMANDS.filter(command => isTTAssistTacticUnlocked(command, new Set(unlocked)))
});
assert.deepEqual(completeProofInput("ref", 3, typeContext([])).items, [],
    "refine completion must remain hidden before apply is unlocked");
assert.deepEqual(completeProofInput("ref", 3, typeContext(["apply"])).items.map(item => item.insert), ["refine"]);
for (const source of ["  · ref", "have n : nat := by ref"]) {
    assert.deepEqual(completeProofInput(source, source.length, typeContext(["apply"])).items
        .map(item => item.insert), ["refine"]);
}
for (const source of ["refine h", "refine (h", "refine f h"]) {
    assert.deepEqual(completeProofInput(source, source.length, typeContext(["apply"])).items.map(item => item.insert), ["h", "hyp", "hello"],
        "refine terms may reference both local and scoped constant names");
}
for (const hole of ["_", "?_"]) {
    assert.deepEqual(complete(`refine succ ${hole}`).items, [],
        "anonymous holes must not become name completion candidates");
    const highlighted = highlightProofScript(`refine succ ${hole}`);
    assert.ok(highlighted.includes('<span class="proof-token-command">refine</span>'));
    assert.ok(highlighted.includes(`<span class="proof-token-hole">${hole}</span>`),
        "the complete anonymous hole token should be highlighted");
}
assert.ok(highlightProofScript("  · refine (_,_)").includes(
    '<span class="proof-token-command">refine</span>'));
assert.equal(highlightProofScript("-- refine ?_"), '<span class="proof-token-comment">-- refine ?_</span>');
console.log("proof completion syntax and scope regression passed");
