import assert from "node:assert/strict";
import { completeProofInput } from "../js/proof-completion.js";

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
console.log("proof completion syntax and scope regression passed");
