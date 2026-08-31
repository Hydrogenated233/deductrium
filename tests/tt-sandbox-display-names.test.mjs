import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { lowerSandboxInductive, parseSandboxInductive } from "../js/tt/sandbox.js";
import { sandboxInductiveDisplaySources } from "../js/tt/sandbox-gui.js";
import { prettySandboxInductiveNamesForDisplay } from "../js/tt/presentation.js";

const parser = new ASTParser();
const bundle = lowerSandboxInductive(parseSandboxInductive(
    "inductive Nat : U | On : Nat | succn : Nat -> Nat"
));
const sourceType = bundle.auxiliaryTypes[0][1];
const sourceText = parser.stringify(sourceType);
const displayed = prettySandboxInductiveNamesForDisplay(sourceType, {
    constructorNames: bundle.metadata.constructors.map(ctor => ctor.name)
});
const displayedText = parser.stringify(displayed);

// Generated implementation names stay in the checker-owned bundle, while
// the cloned presentation uses readable, constructor-specific binders.
assert.equal(parser.stringify(sourceType), sourceText);
assert.match(displayedText, /ΠcOn:C On/);
assert.match(displayedText, /Πcsuccn:/);
assert.match(displayedText, /Πn:Nat/);
assert.match(displayedText, /Πih:C n/);
assert.doesNotMatch(displayedText, /a1_0|ih1_0|Πc0|Πc1/);
assert.match(sourceText, /a1_0|ih1_0/);

// The alpha-renamer must also update dependent occurrences, not just binder
// labels; otherwise the rendered motive would refer to a missing variable.
assert.match(displayedText, /C \(succn n\)/);

assert.deepEqual(sandboxInductiveDisplaySources({
    kind: "inductive",
    inductive: parseSandboxInductive("inductive tri : U | nt : tri | succT : tri -> tri")
}), [
    "tri : U",
    "nt : tri",
    "succT : tri -> tri"
], "valid inductive rows must render their structured head and constructors instead of a parser error");

assert.deepEqual(sandboxInductiveDisplaySources({
    kind: "inductive",
    inductive: parseSandboxInductive(
        "inductive List2 (A : U) : U | nil2 : List2 A | cons2 : A -> List2 A -> List2 A"
    )
}), [
    "List2 (A : U) : U",
    "nil2 : List2 A",
    "cons2 : A -> List2 A -> List2 A"
], "parameterized inductives must retain parameter binders and full constructor results");

assert.deepEqual(sandboxInductiveDisplaySources({
    kind: "inductive",
    inductive: parseSandboxInductive(
        "inductive Vec (A : U) [n : nat] : U | vnil : Vec A 0"
    )
}), [
    "Vec (A : U) [n : nat] : U",
    "vnil : Vec A 0"
], "indexed inductives must distinguish square-bracket indices from uniform parameters");

console.log("sandbox inductive display-name regression passed");
