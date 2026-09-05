import assert from "node:assert/strict";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { ASTParser } from "../js/fs/astparser.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();
const fs = initFormalSystem(true).fs;
fs.addHypothese(parser.parse("V$x:($1<>$2)"));
const assistant = new InferenceProofAssistant(fs, "#rp($1,$x,$y)<>#rp($2,$x,$y)");
for (const command of [
    "constructor",
    "intro h",
    "have hx := p0 $x",
    "obtain <h12,h21> := hx",
    "apply h12",
    "exact h",
    "intro h",
    "have hx := p0 $x",
    "obtain <h12,h21> := hx",
    "apply h21",
    "exact h"
]) assistant.apply(command);

const result = assistant.qed("issue28PremiseQed");
assert.equal(result.committed, true);
assert.deepEqual(
    fs.deductions.issue28PremiseQed.conditions.map(value => parser.stringifyTight(value)),
    ["(V$x:($1<>$2))"]
);
const materialized = fs.materializeDeferredDeduction("issue28PremiseQed");
assert.equal(parser.stringifyTight(materialized.conclusion), "#rp($1,$x,$y)<>#rp($2,$x,$y)");

console.log("GitHub issue #28 proof-assistant premise qed regression passed");
