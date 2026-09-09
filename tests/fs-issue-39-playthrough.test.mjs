import assert from "node:assert/strict";
import { ASTParser } from "../js/fs/astparser.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();
const target = String.raw`~0@(N\{0})`;
const commands = [
    String.raw`have hd := d\ $a=N $b={0} $c=z`,
    "rw hd",
    "have hsall : Vz:((z@{z@N|~(z@{0})})<>(z@N&~(z@{0})))",
    "intro z",
    "exact d{@|}",
    "have hs := hsall 0",
    "have hsing := d{.} 0 0",
    "have heq := a7 0",
    // The reported final tauto is outside MCPT's propositional fragment.
    "have hzero := .<>2 0@{0} 0=0",
    "have hzeroimp := hzero hsing",
    "have hin := hzeroimp heq",
    "apply .a32 $1=0@{0}",
    "intro hz",
    "have hforward := .<>1 (0@{z@N|~(z@{0})}) (0@N&~(0@{0}))",
    "have hforwardimp := hforward hs",
    "have hpair := hforwardimp hz",
    "obtain <hn,hnot> := hpair",
    "exact hnot",
    "exact hin"
];

for (const name of [undefined, "issue39SetDifference"]) {
    const fs = initFormalSystem(true).fs;
    const options = { allowMcpt: false };
    const assistant = new InferenceProofAssistant(fs, target, options);
    for (const command of commands) assistant.apply(command);
    const restored = new InferenceProofAssistant(fs, target, options);
    restored.restore(JSON.parse(JSON.stringify(assistant.snapshot())));
    assert.equal(restored.qed(name).committed, true);
    if (name) {
        assert.deepEqual(fs.deductions[name].conditions, []);
        fs.deduct({ deductionIdx: name, conditionIdxs: [], replaceValues: [] });
    }
    fs.expandMacroWithProp(fs.propositions.length - 1);
    assert.deepEqual(fs.propositions.at(-1).value, parser.parse(target));
    assert.ok(fs.propositions.every(row => row.from),
        "the set difference theorem must have no undischarged hypotheses");
}

console.log("GitHub issue #39 set difference playthrough regression passed");
