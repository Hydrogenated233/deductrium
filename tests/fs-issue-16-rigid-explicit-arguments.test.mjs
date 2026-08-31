import assert from "node:assert/strict";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { ASTParser } from "../js/fs/astparser.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();

// The original report, covering both argument syntaxes and both assertion
// wrappers.  The explicitly supplied term is still schematic: treating its
// `$` names as rigid changes #rp/#nf into an unrelated `$1` subgoal.
const cases = [
    {
        name: "#rp positional",
        command: "apply issue16Contra (V$0:~$1) #rp($1,$0,$2)",
        expected: ["(V$0:~$1)>~#rp($1,$0,$2)", "#rp($1,$0,$2)"]
    },
    {
        name: "#rp named",
        command: "apply issue16Contra $0=(V$0:~$1) $1=#rp($1,$0,$2)",
        expected: ["(V$0:~$1)>~#rp($1,$0,$2)", "#rp($1,$0,$2)"]
    },
    {
        name: "#nf positional",
        command: "apply issue16Contra (V$0:~$1) #nf($1,$0)",
        expected: ["(V$0:~$1)>~#nf($1,$0)", "#nf($1,$0)"]
    },
    {
        name: "#nf named",
        command: "apply issue16Contra $0=(V$0:~$1) $1=#nf($1,$0)",
        expected: ["(V$0:~$1)>~#nf($1,$0)", "#nf($1,$0)"]
    }
];

for (const testCase of cases) {
    const fs = initFormalSystem(true).fs;
    fs.addDeduction("issue16Contra", parser.parse("$0>~$1,$1⊢~$0"), "test*");
    // The test rule is intentionally given positional replacement metadata;
    // named arguments still exercise the same explicit-argument path.
    fs.deductions.issue16Contra.replaceNames = ["$0", "$1"];
    const assistant = new InferenceProofAssistant(fs, "~(V$0:~$1)");
    assistant.apply(testCase.command);
    assert.deepEqual(
        assistant.snapshot().goals.map(goal => parser.stringifyTight(goal.target)),
        testCase.expected,
        testCase.name
    );
}

console.log("GitHub issue #16 explicit assertion-argument regression passed");
