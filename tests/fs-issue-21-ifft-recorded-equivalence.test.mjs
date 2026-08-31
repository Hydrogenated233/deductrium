import assert from "node:assert/strict";

import { ASTMgr } from "../js/fs/astmgr.js";
import { ASTParser } from "../js/fs/astparser.js";
import { initFormalSystem } from "../js/fs/initial.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";

const astmgr = new ASTMgr();
const parser = new ASTParser();
const fs = initFormalSystem(true).fs;
fs.fastmetarules = "cvuqe><:#zZQR";

const recordAssistantTheorem = (name, theorem, commands) => {
    const assistant = new InferenceProofAssistant(fs, theorem, {
        fastMetaRules: fs.fastmetarules,
        ruleNames: Object.keys(fs.deductions),
        allowMcpt: true
    });
    for (const command of commands) assistant.apply(command);
    assistant.qed(name);
};

const runIfft = (sourceRule, source, name) => {
    fs.metaIffTheorem(
        sourceRule,
        [parser.parse(source), parser.parse("0")],
        name,
        "test*",
        false
    );
    return fs.deductions[name];
};

// Prime the universal-lifting cache with the tutorial raw-iff equivalence.
// Issue #21 appeared only after another recorded theorem had already occupied
// the shared v__assistant/vv__assistant helper names.
recordAssistantTheorem(
    "sRawIff",
    "(~(($0>$1)>~($1>$0)))<>($0<>$1)",
    ["tauto"]
);
runIfft(
    "sRawIff",
    "VxVy(Vz(~(((z@x)>(z@y))>~((z@y)>(z@x))))>x=y)",
    "issue21Prime"
);

const source = "Vx:Vy:Vz:~(a>~b)";
const expected = parser.parse(`(${source})<>(Vx:Vy:Vz:(a&b))`);

recordAssistantTheorem("sRawAnd", "~($0>~$1)<>($0&$1)", ["tauto"]);
const deferredTauto = runIfft("sRawAnd", source, "issue21Tauto");
assert.equal(
    astmgr.equal(deferredTauto.conclusion, expected),
    true,
    "quantified ifft must use the selected deferred tauto theorem, not a stale assistant helper"
);
assert.doesNotThrow(() => fs.expandMacroWithDefaultValue("issue21Tauto"));

// The defect is not tauto-specific: an ordinary proof-assistant recording has
// the same deferred representation and must remain independent as well.
recordAssistantTheorem("sRawAndD", "~($0>~$1)<>($0&$1)", ["symm", "exact d&"]);
const recordedMacro = runIfft("sRawAndD", source, "issue21Recorded");
assert.equal(
    astmgr.equal(recordedMacro.conclusion, expected),
    true,
    "quantified ifft must preserve an ordinary recorded equivalence macro"
);
assert.doesNotThrow(() => fs.expandMacroWithDefaultValue("issue21Recorded"));

console.log("GitHub issue #21 quantified ifft cache regression passed");
