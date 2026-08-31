import assert from "node:assert/strict";

import { ASTMgr } from "../js/fs/astmgr.js";
import { ASTParser } from "../js/fs/astparser.js";
import { initFormalSystem } from "../js/fs/initial.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";

const astmgr = new ASTMgr();
const parser = new ASTParser();
const fs = initFormalSystem(true).fs;
fs.fastmetarules = "cvuqe><:#zZQR";

const assistant = new InferenceProofAssistant(
    fs,
    "(~(($0>$1)>~($1>$0)))<>($0<>$1)",
    {
        fastMetaRules: fs.fastmetarules,
        ruleNames: Object.keys(fs.deductions),
        allowMcpt: true
    }
);
assistant.apply("tauto");
assistant.qed("sRawIff");

const source = parser.parse(
    "VxVy(Vz(~(((z@x)>(z@y))>~((z@y)>(z@x))))>x=y)"
);
const expected = parser.parse(
    "VxVy(Vz((z@x)<>(z@y))>x=y)"
);

assert.doesNotThrow(() => fs.metaIffTheorem(
    "sRawIff",
    [source, parser.parse("0")],
    "issue20Iff",
    "test*",
    false
));
assert.equal(
    astmgr.equal(
        fs.deductions.issue20Iff.conclusion,
        parser.parse(`(${parser.stringifyTight(source)})<>(${parser.stringifyTight(expected)})`)
    ),
    true,
    "ifft must lift a deferred tauto theorem through the tutorial quantifiers"
);
assert.doesNotThrow(() => fs.expandMacroWithDefaultValue("issue20Iff"));

console.log("issue #20 ifft/tauto regression passed");
