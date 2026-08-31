import assert from "node:assert/strict";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { ASTParser } from "../js/fs/astparser.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();

function makeInvalidAssistant() {
    const fs = initFormalSystem(true).fs;
    fs.fastmetarules = "c>:<qvu";
    fs.addHypothese(parser.parse("Seed"));
    const assistant = new InferenceProofAssistant(
        fs,
        "(Vx:F(x)@y)>(Vy:(Vx:F(x)@y))",
        {
            fastMetaRules: fs.fastmetarules,
            ruleNames: Object.keys(fs.deductions),
            allowMcpt: true
        }
    );
    for (const command of ["intro h", "intro y", "exact h"]) assistant.apply(command);
    assert.equal(assistant.snapshot().complete, true);
    return { fs, assistant };
}

// A deferred row is visible to #p before expansion.  qed must therefore run
// enough of the replay materializer to reject this illegal generalization
// before a bare-qed page row is registered.  Existing page state and the
// completed draft must survive the failed transaction.
{
    const { fs, assistant } = makeInvalidAssistant();
    const history = assistant.snapshot().history;
    const deductionNames = Object.keys(fs.deductions).sort();
    const previousRows = fs.propositions.slice();
    assert.throws(
        () => assistant.qed(),
        /全称变量出现在未解除的外部前提中：y/
    );
    assert.deepEqual(fs.propositions, previousRows);
    assert.deepEqual(Object.keys(fs.deductions).sort(), deductionNames);
    assert.deepEqual(assistant.snapshot().history, history);
    assert.equal(assistant.snapshot().complete, true);
}

// Previewing remains lazy, but commit must validate before a named deduction
// is registered.  A rejected preview is not marked committed and can be
// retried without accumulating generated rules or changing the page.
{
    const { fs, assistant } = makeInvalidAssistant();
    const history = assistant.snapshot().history;
    const deductionNames = Object.keys(fs.deductions).sort();
    const previousRows = fs.propositions.slice();
    const preview = assistant.materializeQed("issue17InvalidGeneralization");
    assert.equal(preview.committed, false);
    for (let attempt = 0; attempt < 2; attempt++) {
        assert.throws(
            () => assistant.commit(preview),
            /全称变量出现在未解除的外部前提中：y/
        );
        assert.equal(preview.committed, false);
        assert.deepEqual(fs.propositions, previousRows);
        assert.deepEqual(Object.keys(fs.deductions).sort(), deductionNames);
        assert.deepEqual(assistant.snapshot().history, history);
        assert.equal(assistant.snapshot().complete, true);
    }
}

console.log("GitHub issue #17 qed generalization validation regression passed");
