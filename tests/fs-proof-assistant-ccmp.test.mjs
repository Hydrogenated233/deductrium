import assert from "node:assert/strict";
import { FormalSystem } from "../js/fs/formalsystem.js";
import { ASTParser } from "../js/fs/astparser.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";

const parser = new ASTParser();

function makeCcmpSystem() {
    const fs = new FormalSystem();
    // This is the parameter order produced by the condition-deduction path.
    // Its metavariables are intentionally unrelated to the page's `$` names.
    fs.addDeduction(
        "ccmp",
        parser.parse("($3>($2>($0>$1))),($3>($2>$0))⊢($3>($2>$1))"),
        "test"
    );
    fs.addHypothese(parser.parse("$0>($1>$2)"));
    fs.addHypothese(parser.parse("$0>($1>($2>$3))"));
    return fs;
}

// Explicit schema-to-environment mapping keeps rule metavariables separate
// from user `$` variables. `$0=$2` supplies the only premise-only variable;
// the conclusion determines the remaining mappings.
{
    const fs = makeCcmpSystem();
    const assistant = new InferenceProofAssistant(fs, "$0>($1>$3)");
    assistant.apply("apply ccmp $0=$2");
    assert.deepEqual(
        assistant.snapshot().goals.map(goal => parser.stringifyTight(goal.target)),
        ["$0>($1>($2>$3))", "$0>($1>$2)"]
    );
}

// A failed/unknown schema mapping must be transactional and must not retain a
// partially-applied ccmp node or mutate the command history.
{
    const fs = makeCcmpSystem();
    const assistant = new InferenceProofAssistant(fs, "$0>($1>$3)");
    const before = assistant.snapshot();
    assert.throws(() => assistant.apply("apply ccmp $9=$2"), /映射|变量|参数|匹配|规则/);
    assert.deepEqual(assistant.snapshot().history, before.history);
    assert.deepEqual(
        assistant.snapshot().goals.map(goal => parser.stringifyTight(goal.target)),
        before.goals.map(goal => parser.stringifyTight(goal.target))
    );
}

console.log("ccmp metavariable-scope regression passed");
