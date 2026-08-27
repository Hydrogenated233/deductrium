import assert from "node:assert/strict";

import { ASTParser } from "../js/fs/astparser.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();
const lockedRules = ["mp", "a1", "a2"];

function addRules(fs) {
    fs.addDeduction("myCases", parser.parse("$0>$1,~$0>$1⊢$1"), "test");
    fs.addDeduction("myLeft", parser.parse("$0⊢$0|$1"), "test");
    fs.addDeduction("myRight", parser.parse("$1⊢$0|$1"), "test");
    return [...lockedRules, "myCases", "myLeft", "myRight"];
}

// Case analysis is hidden and rejected until .m2 or an equivalent rule exists.
{
    const fs = initFormalSystem(false).fs;
    const assistant = new InferenceProofAssistant(fs, "A|~A", { ruleNames: lockedRules });
    assert.equal(assistant.recommendations().some(command => command.startsWith("by_cases")), false);
    assert.throws(() => assistant.apply("by_cases h : A"), /需要解锁|等价推理规则/);
}

// Each branch gets the same local name in an independent scope and materializes
// through the ordinary .m2-style apply node.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addRules(fs);
    const assistant = new InferenceProofAssistant(fs, "A|~A", { ruleNames });
    assert.ok(assistant.recommendations().includes("by_cases h : ??"));
    assistant.apply("by_cases h : A");
    assert.equal(assistant.snapshot().goals.length, 2);
    assert.equal(parser.stringifyTight(assistant.currentGoal.hypotheses.at(-1).proposition), "A");
    assistant.apply("left");
    assistant.apply("exact h");
    assert.equal(parser.stringifyTight(assistant.currentGoal.hypotheses.at(-1).proposition), "~A");
    assistant.apply("right");
    assistant.apply("exact h");
    assert.equal(assistant.snapshot().complete, true);
    assistant.qed();
    fs.expandMacroWithProp(0);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "A|~A");
}

// Syntax errors and name collisions roll back the whole command.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addRules(fs);
    const assistant = new InferenceProofAssistant(fs, "A>(A|~A)", { ruleNames });
    assistant.apply("intro h");
    const before = assistant.snapshot();
    assert.throws(() => assistant.apply("by_cases h : B"), /假设名称已存在/);
    assert.deepEqual(assistant.snapshot(), before);
    assert.throws(() => assistant.apply("by_cases B"), /语法应为/);
    assert.deepEqual(assistant.snapshot(), before);
}

console.log("inference proof-assistant by_cases regression passed");
