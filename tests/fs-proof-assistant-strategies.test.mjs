import assert from "node:assert/strict";
import { ASTParser } from "../js/fs/astparser.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { SavesParser } from "../js/fs/savesparser.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();
const lockedRules = ["mp", "a1", "a2"];

// assumption is a direct local-hypothesis shortcut and does not need a
// bundled rule.
{
    const fs = initFormalSystem(false).fs;
    const assistant = new InferenceProofAssistant(fs, "A>A", { ruleNames: lockedRules });
    assistant.apply("intro h");
    assert.ok(assistant.recommendations().includes("assumption"));
    assistant.apply("assumption");
    assert.equal(assistant.snapshot().complete, true);
}

// In a locked-down environment, constructor is hidden and rejected until an
// equivalent user rule is available.
{
    const fs = initFormalSystem(false).fs;
    const assistant = new InferenceProofAssistant(fs, "A&B", { ruleNames: lockedRules });
    assert.equal(assistant.recommendations().includes("constructor"), false);
    assert.throws(() => assistant.apply("constructor"), /需要解锁|等价推理规则/);

    fs.addDeduction("myAnd", parser.parse("$0,$1⊢$0&$1"), "test");
    const unlocked = new InferenceProofAssistant(fs, "A&B", { ruleNames: [...lockedRules, "myAnd"] });
    assert.ok(unlocked.recommendations().includes("constructor"));
}

// Locked strategies remain unavailable when no equivalent user rule exists.
{
    const fs = initFormalSystem(false).fs;
    const symm = new InferenceProofAssistant(fs, "A=B", { ruleNames: lockedRules });
    assert.equal(symm.recommendations().includes("symm"), false);
    assert.throws(() => symm.apply("symm"), /需要解锁|等价推理规则/);

    const contradiction = new InferenceProofAssistant(fs, "A>(~A>C)", { ruleNames: lockedRules });
    contradiction.apply("intro h");
    contradiction.apply("intro nh");
    assert.equal(contradiction.recommendations().includes("contradiction"), false);
    assert.throws(() => contradiction.apply("contradiction"), /需要解锁|等价推理规则/);
}

// The same fallback rule is used by the tactic implementation, not merely by
// recommendation filtering.
{
    const fs = initFormalSystem(false).fs;
    fs.addDeduction("myAnd", parser.parse("$0,$1⊢$0&$1"), "test");
    const assistant = new InferenceProofAssistant(fs, "A>(B>(A&B))", {
        ruleNames: [...lockedRules, "myAnd"]
    });
    assistant.apply("intro ha");
    assistant.apply("intro hb");
    assistant.apply("constructor");
    assistant.apply("exact ha");
    assistant.apply("exact hb");
    assert.equal(assistant.snapshot().complete, true);
}

// The unlocked-scope choice is persisted with a deferred proof, so replay
// does not silently use a hidden bundled rule after loading the save.
{
    const fs = initFormalSystem(false).fs;
    fs.addDeduction("myAnd", parser.parse("$0,$1⊢$0&$1"), "test");
    const assistant = new InferenceProofAssistant(fs, "A>(B>(A&B))", {
        ruleNames: [...lockedRules, "myAnd"]
    });
    assistant.apply("intro ha");
    assistant.apply("intro hb");
    assistant.apply("constructor");
    assistant.apply("exact ha");
    assistant.apply("exact hb");
    assistant.qed();
    const row = fs.propositions[0];
    const encoded = new SavesParser(true).serializeProposition(row);
    assert.deepEqual(encoded[1][3].ruleNames, [...lockedRules, "myAnd"]);
    fs.expandMacroWithProp(0);
    // Discharging the two intro hypotheses legitimately wraps the atomic
    // user rule in a generated conditional rule (usually `ccmyAnd`).  The
    // expansion contract is that the deferred proof can be replayed and
    // reaches the original theorem, not that a particular helper layer is
    // preserved as the top-level step.
    assert.ok(fs.deductions.__assistant.steps?.some(step => step.deductionIdx === "ccmyAnd"));
    const conditionalRule = fs.deductions.ccmyAnd;
    assert.ok(conditionalRule, "the conditionalized user rule should be materialized");
    assert.equal(conditionalRule.conditions.length, 2);
    assert.equal(conditionalRule.conclusion.type, "sym");
    assert.equal(conditionalRule.conclusion.name, ">");
    assert.equal(conditionalRule.conclusion.nodes[1]?.type, "sym");
    assert.equal(conditionalRule.conclusion.nodes[1]?.name, ">");
    assert.equal(conditionalRule.conclusion.nodes[1]?.nodes[1]?.type, "sym");
    assert.equal(conditionalRule.conclusion.nodes[1]?.nodes[1]?.name, "&");
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "A>(B>(A&B))");
}

// Equality symmetry also accepts a structurally equivalent user rule when the
// built-in . =s rule is not unlocked.
{
    const fs = initFormalSystem(false).fs;
    fs.addDeduction("mySymm", parser.parse("$0=$1⊢$1=$0"), "test");
    const assistant = new InferenceProofAssistant(fs, "(B=A)>(A=B)", {
        ruleNames: [...lockedRules, "mySymm"]
    });
    assistant.apply("intro h");
    assert.ok(assistant.recommendations().includes("symm"));
    assistant.apply("symm");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "B=A");
    assistant.apply("exact h");
    assert.equal(assistant.snapshot().complete, true);
}

// contradiction uses the equivalent user rule and consumes P/~P in order.
{
    const fs = initFormalSystem(false).fs;
    fs.addDeduction("myContra", parser.parse("$0,~$0⊢$1"), "test");
    const assistant = new InferenceProofAssistant(fs, "A>(~A>C)", {
        ruleNames: [...lockedRules, "myContra"]
    });
    assistant.apply("intro h");
    assistant.apply("intro nh");
    assert.ok(assistant.recommendations().includes("contradiction"));
    assistant.apply("contradiction");
    assert.equal(assistant.snapshot().complete, true);
}

console.log("inference proof-assistant strategy regression passed");
