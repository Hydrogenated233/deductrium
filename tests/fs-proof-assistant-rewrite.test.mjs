import assert from "node:assert/strict";

import { ASTParser } from "../js/fs/astparser.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();
const lockedRules = ["mp", "a1", "a2"];

function addRewriteRules(fs) {
    fs.addDeduction("mySymm", parser.parse("$0=$1⊢$1=$0"), "test");
    fs.addDeduction("mySubst", parser.parse("⊢($0=$1)>($2>#rp($2,$0,$1,$3))"), "test");
    fs.addDeduction("myRfl", parser.parse("⊢$0=$0"), "test");
    return [...lockedRules, "mySymm", "mySubst", "myRfl"];
}

// Locked equality rules hide and reject rw without mutating the proof state.
{
    const fs = initFormalSystem(false).fs;
    const assistant = new InferenceProofAssistant(fs, "(A=B)>((A,B)=(A,B))", { ruleNames: lockedRules });
    assistant.apply("intro h");
    assert.equal(assistant.recommendations().includes("rw h"), false);
    const before = assistant.snapshot();
    assert.throws(() => assistant.apply("rw h"), /需要解锁|等价推理规则/);
    assert.deepEqual(assistant.snapshot(), before);
}

// rw replaces every original occurrence and still reconstructs the exact old
// target when the destination already occurred before rewriting.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addRewriteRules(fs);
    const assistant = new InferenceProofAssistant(fs, "(A=B)>((A,B)=(A,B))", { ruleNames });
    assistant.apply("intro h");
    assert.ok(assistant.recommendations().includes("rw h"));
    assistant.apply("rw h");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "(B,B)=(B,B)");
    assistant.apply("rfl");
    assistant.qed();
    fs.expandMacroWithProp(0);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "(A=B)>((A,B)=(A,B))");
}

// nth_rw uses one-based left-to-right occurrence numbering.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addRewriteRules(fs);
    const assistant = new InferenceProofAssistant(fs, "(A=B)>((A,A)=(A,B))", { ruleNames });
    assistant.apply("intro h");
    assistant.apply("nth_rw 2 h");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "(A,B)=(A,B)");
    assistant.apply("rfl");
    assert.equal(assistant.snapshot().complete, true);
}

// A destination containing the source is inserted once per original match;
// it must not be recursively rewritten during the same command.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addRewriteRules(fs);
    const assistant = new InferenceProofAssistant(fs, "(A=(A,A))>(A=A)", { ruleNames });
    assistant.apply("intro h");
    assistant.apply("rw h");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "(A,A)=(A,A)");
    assistant.apply("rfl");
    assistant.qed();
    fs.expandMacroWithProp(0);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "(A=(A,A))>(A=A)");
}

// Reverse and sequential list rewriting share the same proof-producing core.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addRewriteRules(fs);
    const reverse = new InferenceProofAssistant(fs, "(A=B)>((B,A)=(B,A))", { ruleNames });
    reverse.apply("intro h");
    reverse.apply("rw <-h");
    assert.equal(parser.stringifyTight(reverse.currentGoal.target), "(A,A)=(A,A)");
    reverse.apply("rfl");

    const sequence = new InferenceProofAssistant(fs, "(A=B)>((B=C)>((A,C)=(C,C)))", { ruleNames });
    sequence.apply("intro h");
    sequence.apply("intro g");
    sequence.apply("rw [h,g]");
    assert.equal(parser.stringifyTight(sequence.currentGoal.target), "(C,C)=(C,C)");
    sequence.apply("rfl");
    sequence.qed();
    fs.expandMacroWithProp(0);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "(A=B)>((B=C)>((A,C)=(C,C)))");
}

// Missing and out-of-range occurrences are actionable and transactional.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addRewriteRules(fs);
    const assistant = new InferenceProofAssistant(fs, "(A=B)>(C=C)", { ruleNames });
    assistant.apply("intro h");
    const before = assistant.snapshot();
    assert.throws(() => assistant.apply("rw h"), /未找到可改写项/);
    assert.deepEqual(assistant.snapshot(), before);

    const nth = new InferenceProofAssistant(fs, "(A=B)>((A,A)=(A,B))", { ruleNames });
    nth.apply("intro h");
    assert.throws(() => nth.apply("nth_rw 9 h"), /序号超出匹配数量/);
    assert.throws(() => nth.apply("rw h at h"), /rw at 假设改写尚未支持/);
}

// Bound variables are not rewritten by a free equality with the same spelling.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addRewriteRules(fs);
    const assistant = new InferenceProofAssistant(fs, "(x=y)>(Vx:(x=x))", { ruleNames });
    assistant.apply("intro h");
    const before = assistant.snapshot();
    assert.throws(() => assistant.apply("rw h"), /未找到可改写项/);
    assert.deepEqual(assistant.snapshot(), before);
}

// Page equalities can drive a rewrite and remain snapshotted by deferred qed.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addRewriteRules(fs);
    fs.addHypothese(parser.parse("A=B"));
    const assistant = new InferenceProofAssistant(fs, "(A,B)=(A,B)", { ruleNames });
    assistant.apply("rw p0");
    assistant.apply("rfl");
    assistant.qed();
    fs.expandMacroWithProp(1);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "(A,B)=(A,B)");
}

// Distinct replacement-variable names are fixed surface occurrences for rw.
// An unknown possible match in a different sibling must not cancel the known
// $0 occurrence selected by rw p0.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addRewriteRules(fs);
    fs.addHypothese(parser.parse("$0=$1"));
    fs.addHypothese(parser.parse("$1=$2"));
    const assistant = new InferenceProofAssistant(fs, "$0=$2", { ruleNames });
    assistant.apply("rw p0");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "$1=$2");
}

console.log("inference proof-assistant rewrite regression passed");
