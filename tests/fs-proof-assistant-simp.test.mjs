import assert from "node:assert/strict";

import { ASTParser } from "../js/fs/astparser.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();
const lockedRules = ["mp", "a1", "a2"];

function addRules(fs, includeRfl = true) {
    fs.addDeduction("mySymm", parser.parse("$0=$1⊢$1=$0"), "test");
    fs.addDeduction("mySubst", parser.parse("⊢($0=$1)>($2>#rp($2,$0,$1,$3))"), "test");
    const names = [...lockedRules, "mySymm", "mySubst"];
    if (includeRfl) {
        fs.addDeduction("myRfl", parser.parse("⊢$0=$0"), "test");
        names.push("myRfl");
    }
    return names;
}

// Without a8/equivalent rules, simp is hidden and rolls back cleanly.
{
    const fs = initFormalSystem(false).fs;
    const assistant = new InferenceProofAssistant(fs, "((A,A)=A)>((A,A)=(A,A))", {
        ruleNames: lockedRules
    });
    assistant.apply("intro h");
    assert.equal(assistant.recommendations().includes("simp"), false);
    const before = assistant.snapshot();
    assert.throws(() => assistant.apply("simp"), /需要解锁|等价推理规则/);
    assert.deepEqual(assistant.snapshot(), before);
}

// simp chooses the structurally smaller side and closes a reflexive result.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addRules(fs);
    const assistant = new InferenceProofAssistant(fs, "((A,A)=A)>((A,A)=(A,A))", { ruleNames });
    assistant.apply("intro h");
    assert.ok(assistant.recommendations().includes("simp"));
    assistant.apply("simp");
    assert.equal(assistant.snapshot().complete, true);
    assistant.qed();
    fs.expandMacroWithProp(0);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "((A,A)=A)>((A,A)=(A,A))");
}

// simp only excludes unrelated local equalities and does not require rfl.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addRules(fs, false);
    const assistant = new InferenceProofAssistant(fs,
        "((A,A)=A)>(((B,B)=B)>(((A,A),(B,B))=((A,A),(B,B))))", { ruleNames });
    assistant.apply("intro ha");
    assistant.apply("intro hb");
    assistant.apply("simp only [ha]");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "(A,(B,B))=(A,(B,B))");
    assistant.apply("simp only [hb]");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "(A,B)=(A,B)");
}

// Opposite equalities orient to the same total order instead of cycling.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addRules(fs);
    const assistant = new InferenceProofAssistant(fs, "(A=B)>((B=A)>(B=B))", { ruleNames });
    assistant.apply("intro h");
    assistant.apply("intro g");
    assistant.apply("simp");
    assert.equal(assistant.snapshot().complete, true);
}

// Explicit sources, page sources, and unsupported hypothesis rewriting are
// deterministic and transactional.
{
    const fs = initFormalSystem(false).fs;
    const ruleNames = addRules(fs, false);
    fs.addHypothese(parser.parse("(A,A)=A"));
    const assistant = new InferenceProofAssistant(fs, "(A,A)=(A,A)", { ruleNames });
    assistant.apply("simp only [p0]");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "A=A");
    const before = assistant.snapshot();
    assert.throws(() => assistant.apply("simp at p0"), /simp at 假设化简尚未支持/);
    assert.deepEqual(assistant.snapshot(), before);
    assert.throws(() => assistant.apply("simp only [missing]"), /未找到证明来源/);
}

console.log("inference proof-assistant simp regression passed");
