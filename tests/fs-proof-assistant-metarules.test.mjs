import assert from "node:assert/strict";
import { ASTParser } from "../js/fs/astparser.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();
const baseRules = ["mp", "a1", "a2"];

// Hidden bundled rules must not become available through direct apply/exact.
{
    const fs = initFormalSystem(false).fs;
    const assistant = new InferenceProofAssistant(fs, "C", {
        ruleNames: baseRules,
        fastMetaRules: ""
    });
    assert.throws(
        () => assistant.apply("apply .m $0=A $1=C"),
        /未解锁|作用域|不可用/
    );

    const exact = new InferenceProofAssistant(fs, "A>A", {
        ruleNames: baseRules,
        fastMetaRules: ""
    });
    assert.throws(() => exact.apply("exact .i"), /作用域|不可用/);
}

// A generated rule remains gated after it has been cached by another context.
{
    const fs = initFormalSystem(false).fs;
    fs.fastmetarules = ">";
    fs.generateDeduction(">.m");
    fs.fastmetarules = "";
    const assistant = new InferenceProofAssistant(fs, "~A>B", {
        ruleNames: [".m"],
        fastMetaRules: ""
    });
    assert.throws(() => assistant.apply("apply >.m $0=A $1=B"), /演绎元定理|未解锁/);
}

// Cached generated rules also retain the automatic dependency audit; caching
// under a wider unlock set cannot hide c/< requirements from a later page.
{
    const fs = initFormalSystem(false).fs;
    fs.fastmetarules = "><c";
    fs.generateDeduction(">.m");
    fs.fastmetarules = "";
    const assistant = new InferenceProofAssistant(fs, "~A>B", {
        ruleNames: [".m"],
        fastMetaRules: ">"
    });
    assert.throws(
        () => assistant.apply("apply >.m $0=A $1=B"),
        /自动生成证明步骤需要解锁.*(?:条件演绎|逆演绎)元定理/
    );
}

// A metatheorem cannot expose a hidden atomic rule from the bundle.
{
    const fs = initFormalSystem(false).fs;
    const assistant = new InferenceProofAssistant(fs, "~A>B", {
        ruleNames: baseRules,
        fastMetaRules: ">"
    });
    assert.throws(() => assistant.apply("apply >.m $0=A $1=B"), /作用域|不可用|未解锁/);
}

// The > generator itself emits c/< helpers; those automatic dependencies are
// checked instead of being silently enabled by the metatheorem implementation.
{
    const fs = initFormalSystem(false).fs;
    const assistant = new InferenceProofAssistant(fs, "~A>B", {
        ruleNames: [".m"],
        fastMetaRules: ">"
    });
    assert.throws(
        () => assistant.apply("apply >.m $0=A $1=B"),
        /自动生成证明步骤需要解锁.*(?:条件演绎|逆演绎)元定理/
    );
}

// intro recommendations and execution follow the c/v metatheorem unlocks.
{
    const implication = new InferenceProofAssistant(initFormalSystem(false).fs, "A>A", {
        ruleNames: baseRules,
        fastMetaRules: "",
        allowMcpt: false
    });
    assert.equal(implication.recommendations().includes("intro"), false);
    assert.throws(() => implication.apply("intro h"), /条件演绎元定理|未解锁/);

    const missingInverse = new InferenceProofAssistant(initFormalSystem(false).fs, "A>A", {
        ruleNames: baseRules,
        fastMetaRules: "c",
        allowMcpt: false
    });
    assert.equal(missingInverse.recommendations().includes("intro"), false);
    assert.throws(() => missingInverse.apply("intro h"), /逆演绎元定理|未解锁/);

    const universal = new InferenceProofAssistant(initFormalSystem(false).fs, "Vx:(x=x)", {
        ruleNames: [...baseRules, "a6", "a7"],
        fastMetaRules: ""
    });
    assert.equal(universal.recommendations().includes("intro"), false);
    assert.throws(() => universal.apply("intro x"), /条件概括元定理|未解锁/);
}

// Strategies that introduce branch hypotheses inherit the same c gate.
{
    const fs = initFormalSystem(false).fs;
    fs.addDeduction("myReductio", parser.parse("⊢(~$0>$0)>$0"), "test");
    fs.addDeduction("myCases", parser.parse("$0>$1,~$0>$1⊢$1"), "test");

    const reductio = new InferenceProofAssistant(fs, "A", {
        ruleNames: ["myReductio"],
        fastMetaRules: ""
    });
    assert.equal(reductio.recommendations().includes("by_contra"), false);
    assert.throws(() => reductio.apply("by_contra h"), /条件演绎元定理|未解锁/);

    const cases = new InferenceProofAssistant(fs, "A|~A", {
        ruleNames: ["myCases"],
        fastMetaRules: ""
    });
    assert.equal(cases.recommendations().some(command => command.startsWith("by_cases")), false);
    assert.throws(() => cases.apply("by_cases h : A"), /条件演绎元定理|未解锁/);
}

{
    const fs = initFormalSystem(false).fs;
    fs.addHypothese(parser.parse("A|B"));
    fs.addDeduction("myOrElim", parser.parse("$0>$2,$1>$2⊢($0|$1)>$2"), "test");
    const assistant = new InferenceProofAssistant(fs, "C", {
        ruleNames: ["myOrElim"],
        fastMetaRules: ""
    });
    assert.equal(assistant.recommendations().some(command => command.startsWith("obtain ")), false);
    assert.throws(
        () => assistant.apply("obtain ha | hb := p0"),
        /条件演绎元定理|未解锁/
    );
}

// The two deduction metatheorems are usable inside the assistant only when
// their prefix is unlocked and their underlying rule is visible.
{
    const fs = initFormalSystem(false).fs;
    fs.addHypothese(parser.parse("A"));
    const assistant = new InferenceProofAssistant(fs, "~A>B", {
        ruleNames: [".m"],
        fastMetaRules: "><c"
    });
    assistant.apply("apply >.m $0=A $1=B");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "A");
    assistant.apply("exact p0");
    assert.equal(assistant.snapshot().complete, true);
    assistant.qed();
    assert.equal(fs.propositions[1].from.assistant.fastMetaRules, "><c");
    assert.doesNotThrow(() => fs.expandMacroWithProp(1));
}

// Mixed prefixes are considered when they produce the same semantic rule;
// the shortest recursive expansion wins over the canonical c-only form.
{
    const fs = initFormalSystem(false).fs;
    const fastMetaRules = "cvuqe><:#zZQR";
    const assistant = new InferenceProofAssistant(fs, "A>(~A>C)", {
        ruleNames: [".m", "a1", "a2", "mp"],
        fastMetaRules,
        allowMcpt: false
    });
    assistant.apply("intro h");
    assistant.apply("intro nh");
    assistant.apply("apply .m $0=A $1=C");
    assistant.apply("exact h");
    assistant.apply("exact nh");
    assistant.qed();
    fs.expandMacroWithProp(0);
    assert.ok(fs.propositions.some(proposition => proposition.from?.deductionIdx === "cc.m"));
}

// Strict c/< snapshots still support the automatic implication-intro path;
// the generated helper is expanded only after the deferred proof is opened.
{
    const fs = initFormalSystem(false).fs;
    const assistant = new InferenceProofAssistant(fs, "A>A", {
        ruleNames: baseRules,
        fastMetaRules: "c<",
        allowMcpt: false
    });
    assistant.apply("intro h");
    assistant.apply("exact h");
    assistant.qed();
    assert.doesNotThrow(() => fs.expandMacroWithProp(0));
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "A>A");
}

{
    const fs = initFormalSystem(false).fs;
    fs.addHypothese(parser.parse("A"));
    const assistant = new InferenceProofAssistant(fs, "B>A", {
        ruleNames: ["a1"],
        fastMetaRules: "<"
    });
    assistant.apply("apply <a1 $0=A $1=B");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "A");
    assistant.apply("exact p0");
    assert.equal(assistant.snapshot().complete, true);
}

console.log("inference proof-assistant metarule gating regression passed");
