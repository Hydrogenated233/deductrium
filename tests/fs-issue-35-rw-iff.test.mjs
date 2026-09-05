import assert from "node:assert/strict";

import { ASTParser } from "../js/fs/astparser.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { initFormalSystem } from "../js/fs/initial.js";
import { SavesParser } from "../js/fs/savesparser.js";

const parser = new ASTParser();
const allRules = () => Object.keys(initFormalSystem(true).fs.deductions);
const targetText = assistant => parser.stringifyTight(assistant.currentGoal.target);

// A local iff rewrites a supported implication context from left to right.
{
    const { fs } = initFormalSystem(true);
    const assistant = new InferenceProofAssistant(fs, "(A<>B)>((A>C)>(B>C))", {
        ruleNames: allRules(),
        allowIfft: true
    });
    assistant.apply("intro h");
    assistant.apply("rw h");
    assert.equal(targetText(assistant), "(B>C)>(B>C)");
    assistant.apply("exact .i");
    assistant.qed("issue35Forward");
    assert.doesNotThrow(() => fs.expandMacroWithDefaultValue("issue35Forward"));
    assert.equal(Object.keys(fs.deductions).some(name => name.startsWith("__rw_")), false);
}

// Reverse iff rewriting uses the opposite implication direction.
{
    const { fs } = initFormalSystem(true);
    const assistant = new InferenceProofAssistant(fs, "(A<>B)>((B>C)>(A>C))", {
        ruleNames: allRules(),
        allowIfft: true
    });
    assistant.apply("intro h");
    assistant.apply("rw <-h");
    assert.equal(targetText(assistant), "(A>C)>(A>C)");
    assistant.apply("exact .i");
    assistant.qed("issue35Reverse");
    assert.doesNotThrow(() => fs.expandMacroWithDefaultValue("issue35Reverse"));
}

// Page iff propositions are valid rw sources as well.
{
    const { fs } = initFormalSystem(true);
    fs.addHypothese(parser.parse("A<>B"));
    const assistant = new InferenceProofAssistant(fs, "(A>C)>(B>C)", {
        ruleNames: allRules(),
        allowIfft: true
    });
    assistant.apply("rw p0");
    assert.equal(targetText(assistant), "(B>C)>(B>C)");
    assistant.apply("exact .i");
    assistant.qed("issue35Page");
    assert.doesNotThrow(() => fs.expandMacroWithDefaultValue("issue35Page"));
}

// Quantifier contexts use the lifted `.<>rV` rule and survive qed replay.
{
    const { fs } = initFormalSystem(true);
    const assistant = new InferenceProofAssistant(fs, "(A<>B)>(Vx:((A>C)>(B>C)))", {
        ruleNames: allRules(),
        allowIfft: true
    });
    assistant.apply("intro h");
    assistant.apply("rw h");
    assert.equal(targetText(assistant), "(Vx:((B>C)>(B>C)))");
    assistant.apply("intro x");
    assistant.apply("exact .i");
    assistant.qed("issue35Quantifier");
    assert.doesNotThrow(() => fs.expandMacroWithDefaultValue("issue35Quantifier"));
}

// IFFT is an explicit capability.  A locked assistant must reject without
// changing the proof state or creating helper deductions.
{
    const { fs } = initFormalSystem(true);
    const assistant = new InferenceProofAssistant(fs, "(A<>B)>((A>C)>(B>C))", {
        ruleNames: allRules(),
        allowIfft: false
    });
    assistant.apply("intro h");
    const before = assistant.snapshot();
    const namesBefore = Object.keys(fs.deductions);
    assert.throws(() => assistant.apply("rw h"), /ifft|互推替换|解锁/);
    assert.deepEqual(assistant.snapshot(), before);
    assert.deepEqual(Object.keys(fs.deductions), namesBefore);
}

// Unlocking `ifft` alone is not enough for contextual rewriting: the
// corresponding lifting rule must also be visible in the proof scope.
{
    const { fs } = initFormalSystem(true);
    const ruleNames = allRules().filter(name => name !== ".<>r>");
    const assistant = new InferenceProofAssistant(fs, "(A<>B)>((A>C)>(B>C))", {
        ruleNames,
        allowIfft: true
    });
    assistant.apply("intro h");
    assert.equal(assistant.recommendations({ ruleNames }).some(command => command === "rw h"), false);
    const before = assistant.snapshot();
    assert.throws(() => assistant.apply("rw h"), /上下文等价规则|\.<>r>/);
    assert.deepEqual(assistant.snapshot(), before);
}

// Equality/member relation contexts are deliberately outside the logical
// lifting fragment and must fail transactionally.
{
    const { fs } = initFormalSystem(true);
    const assistant = new InferenceProofAssistant(fs, "(A<>B)>((A@C)>(B@C))", {
        ruleNames: allRules(),
        allowIfft: true
    });
    assistant.apply("intro h");
    const before = assistant.snapshot();
    assert.throws(() => assistant.apply("rw h"), /不支持|函数或关系/);
    assert.deepEqual(assistant.snapshot(), before);
}

// The capability snapshot must survive the deferred assistant save boundary.
// This prevents a loaded recipe from silently gaining iff lifting after the
// game has revoked the corresponding unlock.
{
    const { fs } = initFormalSystem(true);
    const assistant = new InferenceProofAssistant(fs, "(A<>B)>((A>C)>(B>C))", {
        ruleNames: allRules(),
        allowIfft: true
    });
    assistant.apply("intro h");
    assistant.apply("rw h");
    assistant.apply("exact .i");
    const result = assistant.qed("issue35Save");
    const encoded = JSON.parse(JSON.stringify(
        new SavesParser(true).serializeDeduction(fs.deductions.issue35Save)
    ));
    assert.equal(encoded[5].allowIfft, true);
    assert.equal(encoded[5].allowIfftEu, true);

    const restored = initFormalSystem(true).fs;
    const saves = new SavesParser(true);
    saves.deserializeDeduction("issue35Save", restored, encoded);
    assert.equal(restored.deductions.issue35Save.deferredPayload.allowIfft, true);
    assert.equal(restored.deductions.issue35Save.deferredPayload.allowIfftEu, true);
    assert.doesNotThrow(() => restored.expandMacroWithDefaultValue("issue35Save"));
    assert.equal(result.deferred, true);
}

// `ifft-EU` is a separate capability: lifting through `E!` must remain
// unavailable until that unlock, while ordinary iff rewriting still works.
{
    const { fs } = initFormalSystem(true);
    const locked = new InferenceProofAssistant(fs, "(A<>B)>(E!x:A>E!x:B)", {
        ruleNames: allRules(),
        allowIfft: true,
        allowIfftEu: false
    });
    locked.apply("intro h");
    const before = locked.snapshot();
    assert.throws(() => locked.apply("rw h"), /ifft-EU|跨E!/);
    assert.deepEqual(locked.snapshot(), before);

    const open = new InferenceProofAssistant(fs, "(A<>B)>(E!x:A>E!x:B)", {
        ruleNames: allRules(),
        allowIfft: true,
        allowIfftEu: true
    });
    open.apply("intro h");
    open.apply("rw h");
    open.apply("intro hx");
    open.apply("exact hx");
    open.qed("issue35EUnique");
    assert.doesNotThrow(() => fs.expandMacroWithDefaultValue("issue35EUnique"));
}

// Ordinary existential lifting uses `.<>rE` and does not require the
// `ifft-EU` capability.
{
    const { fs } = initFormalSystem(true);
    const assistant = new InferenceProofAssistant(fs, "(A<>B)>((Ex:A)>(Ex:B))", {
        ruleNames: allRules(),
        allowIfft: true,
        allowIfftEu: false
    });
    assistant.apply("intro h");
    assistant.apply("rw h");
    assistant.apply("intro hx");
    assistant.apply("exact hx");
    assistant.qed("issue35Existential");
    assert.doesNotThrow(() => fs.expandMacroWithDefaultValue("issue35Existential"));
}

// Equivalent user rules may use different metavariable names and order.  The
// resolver must map canonical iff/a6 parameters before writing replacement
// rows instead of assuming the built-in positional order.
{
    const { fs } = initFormalSystem(true);
    const parserRules = [
        ["iffForwardAlias", "⊢($b<>$a)>($a>$b)"],
        ["iffImpAlias", "$b1<>$b2,$a1<>$a2⊢($b1>$a1)<>($b2>$a2)"],
        ["forallAlias", "⊢(#nf($pred,$var)>(V$var:#nf($pred,$var)))"]
    ];
    for (const [name, value] of parserRules) fs.addDeduction(name, parser.parse(value), "test");
    const builtins = allRules().filter(name => ![".<>1", ".<>2", ".<>r>", "a6"].includes(name));
    const ruleNames = [...builtins, ...parserRules.map(([name]) => name)];
    const assistant = new InferenceProofAssistant(fs,
        "(A<>B)>(Vx:((A>C)>(B>C)))", {
            ruleNames,
            allowIfft: true
        });
    assistant.apply("intro h");
    assistant.apply("rw h");
    assistant.apply("intro x");
    assistant.apply("intro hx");
    assistant.apply("exact hx");
    assistant.qed("issue35Aliases");
    assert.doesNotThrow(() => fs.expandMacroWithDefaultValue("issue35Aliases"));
}

console.log("GitHub issue #35 iff rw regression passed");
