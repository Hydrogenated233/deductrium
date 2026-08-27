import assert from "node:assert/strict";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { ASTParser } from "../js/fs/astparser.js";
import { SavesParser } from "../js/fs/savesparser.js";
import { DEFERRED_ASSISTANT_STEP } from "../js/fs/formalsystem.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();
const saves = new SavesParser(true);

// A bare assistant proof is represented by one step-local recipe.  No
// per-proof __assist_N deduction is allocated, and expansion must work even
// when a free `$` variable occurs only in the theorem conclusion.
{
    const fs = initFormalSystem(true).fs;
    fs.addHypothese(parser.parse("$0"));
    const assistant = new InferenceProofAssistant(fs, "~$1>$0");
    assistant.apply("intro");
    assistant.apply("exact p0");
    const result = assistant.qed();

    assert.equal(result.deductionName, DEFERRED_ASSISTANT_STEP);
    assert.equal(result.steps.length, 1);
    assert.equal(result.steps[0].deductionIdx, DEFERRED_ASSISTANT_STEP);
    assert.ok(result.steps[0].assistant);
    assert.equal(Object.keys(fs.deductions).some(name => /^__assist_/.test(name)), false);
    assert.equal(fs.propositions.length, 2);
    assert.equal(fs.propositions[1].from.assistant.history[1], "exact p0");

    fs.expandMacroWithProp(1);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "~$1>$0");
    assert.equal(Object.keys(fs.deductions).some(name => /^__assist_/.test(name)), false);
}

// Multiple bare assistant proofs use the same compatibility marker, while
// each page step retains its own replay recipe.
{
    const fs = initFormalSystem(true).fs;
    fs.addHypothese(parser.parse("$0"));
    const first = new InferenceProofAssistant(fs, "~$1>$0");
    first.apply("intro");
    first.apply("exact p0");
    first.qed();
    const second = new InferenceProofAssistant(fs, "~$1>$0");
    second.apply("intro");
    second.apply("exact p0");
    second.qed();
    assert.equal(fs.propositions[1].from.deductionIdx, DEFERRED_ASSISTANT_STEP);
    assert.equal(fs.propositions[2].from.deductionIdx, DEFERRED_ASSISTANT_STEP);
    assert.notEqual(fs.propositions[1].from.assistant, fs.propositions[2].from.assistant);
    assert.equal(Object.keys(fs.deductions).filter(name => /^__assist_/.test(name)).length, 0);
}

// Step metadata survives the compact proposition save format.  The legacy
// three-field tuple remains accepted by deserializeDeductionStep.
{
    const fs = initFormalSystem(true).fs;
    fs.addHypothese(parser.parse("$0"));
    const assistant = new InferenceProofAssistant(fs, "~$1>$0");
    assistant.apply("intro");
    assistant.apply("exact p0");
    assistant.qed();
    const row = fs.propositions[1];
    const encoded = saves.serializeProposition(row);
    const restored = saves.deserializeProposition(JSON.parse(JSON.stringify(encoded)));
    assert.equal(restored.from.deductionIdx, DEFERRED_ASSISTANT_STEP);
    assert.deepEqual(restored.from.assistant.history, ["intro", "exact p0"]);
    assert.equal(saves.deserializeDeductionStep(["mp", [], []]).assistant, undefined);
}

// Legacy bare-qed rules may still be present in an imported save under an
// `__assist_N` name.  Expansion normalizes their inferred conclusion-only
// replacement names instead of calling getReplVarsType(undefined).
{
    const source = initFormalSystem(true).fs;
    source.addHypothese(parser.parse("$0"));
    const assistant = new InferenceProofAssistant(source, "~$1>$0");
    assistant.apply("intro");
    assistant.apply("exact p0");
    assistant.qed();
    const marker = source.deductions[DEFERRED_ASSISTANT_STEP];
    const tuple = JSON.parse(JSON.stringify(saves.serializeDeduction(marker)));

    const restored = initFormalSystem(true).fs;
    restored.addHypothese(parser.parse("$0"));
    saves.deserializeDeduction("__assist_1", restored, tuple);
    restored.propositions.push({
        value: parser.parse("~$1>$0"),
        from: { deductionIdx: "__assist_1", conditionIdxs: [0], replaceValues: [] },
        deferredKind: "assistant"
    });
    restored.expandMacroWithProp(1);
    assert.equal(parser.stringifyTight(restored.propositions.at(-1).value), "~$1>$0");
}

console.log("proof-assistant step metadata regression passed");
