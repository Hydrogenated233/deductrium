import assert from "node:assert/strict";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { ASTParser } from "../js/fs/astparser.js";
import { SavesParser } from "../js/fs/savesparser.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();
const saves = new SavesParser(true);

// Bare qed is one page row and keeps the replay recipe, not the expanded graph.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assistant.apply("intro h");
    assistant.apply("exact h");
    const result = assistant.qed();
    assert.equal(fs.propositions.length, 1);
    assert.equal(result.steps.length, 1);
    const row = fs.propositions[0];
    const deduction = fs.deductions[row.from.deductionIdx];
    assert.equal(row.deferredKind, "assistant");
    assert.equal(deduction.deferredKind, "assistant");
    assert.equal(deduction.steps, undefined);
    assert.deepEqual(deduction.deferredPayload.history, ["intro h", "exact h"]);

    const serialized = saves.serializeDeduction(deduction);
    assert.equal(serialized[2], undefined);
    assert.equal(serialized[4], "assistant");
    assert.deepEqual(serialized[5].history, ["intro h", "exact h"]);
    assert.equal(serialized[5].premises.length, 0);

    const propositionTuple = saves.serializeProposition(row);
    assert.equal(propositionTuple[2], "assistant");
    const restoredRow = saves.deserializeProposition(propositionTuple);
    assert.equal(restoredRow.deferredKind, "assistant");

    fs.expandMacroWithProp(0);
    assert.ok(fs.deductions[row.from.deductionIdx].steps?.length);
    const serializedAfterExpansion = saves.serializeDeduction(fs.deductions[row.from.deductionIdx]);
    assert.equal(serializedAfterExpansion[2], undefined,
        "materializing a lazy assistant rule must not make saved steps eager");
    assert.deepEqual(serializedAfterExpansion[5].history, ["intro h", "exact h"]);
}

// pN references are snapshotted and replayed against a private page, so a
// loaded assistant proof does not depend on the current page object identity.
{
    const source = initFormalSystem(true).fs;
    source.addHypothese(parser.parse("A>B"));
    source.addHypothese(parser.parse("A"));
    const assistant = new InferenceProofAssistant(source, "B");
    assistant.apply("apply p0");
    assistant.apply("exact p1");
    const result = assistant.qed();
    const tuple = JSON.parse(JSON.stringify(saves.serializeDeduction(source.deductions[result.deductionName])));

    const restored = initFormalSystem(true).fs;
    restored.addHypothese(parser.parse("A>B"));
    restored.addHypothese(parser.parse("A"));
    saves.deserializeDeduction(result.deductionName, restored, tuple);
    restored.propositions.push({
        value: parser.parse("B"),
        from: { deductionIdx: result.deductionName, conditionIdxs: [0, 1], replaceValues: [] }
    });
    restored.expandMacroWithProp(2);
    assert.equal(parser.stringifyTight(restored.propositions.at(-1).value), "B");
    assert.ok(restored.deductions[result.deductionName].steps?.length);
}

// Named qed keeps the legacy page-clearing behavior while storing a deferred
// rule that can be expanded later as a regular macro.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assistant.apply("intro h");
    assistant.apply("exact h");
    assistant.qed("namedAssistantProof");
    assert.equal(fs.propositions.length, 0);
    assert.equal(fs.deductions.namedAssistantProof.deferredKind, "assistant");
    assert.equal(fs.deductions.namedAssistantProof.steps, undefined);
    fs.expandMacroWithDefaultValue("namedAssistantProof");
    assert.ok(fs.deductions.namedAssistantProof.steps?.length);
}

// A bad recipe must fail before mutating the live proposition page.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assistant.apply("intro h");
    assistant.apply("exact h");
    const result = assistant.qed();
    const name = result.deductionName;
    fs.deductions[name].deferredPayload.history = ["intro h", "unknown-command"];
    const before = fs.propositions.slice();
    assert.throws(() => fs.expandMacroWithProp(0));
    assert.deepEqual(fs.propositions, before);
}

// A failed pN remap must not poison the recursion guard: fixing the payload
// and retrying should report the real replay result, not a false cycle.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assistant.apply("intro h");
    assistant.apply("exact h");
    const result = assistant.qed();
    const deduction = fs.deductions[result.deductionName];
    deduction.deferredPayload.history = ["exact p9"];
    assert.throws(() => fs.expandMacroWithProp(0), /前提定理 p9/);
    deduction.deferredPayload.history = ["intro h", "exact h"];
    fs.expandMacroWithProp(0);
    assert.ok(deduction.steps?.length);
}

console.log("inference proof-assistant lazy atomic regression passed");
