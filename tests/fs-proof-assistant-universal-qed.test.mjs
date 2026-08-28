import assert from "node:assert/strict";
import { initFormalSystem } from "../js/fs/initial.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { ASTParser } from "../js/fs/astparser.js";

const parser = new ASTParser();
const fs = initFormalSystem(true).fs;
const target = "Vx:(Va:(((x=1)&(a=1))>(x=a)))";
const assistant = new InferenceProofAssistant(fs, target);

for (const command of [
    "intros ha hb hand",
    "obtain <h1,h2> := hand",
    "rw [h1,h2]",
    "rfl"
]) assistant.apply(command);

const result = assistant.qed();
assert.equal(result.committed, true);
assert.equal(fs.propositions.length, 1);
assert.doesNotThrow(() => fs.expandMacroWithProp(0),
    "expanding a deferred proof must restore universal binders introduced by the assistant");
assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), parser.stringifyTight(parser.parse(target)));

// Preserve the exact reverse intro order when implication and universal
// binders are interleaved: Vx:(A > Vy:P) is not Vx:Vy:(A > P).
{
    const mixedFs = initFormalSystem(true).fs;
    const mixedTarget = "Vx:(A>(Vy:(x=x)))";
    const mixed = new InferenceProofAssistant(mixedFs, mixedTarget);
    mixed.apply("intros x h y");
    mixed.apply("rfl");
    mixed.qed();
    assert.doesNotThrow(() => mixedFs.expandMacroWithProp(0));
    assert.equal(parser.stringifyTight(mixedFs.propositions.at(-1).value),
        parser.stringifyTight(parser.parse(mixedTarget)));
}

console.log("inference universal-intro qed expansion regression passed");
