import assert from "node:assert/strict";

import { ASTParser } from "../js/fs/astparser.js";
import { expandInferenceSnapshot } from "../js/fs/inference-worker-core.js";
import { initFormalSystem } from "../js/fs/initial.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { SavesParser } from "../js/fs/savesparser.js";

const parser = new ASTParser();

const creativeInit = initFormalSystem(true);
assert.ok(creativeInit.arrD.includes("sorry"));
assert.ok(creativeInit.fs.deductions.sorry);
assert.equal(creativeInit.fs.deductions.sorry.conditions.length, 0);
assert.equal(parser.stringifyTight(creativeInit.fs.deductions.sorry.conclusion), "$0");

const creativeAssistant = new InferenceProofAssistant(creativeInit.fs, "A", {
    ruleNames: creativeInit.arrD,
    allowMcpt: false
});
assert.ok(creativeAssistant.recommendations({
    ruleNames: creativeInit.arrD
}).includes("exact sorry"));
assert.equal(creativeAssistant.apply("exact sorry").complete, true);
creativeAssistant.qed("savedSorryProof");
assert.ok(creativeInit.fs.deductions.savedSorryProof);

const pageAssistant = new InferenceProofAssistant(creativeInit.fs, "B", {
    ruleNames: creativeInit.arrD,
    allowMcpt: false
});
pageAssistant.apply("exact sorry");
pageAssistant.qed();
assert.ok(creativeInit.fs.propositions.at(-1)?.from);

const creativeSaves = new SavesParser(true);
const creativeSave = creativeSaves.serialize({
    formalSystem: creativeInit.fs,
    deductions: creativeInit.arrD,
    metarules: [],
    getProps: () => creativeInit.fs.propositions,
    pageStore: creativeInit.fs.inferencePages
});
const creativeData = JSON.parse(creativeSave).data;

const survivalInit = initFormalSystem(false);
assert.equal(survivalInit.arrD.includes("sorry"), false);
assert.equal(survivalInit.fs.deductions.sorry, undefined);
const survivalAssistant = new InferenceProofAssistant(survivalInit.fs, "A", {
    ruleNames: survivalInit.arrD,
    allowMcpt: false
});
assert.equal(survivalAssistant.recommendations({
    ruleNames: survivalInit.arrD
}).includes("exact sorry"), false);
assert.throws(
    () => survivalAssistant.apply("exact sorry"),
    /未找到证明来源|不在当前证明助手作用域|不存在/
);

const restored = new SavesParser(false).deserializeArr(
    initFormalSystem(false).fs,
    structuredClone(creativeData)
);
assert.equal(restored.arrD.includes("sorry"), false);
assert.equal(restored.fs.deductions.sorry, undefined);
assert.equal(restored.fs.deductions.savedSorryProof, undefined);
assert.equal(restored.fs.propositions.at(-1)?.from, null,
    "a proposition proved through creative sorry must restore as a hypothesis in survival");

assert.doesNotThrow(() => expandInferenceSnapshot({
    save: creativeSave,
    creative: true,
    fastMetaRules: "",
    metarules: [],
    target: { kind: "proposition", index: 0 }
}));
assert.throws(() => expandInferenceSnapshot({
    save: creativeSave,
    creative: false,
    fastMetaRules: "",
    metarules: [],
    target: { kind: "proposition", index: 0 }
}), /假设|无法展开|不存在|hypothesis|deduction steps/);

console.log("creative-only inference sorry regression passed");
