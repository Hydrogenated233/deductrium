import assert from "node:assert/strict";
import { ASTParser } from "../js/fs/astparser.js";
import { initFormalSystem } from "../js/fs/initial.js";
import { SavesParser } from "../js/fs/savesparser.js";

const parser = new ASTParser();
const source = initFormalSystem(true);
const fs = source.fs;
fs.addHypothese(parser.parse("True"));
const mainId = fs.inferencePages.activeId;
fs.createInferencePage("第二表");
fs.activateInferencePage("第二表");
fs.addHypothese(parser.parse("True"));
const secondId = fs.inferencePages.activeId;
fs.inferencePages.active.command.state = {
    inferenceProof: { theorem: parser.parse("A>A"), history: ["intro h"] },
    marker: "preserve-me"
};

const gui = {
    formalSystem: fs,
    deductions: source.arrD,
    metarules: [],
    pageStore: fs.inferencePages,
    actionInput: { value: "d" },
    cmd: { cmdBuffer: ["d", "a"], escClear: false, lastDeduction: "a" },
    getProps: () => fs.propositions
};
const saver = new SavesParser(true);
const encoded = saver.serialize(gui);
const parsed = JSON.parse(encoded);
assert.equal(parsed.version, 2);
assert.equal(parsed.data[7].activeId, secondId);
assert.deepEqual(parsed.data[7].pages.map(p => p.name), ["主表", "第二表"]);
assert.deepEqual(parsed.data[7].pages.map(p => p.propositions.length), [1, 1]);
assert.deepEqual(parsed.data[7].pages[1].command.buffer, ["d", "a"]);
assert.deepEqual(parsed.data[7].pages[1].command.state.inferenceProof.history, ["intro h"]);
assert.equal(parsed.data[7].pages[1].command.state.marker, "preserve-me");

const restoredGui = {
    skipRendering: true,
    formalSystem: initFormalSystem(true).fs,
    deductions: [],
    metarules: [],
    cmd: { cmdBuffer: [], escClear: true, lastDeduction: null, pListMasked: true },
    actionInput: { value: "" },
    hintText: { innerHTML: "" },
    updatePropositionList() {},
    updateDeductionList() {},
    updateMetaRuleList() {}
};
saver.deserialize(restoredGui, encoded);
assert.deepEqual(restoredGui.formalSystem.inferencePages.pages.map(p => p.name), ["主表", "第二表"]);
assert.equal(restoredGui.formalSystem.inferencePages.active.name, "第二表");
assert.equal(restoredGui.formalSystem.inferencePages.page("主表").propositions.length, 1);
assert.equal(restoredGui.formalSystem.inferencePages.active.propositions.length, 1);
assert.deepEqual(restoredGui.formalSystem.inferencePages.active.command.buffer, ["d", "a"]);
assert.deepEqual(restoredGui.cmd.cmdBuffer, ["d", "a"]);
assert.equal(restoredGui.cmd.escClear, false);
assert.equal(restoredGui.cmd.lastDeduction, "a");
assert.equal(restoredGui.actionInput.value, "d");
assert.deepEqual(restoredGui.formalSystem.inferencePages.active.command.state.inferenceProof.history, ["intro h"]);
assert.equal(restoredGui.formalSystem.inferencePages.active.command.state.marker, "preserve-me");

const legacyGui = {
    skipRendering: true,
    formalSystem: initFormalSystem(true).fs,
    deductions: [],
    metarules: [],
    updatePropositionList() {},
    updateDeductionList() {},
    updateMetaRuleList() {}
};
const legacy = JSON.stringify([
    ["{}", "omega", "N"], [], [], 0, 0, 0, 1, [1], 15
]);
// Use the actual old FS payload shape: constants, functions, verbs, meta rules,
// user deductions, visible rule order, and one proposition list.
const oldFs = JSON.stringify({
    version: 1,
    data: [[], [], [], [[]], {}, [], [["True", null]]]
});
saver.deserialize(legacyGui, oldFs);
assert.equal(legacyGui.formalSystem.inferencePages.size, 1);
assert.equal(legacyGui.formalSystem.inferencePages.active.name, "主表");
assert.equal(legacyGui.formalSystem.propositions.length, 1);

assert.throws(
    () => saver.deserialize({
        skipRendering: true,
        formalSystem: initFormalSystem(true).fs,
        deductions: [],
        metarules: [],
        updatePropositionList() {},
        updateDeductionList() {},
        updateMetaRuleList() {}
    }, JSON.stringify({ version: 2, data: [[], [], [], [[]], {}, [], [], { pages: [], activeId: "page-1" }] })),
    /推理表存档格式无效/
);
assert.throws(
    () => saver.deserialize({
        skipRendering: true,
        formalSystem: initFormalSystem(true).fs,
        deductions: [],
        metarules: [],
        updatePropositionList() {},
        updateDeductionList() {},
        updateMetaRuleList() {}
    }, JSON.stringify({ version: 2, data: [[], [], [], [[]], {}, [], [], {
        pages: [{ id: "page-1", name: "主表", propositions: [], command: { input: 1 } }],
        activeId: "page-1"
    }] })),
    /推理表存档格式无效/
);
assert.throws(
    () => saver.deserialize({
        skipRendering: true,
        formalSystem: initFormalSystem(true).fs,
        deductions: [],
        metarules: [],
        updatePropositionList() {},
        updateDeductionList() {},
        updateMetaRuleList() {}
    }, JSON.stringify({ version: 2, data: [[], [], [], [[]], {}, [], [], {
        pages: [{ id: "page-1", name: "主表", propositions: [] }],
        activeId: "missing"
    }] })),
    /推理表存档格式无效/
);

// Invalid JSON/shape is parsed before the live GUI is touched. The active
// assistant/session and renderer flag must survive a rejected import.
{
    const previousFs = initFormalSystem(true).fs;
    let closeCalls = 0;
    const badGui = {
        skipRendering: false,
        formalSystem: previousFs,
        closeInferenceProofAssistant() { closeCalls++; }
    };
    assert.throws(() => saver.deserialize(badGui, "{"));
    assert.equal(closeCalls, 0);
    assert.equal(badGui.formalSystem, previousFs);
    assert.equal(badGui.skipRendering, false);

    assert.throws(() => saver.deserialize(badGui, JSON.stringify({ version: 2, data: [] })));
    assert.equal(closeCalls, 0);
    assert.equal(badGui.formalSystem, previousFs);
    assert.equal(badGui.skipRendering, false);
}

console.log("inference page save/legacy migration regression passed");
