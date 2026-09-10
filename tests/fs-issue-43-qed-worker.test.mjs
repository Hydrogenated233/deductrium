import assert from "node:assert/strict";
import { FSGui } from "../js/fs/gui.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { initFormalSystem } from "../js/fs/initial.js";
import { ASTParser } from "../js/fs/astparser.js";
import { expandInferenceSnapshot } from "../js/fs/inference-worker-core.js";
import { InferenceWorkerClient } from "../js/fs/inference-worker-client.js";
import { SavesParser } from "../js/fs/savesparser.js";

const parser = new ASTParser();

// Shared descendants are counted with their multiplicity, but visited once
// per cost search. No machine-specific time limit is needed.
{
    const fs = initFormalSystem(true).fs;
    let reads = 0;
    for (let i = 0; i <= 18; i++) {
        fs.deductions[`cost${i}`] = {
            get steps() {
                reads++;
                return i ? [{ deductionIdx: `cost${i - 1}` }, { deductionIdx: `cost${i - 1}` }] : [];
            }
        };
    }
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assert.equal(assistant.generatedDeductionCost("cost18"), 2 ** 19 - 1);
    assert.ok(reads < 256, `shared DAG cost must not unfold a tree: ${reads}`);
    fs.deductions.cycle = { steps: [{ deductionIdx: "cycle" }] };
    assert.equal(assistant.generatedDeductionCost("cycle"), Infinity);
    assert.equal(assistant.generatedDeductionCost("missing"), Infinity);
    fs.deductions.cost18 = { steps: [] };
    assert.equal(assistant.generatedDeductionCost("cost18"), 1, "no stale cache between searches");
}

const oldDocument = globalThis.document;
const oldWindow = globalThis.window;
const elements = new Map();
globalThis.document = {
    getElementById(id) {
        if (!elements.has(id)) elements.set(id, {
            value: "", textContent: "", innerText: "", disabled: false,
            classList: { add() {}, remove() {} }, replaceChildren() {}, setAttribute() {}
        });
        return elements.get(id);
    }
};
globalThis.window = { setTimeout, clearTimeout };

function makeGui(target = "A>A", history = ["intro h", "exact h"]) {
    const gui = Object.create(FSGui.prototype);
    const fs = initFormalSystem(true).fs;
    fs.fastmetarules = "cvuqe><:#zZQR";
    fs.inferencePages.active.command = { input: "keep-active", buffer: [] };
    const other = fs.inferencePages.create("other");
    other.command = { input: "keep-other", buffer: [], state: { custom: 42 } };
    gui.formalSystem = fs;
    gui.getProps = () => gui.formalSystem.propositions;
    gui.creative = true;
    gui.deductions = Object.keys(fs.deductions);
    gui.metarules = [];
    gui.enableMIFFT_RP = false;
    gui.inferenceProofBusy = false;
    gui.inferenceProofGeneration = 0;
    gui.inferenceProofTextReplayTimer = null;
    gui.inferenceProofScript = history.join("\n");
    gui.inferenceProofPageId = fs.inferencePages.activeId;
    gui.inferenceProofAssistant = new InferenceProofAssistant(fs, target, {
        history, ruleNames: gui.deductions, fastMetaRules: fs.fastmetarules, allowMcpt: false
    });
    gui.inferenceProofSnapshot = gui.inferenceProofAssistant.snapshot();
    gui.hintText = { innerText: "" };
    gui.updatePropositionList = gui.updateDeductionList = gui.onStateChange = () => {};
    gui.renderInferenceProofRecommendations = () => {};
    gui.addToDeductions = name => gui.deductions.push(name);
    gui.inferenceWorkerClient = {
        calls: [],
        expand(payload) {
            return new Promise((resolve, reject) => this.calls.push({ payload, resolve, reject }));
        },
        terminate() {
            for (const call of this.calls) call.reject(new Error("cancelled"));
        }
    };
    return gui;
}

try {
    for (const name of [undefined, "workerIdentity"]) {
        const gui = makeGui();
        const original = gui.formalSystem;
        gui.inferenceProofAssistant.qed = () => { throw new Error("main-thread qed must not run"); };
        const pending = gui.finishInferenceProof(name);
        assert.equal(gui.inferenceProofBusy, true);
        assert.equal(await gui.finishInferenceProof(name), null, "no duplicate commit");
        assert.equal(gui.inferenceWorkerClient.calls.length, 1);
        const call = gui.inferenceWorkerClient.calls[0];
        const response = expandInferenceSnapshot(call.payload);
        assert.equal(original.propositions.length, 0, "worker cannot mutate live rows");
        call.resolve(response);
        assert.equal((await pending).committed, true);
        assert.equal(gui.inferenceProofAssistant, null);
        assert.equal(gui.inferenceProofBusy, false);
        assert.equal(gui.formalSystem.inferencePages.pages[1].command.input, "keep-other");
        if (name) {
            assert.ok(gui.formalSystem.deductions[name]);
            assert.equal(gui.formalSystem.propositions.length, 0);
        } else {
            assert.equal(gui.formalSystem.propositions.length, 1);
            assert.deepEqual(gui.formalSystem.propositions[0].value, parser.parse("A>A"));
        }
    }

    for (const mutate of [
        gui => { gui.formalSystem.propositions.push({ value: parser.parse("B"), from: null }); },
        gui => { gui.formalSystem = initFormalSystem(true).fs; },
        gui => { gui.formalSystem.inferencePages.activate(gui.formalSystem.inferencePages.pages[1].id); },
        gui => { gui.inferenceProofAssistant.undo(); },
        gui => { gui.inferenceProofScript += "\nchanged"; },
        gui => { gui.formalSystem.fastmetarules = ""; },
        gui => { gui.formalSystem.addDeduction("newRule", parser.parse("⊢B"), "test"); }
    ]) {
        const gui = makeGui();
        const pending = gui.finishInferenceProof("stale");
        const call = gui.inferenceWorkerClient.calls[0];
        const response = expandInferenceSnapshot(call.payload);
        mutate(gui);
        const current = gui.formalSystem;
        call.resolve(response);
        assert.equal(await pending, null);
        assert.equal(gui.formalSystem, current);
        assert.equal(gui.formalSystem.deductions.stale, undefined);
        assert.ok(gui.inferenceProofAssistant, "stale result must preserve the draft");
        assert.equal(gui.inferenceProofBusy, false);
    }

    {
        const gui = makeGui();
        const assistant = gui.inferenceProofAssistant;
        const pending = gui.finishInferenceProof("xCancelled");
        assert.equal(gui.inferenceWorkerClient.calls.length, 1);
        gui.closeInferenceProofAssistant();
        assert.equal(await pending, null);
        assert.equal(gui.inferenceProofAssistant, assistant, "Cancel retains the draft");
        assert.equal(gui.inferenceProofBusy, false);
        const retry = gui.finishInferenceProof("retry");
        const call = gui.inferenceWorkerClient.calls.at(-1);
        call.resolve(expandInferenceSnapshot(call.payload));
        assert.equal((await retry).committed, true);
    }

    {
        const gui = makeGui();
        const saves = new SavesParser(true);
        const save = saves.serialize(gui);
        gui.updateMetaRuleList = () => {};
        const pending = gui.finishInferenceProof("xBeforeLoad");
        saves.deserialize(gui, save);
        assert.equal(await pending, null);
        assert.equal(gui.inferenceProofAssistant, null, "loading must discard the old busy assistant");
        assert.equal(gui.inferenceProofBusy, false);
        assert.equal(gui.formalSystem.deductions.xBeforeLoad, undefined);
    }

    // Exercise the real sliced text replay, including cancellation at a yield.
    {
        const oldPerformance = globalThis.performance;
        const yields = [];
        let clock = 0;
        globalThis.performance = { now: () => (clock += 10) };
        globalThis.window = { setTimeout(callback) { yields.push(callback); return 1; }, clearTimeout() {} };
        try {
            const gui = makeGui();
            const original = gui.inferenceProofAssistant;
            gui.inferenceProofTextMode = true;
            elements.get("fs-proof-script").value = "intro h\nexact h";
            const pending = gui.replayInferenceProofText(true);
            assert.equal(yields.length, 1);
            assert.equal(gui.inferenceProofBusy, true);
            gui.closeInferenceProofAssistant();
            yields.shift()();
            await pending;
            assert.equal(gui.inferenceProofAssistant, original);
            assert.equal(gui.inferenceProofBusy, false);
            assert.equal(gui.inferenceWorkerClient.calls.length, 0);
        } finally {
            globalThis.performance = oldPerformance;
            globalThis.window = { setTimeout, clearTimeout };
        }
    }

    {
        const gui = makeGui("#nf($0,x)>(Vy:#nf($0,x))", ["intro h", "intro y", "exact h"]);
        const fs = gui.formalSystem;
        const snapshot = gui.inferenceProofAssistant.snapshot();
        const pending = gui.finishInferenceProof("invalid");
        const call = gui.inferenceWorkerClient.calls[0];
        assert.throws(() => expandInferenceSnapshot(call.payload), /无法确认全称变量/);
        call.reject(new Error("invalid proof"));
        assert.equal(await pending, null);
        assert.equal(gui.formalSystem, fs);
        assert.deepEqual(gui.inferenceProofAssistant.snapshot(), snapshot);
        assert.equal(fs.deductions.invalid, undefined);
    }

    {
        const gui = makeGui();
        const pending = gui.finishInferenceProof("xScope");
        const call = gui.inferenceWorkerClient.calls[0];
        assert.throws(() => expandInferenceSnapshot({
            ...call.payload, fastMetaRules: ""
        }), /条件演绎元定理|未解锁/);
        assert.throws(() => expandInferenceSnapshot({
            ...call.payload,
            target: { ...call.payload.target, ruleNames: ["mp", "a1", "a2"], history: ["exact .i"] }
        }), /作用域|不可用|未解锁/);
        gui.closeInferenceProofAssistant();
        assert.equal(await pending, null);
    }

    {
        const oldWorker = globalThis.Worker;
        const timers = new Map();
        let nextTimer = 0;
        const workers = [];
        globalThis.window = {
            setTimeout(callback) { timers.set(++nextTimer, callback); return nextTimer; },
            clearTimeout(id) { timers.delete(id); }
        };
        globalThis.Worker = class {
            listeners = {};
            messages = [];
            terminated = false;
            constructor() { workers.push(this); }
            addEventListener(name, callback) { this.listeners[name] = callback; }
            postMessage(message) { this.messages.push(message); }
            terminate() { this.terminated = true; }
        };
        try {
            const gui = makeGui();
            const assistant = gui.inferenceProofAssistant;
            gui.formalSystem.disabledMetaRules = ["restricted"];
            gui.inferenceWorkerClient = new InferenceWorkerClient();
            const pending = gui.finishInferenceProof("xTimedOut");
            assert.deepEqual(workers[0].messages[0].payload.disabledMetaRules, ["restricted"]);
            const timeout = [...timers.values()][0];
            timeout();
            assert.equal(await pending, null);
            assert.equal(workers[0].terminated, true);
            assert.equal(gui.inferenceProofAssistant, assistant);
            assert.equal(gui.inferenceProofBusy, false);
            assert.equal(gui.formalSystem.deductions.xTimedOut, undefined);
            const retry = gui.finishInferenceProof("xAfterTimeout");
            const message = workers[1].messages[0];
            workers[1].listeners.message({ data: {
                id: message.id, ok: true, result: expandInferenceSnapshot(message.payload)
            } });
            assert.equal((await retry).committed, true);
            assert.deepEqual(gui.formalSystem.disabledMetaRules, ["restricted"]);
            gui.inferenceWorkerClient.terminate();
            assert.equal(timers.size, 0);

            delete globalThis.Worker;
            const unavailable = makeGui();
            unavailable.inferenceWorkerClient = new InferenceWorkerClient();
            unavailable.inferenceProofAssistant.qed = () => { throw new Error("no synchronous fallback"); };
            assert.equal(await unavailable.finishInferenceProof(), null);
            assert.ok(unavailable.inferenceProofAssistant);
            assert.equal(unavailable.inferenceProofBusy, false);
            assert.match(elements.get("fs-proof-errmsg").innerText, /Worker/);
            assert.match(elements.get("fs-proof-script-error").innerText, /Worker/);
        } finally {
            if (oldWorker === undefined) delete globalThis.Worker;
            else globalThis.Worker = oldWorker;
            globalThis.window = { setTimeout, clearTimeout };
        }
    }
} finally {
    if (oldDocument === undefined) delete globalThis.document;
    else globalThis.document = oldDocument;
    if (oldWindow === undefined) delete globalThis.window;
    else globalThis.window = oldWindow;
}

console.log("GitHub issue #43 qed worker and cost DAG regression passed");
