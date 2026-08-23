import assert from "node:assert/strict";

import { Assist } from "../js/tt/assist.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { Core } from "../js/tt/core.js";
import { initTypeSystem } from "../js/tt/initial.js";

const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
};
const options = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};
const target = "Πa:U0,Πb:U0,Πc:U0,(a ≃ b)→(b ≃ c)→((a ≃ c))";
const history = [
    "intro a",
    "intro b",
    "intro c",
    "expand eqv",
    "intro ab",
    "intro bc",
    "ex"
];
const continuedHistory = [...history, "intro f"];
const deeperHistory = [
    ...continuedHistory,
    "exact (pr0 bc) ((pr0 ab) f)",
    "case",
    "ex"
];

function createRawEngine() {
    const engine = new TTAssistEngine();
    engine.configure(config);
    // Deliberately use the engine's construction and replay seams directly:
    // snapshot() computes recommendations, whereas this regression must prove
    // that replay is correct without that unrelated side effect.
    engine.options = { ...options };
    engine.targetSource = target;
    engine.createAssist();
    return engine;
}

function executeRaw(engine, command) {
    engine.executeCommand(command, true);
}

const originalLog = console.log;
const originalWarn = console.warn;
const originalAutofill = Assist.prototype.autofillTactics;
try {
    console.log = () => { };
    console.warn = () => { };
    Assist.prototype.autofillTactics = () => {
        throw new Error("history replay must not depend on tactic recommendations");
    };

    const raw = createRawEngine();
    for (const command of continuedHistory) executeRaw(raw, command);
    assert.equal(raw.assist.goal.length, 2,
        "the extended dependent-pair path must execute without a recommendation pass");
    assert.equal(raw.assist.goal[1].type.type, "X");
    assert.ok(
        !raw.assist.goal.some(goal => Core.getFreeVars(goal.type).has("x'")),
        "expanding eqv must not strand the generated x' name as a free variable"
    );

    // Simulate two undo operations by exercising the exact replay helper, but
    // intentionally do not render a snapshot between either replay.  The old
    // bug only disappeared because snapshot() happened to run recommendations.
    raw.replayHistory(continuedHistory.slice(0, -1));
    assert.deepEqual(raw.history, history);
    assert.equal(raw.assist.goal.length, 2,
        "the first undo must restore both dependent-pair goals");
    assert.equal(raw.assist.goal[1].type.type, "X");

    raw.replayHistory(continuedHistory.slice(0, -2));
    assert.deepEqual(raw.history, history.slice(0, -1));
    assert.equal(raw.assist.goal.length, 1,
        "the second undo must restore the equivalence witness goal");
    assert.equal(raw.assist.goal[0].type.type, "S");

    executeRaw(raw, "ex");
    assert.deepEqual(raw.assist.goal.map(goal => goal.type.type), ["->", "X"],
        "the replayed goal must remain usable after the second undo");

    // The real report noted that the bad state can need more proof work before
    // undo exposes it.  Continue through a function witness, its inverse pair,
    // and an existential witness, then replay two later undo points as well.
    const deep = createRawEngine();
    for (const command of deeperHistory) executeRaw(deep, command);
    assert.deepEqual(deep.assist.goal.map(goal => goal.type.type), ["->", "P", "S"],
        "the deeper equivalence construction must execute without a snapshot");

    deep.replayHistory(deeperHistory.slice(0, -1));
    assert.deepEqual(deep.assist.goal.map(goal => goal.type.type), ["S", "S"],
        "undoing the existential witness must restore both inverse witnesses");

    deep.replayHistory(deeperHistory.slice(0, -2));
    assert.deepEqual(deep.assist.goal.map(goal => goal.type.type), ["X"],
        "undoing the pair split must restore the complete inverse pair goal");
    executeRaw(deep, "case");
    assert.deepEqual(deep.assist.goal.map(goal => goal.type.type), ["S", "S"],
        "the deeper replay state must remain usable after both undos");
} finally {
    console.log = originalLog;
    console.warn = originalWarn;
    Assist.prototype.autofillTactics = originalAutofill;
}

console.log("proof-assistant history replay regression passed");
