import assert from "node:assert/strict";

import { TTAssistEngine } from "../js/tt/assist-engine.js";
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

const engine = new TTAssistEngine();
engine.configure(config);

const originalLog = console.log;
try {
    console.log = () => { };
    let snapshot = engine.start("Πx:S2,(x=x)", options);
    assert.ok(snapshot.tactics.includes("intro x"));
    snapshot = engine.apply("intro x");
    assert.ok(snapshot.tactics.includes("destruct x"));
    snapshot = engine.apply("destruct x");
    assert.equal(snapshot.goals.length, 2);
    snapshot = engine.undo();
    assert.equal(snapshot.goals.length, 1);
    assert.ok(snapshot.tactics.includes("destruct x"));

    snapshot = engine.start("Even 3", options);
    assert.ok(snapshot.tactics.includes("apply evenss _"));

    snapshot = engine.start("Even 0", options);
    snapshot = engine.apply("exact even0");
    assert.equal(snapshot.goals.length, 0);
    const qed = engine.qed();
    assert.equal(qed.theorem, "(Even 0)");
    assert.match(qed.proof, /even0/);

    const equalityCancellation = "Πa:U,Πx:a,Πy:a,Πz:a,Πp:x = y,Πm:y = z,Πn:y = z,(p * m = p * n)→m = n";
    snapshot = engine.start(equalityCancellation, { ...options, disableDestructEq: true });
    for (const command of ["intro a", "intro x", "intro y", "intro z"]) {
        snapshot = engine.apply(command);
    }
    snapshot = engine.apply("intro p");
    assert.ok(!snapshot.tactics.includes("destruct p"), "equality destruct should stay hidden while locked");
    assert.throws(() => engine.apply("destruct p"), /只能解构解锁的归纳类型的变量/);

    snapshot = engine.start(equalityCancellation, options);
    for (const command of ["intro a", "intro x", "intro y", "intro z", "intro p"]) {
        snapshot = engine.apply(command);
    }
    snapshot = engine.apply("destruct p");
    assert.equal(snapshot.goals.length, 1);
} finally {
    console.log = originalLog;
}

console.log("proof-assistant Worker engine regression passed");
