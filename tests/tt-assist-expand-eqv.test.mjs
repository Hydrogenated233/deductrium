import assert from "node:assert/strict";

import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const engine = new TTAssistEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

const options = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};

const originalLog = console.log;
const originalWarn = console.warn;
try {
    console.log = () => { };
    console.warn = () => { };
    engine.start("Πa:U0,Πb:U0,((LiftU (a ≃ b)) ≃ (a = b))", options);
    engine.apply("intro a");
    engine.apply("intro b");
    assert.doesNotThrow(() => engine.apply("expand eqv"));
} finally {
    console.log = originalLog;
    console.warn = originalWarn;
}

console.log("proof-assistant expand eqv regression passed");
