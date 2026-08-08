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

const messages = [];
const originalLog = console.log;
const originalWarn = console.warn;
console.log = (...args) => messages.push(args.join(" "));
console.warn = (...args) => messages.push(args.join(" "));
try {
    engine.start("(base=base)~=Z", options);
    engine.apply("expand eqv");
    engine.apply("ex");
} finally {
    console.log = originalLog;
    console.warn = originalWarn;
}

assert.ok(
    !messages.some(message => message.includes("未知的变量：(%0)")),
    "intermediate dependent proof holes must not be checked as user constants"
);

console.log("proof-assistant intermediate-hole regression passed");
