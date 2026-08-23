import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
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

    const mixedEngine = new TTAssistEngine();
    mixedEngine.configure({
        unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
        inferDisplayMode: "_",
        timeout: 30_000,
        language: "zh"
    });
    mixedEngine.start("Πh:(@eq @0 True true true),True~=True", options);
    mixedEngine.apply("intro h");
    const expanded = mixedEngine.apply("expand eqv");
    assert.equal(
        parser.stringify(expanded.goals[0].context[0][1]),
        "(@eq @0 True true true)",
        "expand must retain an explicit @ occurrence inherited from the target"
    );
    const expandedGoal = parser.stringify(expanded.goals[0].type);
    assert.match(expandedGoal, /x=/,
        "expanded equality fields must use the compact public notation");
    assert.doesNotMatch(expandedGoal, /@eq/,
        "an explicit @eq elsewhere must not force generated @eq occurrences to stay expanded");

    const pureEngine = new TTAssistEngine();
    pureEngine.configure({
        unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
        inferDisplayMode: "_",
        timeout: 30_000,
        language: "zh"
    });
    pureEngine.start("Πa:U0,Πb:U0,((LiftU (a ≃ b)) ≃ (a = b))", options);
    pureEngine.apply("intro a");
    pureEngine.apply("intro b");

    assert.doesNotThrow(() => pureEngine["assist"].expand(" eqv"));

    const sumEngine = new TTAssistEngine();
    sumEngine.configure({
        unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
        inferDisplayMode: "_",
        timeout: 30_000,
        language: "zh"
    });
    sumEngine.start("((True+True) ≃ Bool)", options);
    const sumExpanded = sumEngine.apply("expand eqv");
    assert.match(
        parser.stringify(sumExpanded.goals[0].type),
        /^\(Σf:/,
        "expand eqv must normalize a Sum-valued equivalence target instead of failing in WHNF"
    );
} finally {
    console.log = originalLog;
    console.warn = originalWarn;
}

console.log("proof-assistant expand eqv regression passed");
