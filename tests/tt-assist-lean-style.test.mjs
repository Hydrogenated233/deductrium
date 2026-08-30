import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
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

// Lean aliases for assumptions and simplification close ordinary goals.
{
    const engine = new TTAssistEngine();
    engine.configure(config);
    engine.start("Πh:True,True", options);
    engine.apply("intro h");
    engine.apply("assumption");
    assert.equal(engine.qed().theorem, "(Πh:True,True)");
}

{
    const engine = new TTAssistEngine();
    engine.configure(config);
    engine.start("Πh:True,True", options);
    engine.apply("intro h");
    engine.apply("simpa using h");
    assert.equal(engine.qed().theorem, "(Πh:True,True)");
}

// `constructor` maps to the product constructor and leaves two goals.
{
    const engine = new TTAssistEngine();
    engine.configure(config);
    let snapshot = engine.start("True X True", options);
    snapshot = engine.apply("constructor");
    assert.equal(snapshot.goals.length, 2);
    snapshot = engine.apply("exact true");
    snapshot = engine.apply("exact true");
    assert.equal(snapshot.goals.length, 0);
}

// `cases`/`rcases` are aliases for the existing dependent eliminator.
{
    const engine = new TTAssistEngine();
    engine.configure(config);
    engine.start("Πb:Bool,b=b", options);
    const cases = engine.apply("intro b");
    assert.ok(cases.tactics.includes("cases b") === false,
        "type-theory recommendations remain canonical while aliases stay accepted");
    const split = engine.apply("rcases b");
    assert.equal(split.goals.length, 2);
}

// Lean list rewrite syntax applies each equality in order.
{
    const engine = new TTAssistEngine();
    engine.configure(config);
    engine.start("Πx:nat,Πp:x=0,x=0", options);
    engine.apply("intro x");
    engine.apply("intro p");
    const rewritten = engine.apply("rw [p]");
    assert.equal(parser.stringify(rewritten.goals[0].type), "(0=0)");
}

console.log("type-theory Lean-style strategy regression passed");
