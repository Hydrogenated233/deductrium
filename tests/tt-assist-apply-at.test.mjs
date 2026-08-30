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

// `apply f at h` consumes h as the first argument and changes its local type.
{
    const engine = new TTAssistEngine();
    engine.configure(config);
    const theorem = "Πp:(True→False),Πh:True,False";
    engine.start(theorem, options);
    engine.apply("intro p");
    engine.apply("intro h");
    const snapshot = engine.apply("apply p at h");
    assert.equal(snapshot.goals.length, 1);
    assert.equal(parser.stringify(snapshot.goals[0].context[0][1]), "False");
    engine.apply("exact h");
    assert.equal(engine.qed().theorem, parser.stringify(parser.parse(theorem)));
}

// Remaining arguments become normal goals and are substituted into the
// resulting local type before the continuation is checked.
{
    const engine = new TTAssistEngine();
    engine.configure(config);
    const theorem = "Πp:(True→True→False),Πh:True,False";
    engine.start(theorem, options);
    engine.apply("intro p");
    engine.apply("intro h");
    const snapshot = engine.apply("apply p at h");
    assert.deepEqual(snapshot.goals.map(goal => parser.stringify(goal.type)), ["True", "False"]);
    engine.apply("exact true");
    engine.apply("exact h");
    assert.equal(engine.qed().theorem, parser.stringify(parser.parse(theorem)));
}

console.log("type-theory apply-at regression passed");

// `specialize h a` applies arguments to a local dependent function fact.
{
    const engine = new TTAssistEngine();
    engine.configure(config);
    const theorem = "Πh:(Πx:True,False),False";
    engine.start(theorem, options);
    engine.apply("intro h");
    const snapshot = engine.apply("specialize h true");
    assert.equal(parser.stringify(snapshot.goals[0].context[0][1]), "False");
    engine.apply("exact h");
    assert.equal(engine.qed().theorem, parser.stringify(parser.parse(theorem)));
}
