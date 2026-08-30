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

let snapshot = engine.start("Px:nat.Py:nat.eq (add x y) (add y x)", options);
snapshot = engine.apply("intro x");
snapshot = engine.apply("intro y");
snapshot = engine.apply("induction y with d dh");

assert.equal(snapshot.goals.length, 2);
assert.deepEqual(snapshot.goals[0].context.map(([name]) => name), ["x"]);
assert.deepEqual(snapshot.goals[1].context.map(([name]) => name), ["dh", "d", "x"]);
assert.equal(snapshot.goals[1].context.some(([name]) => name === "y"), false);
assert.equal(snapshot.goals[1].context.some(([name]) => name === "y_"), false);
assert.match(parser.stringify(snapshot.goals[1].context.find(([name]) => name === "d")[1]), /nat/);
assert.deepEqual(snapshot.history, ["intro x", "intro y", "induction y with d dh"]);

snapshot = engine.undo();
assert.deepEqual(snapshot.goals[0].context.map(([name]) => name), ["y", "x"]);
snapshot = engine.apply("induction y with d dh");
assert.deepEqual(snapshot.goals[1].context.map(([name]) => name), ["dh", "d", "x"],
    "induction names must survive replay after undo/reapply");

const collisionEngine = new TTAssistEngine();
collisionEngine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});
let collision = collisionEngine.start("Pd:nat.Pn:nat.eq n n", options);
collision = collisionEngine.apply("intro d");
collision = collisionEngine.apply("intro n");
assert.throws(() => collisionEngine.apply("induction n with d dh"), /induction分支名称已存在：d/);
assert.deepEqual(collisionEngine.apply("induction n with pred ih").goals[1].context.map(([name]) => name),
    ["ih", "pred", "d"], "failed induction naming must roll back the session");

console.log("Lean-style induction naming regression passed");
