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

// `rintro` combines introduction with the existing dependent product eliminator.
engine.start("Πh:(True X False),True", options);
let snapshot = engine.apply("rintro ⟨ha,hb⟩");
assert.deepEqual(snapshot.goals[0].context.map(([name]) => name), ["ha", "hb"]);
assert.deepEqual(snapshot.goals[0].context.map(([name, type]) => [name, type.name]), [
    ["ha", "True"],
    ["hb", "False"]
], "rintro pattern names should retain constructor argument order and types");
engine.apply("exact true");
assert.equal(engine.qed().theorem, "(Πh:(True×False),True)");

// `change` and `show` accept only definitionally equal targets and are transactional.
engine.start("Πh:True,True", options);
engine.apply("intro h");
snapshot = engine.apply("change True");
assert.equal(snapshot.goals[0].type.name, "True");
assert.throws(() => engine.apply("show False"), /类型|等价|定义相等/);
assert.equal(engine.apply("show True").goals[0].type.name, "True");
engine.apply("exact true");
engine.qed();

console.log("type-theory rintro/change regression passed");
