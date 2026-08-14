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

const invalidLoopElimination =
    "Πa:U,Πx:a,Πy:a,Πp:(x=y),Πq:(x=y),(refl x)=(p*inveq q)";
let snapshot = engine.start(invalidLoopElimination, options);
for (const command of [
    "intro a", "intro x", "intro y", "intro p", "intro q", "destruct q"
]) {
    snapshot = engine.apply(command);
}
assert.equal(snapshot.goals.length, 1);
assert.ok(snapshot.goals[0].context.some(([name]) => name === "q_p"));
assert.throws(
    () => engine.apply("destruct q_p"),
    /无法构造合法的等式归纳目标/,
    "an invalid self-loop motive must be rejected by destruct, not delayed until qed"
);

snapshot = engine.start("Πa:U,Πx:a,Πp:(x=x),p=p", options);
for (const command of ["intro a", "intro x", "intro p", "destruct p", "rfl"]) {
    snapshot = engine.apply(command);
}
assert.equal(snapshot.goals.length, 0);
assert.doesNotThrow(() => engine.qed(),
    "self-loop equalities with a valid fixed-left motive must remain destructible");

console.log("proof-assistant self-loop equality destruct regression passed");
