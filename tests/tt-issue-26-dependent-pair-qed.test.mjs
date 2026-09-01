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

// Issue #26: `ex` must construct dependent Sigma values without routing the
// generated term through the polymorphic `pair` alias.  The latter leaves an
// inconsistent implicit constraint in the dependent second component.
const theorem = "Σf:nat→nat,(eq (f 0) 0)×((n:nat)→eq (f (succ n)) n)";
const commands = [
    "ex ind_nat (Lx:nat.nat) 0 (Lx:nat.LCx:nat.x)",
    "simpl",
    "case",
    "rfl",
    "intro n",
    "rfl"
];

const originalLog = console.log;
try {
    console.log = () => { };
    let snapshot = engine.start(theorem, options);
    for (const command of commands) snapshot = engine.apply(command);
    assert.equal(snapshot.goals.length, 0, "the dependent pair proof should have no remaining goals");
} finally {
    console.log = originalLog;
}

const result = engine.qed();
assert.equal(result.theorem, "(Σf:(nat→nat),((eq (f 0) 0)×(Πn:nat,eq (f (succ n)) n)))");
const checked = engine.engine.check(`${result.proof}:${result.theorem}`);
assert.equal(checked.ok, true, checked.error ?? "issue #26 proof failed Core validation");

console.log("GitHub issue #26 dependent-pair qed regression passed");
