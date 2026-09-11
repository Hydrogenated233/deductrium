import assert from "node:assert/strict";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_", timeout: 30_000, language: "zh"
};
const target = "Πb:Bool,ind_Bool (λb:Bool.U1) U (U→U) b";
for (const restricted of [true, false]) {
    for (const tactic of ["cases", "destruct"]) {
        for (const simplify of [true, false]) {
            const options = {
                disableMultipleApply: restricted,
                disableDestructConds: restricted,
                disableDestructEq: restricted
            };
            const engine = new TTAssistEngine();
            engine.configure(config);
            engine.start(target, options);
            engine.apply("intro b");
            let split = engine.apply(`${tactic} b`);
            if (simplify) split = engine.apply("simpl");
            const first = engine.apply("exact True");
            assert.equal(first.goals.length, 1);
            assert.deepEqual(engine.undo(), split);
            assert.deepEqual(engine.start(target, options, first.history), first);
            engine.apply("simpl");
            engine.apply("intro A");
            assert.equal(engine.apply("exact A").goals.length, 0);
            const qed = engine.qed();
            const saved = JSON.parse(JSON.stringify(qed));
            const fresh = new TTCoreSession();
            fresh.configure(config);
            const result = fresh.validate(0,
                parser.parseSurface(`what := ${saved.proof} : ${saved.theorem}`));
            assert.equal(result.ok, true, result.error);
            assert.equal(result.inferenceComplete, true);
            for (const equality of ["what 0b ≡ True", "what 1b True ≡ True", "what 0b ≡ what 1b True"]) {
                const checked = fresh.validate(1, parser.parseSurface(equality));
                assert.equal(checked.ok, true, checked.error);
            }
        }
    }
}

// Bare U returned by beta/iota computation has the same meaning as U @0,
// without collapsing U0 and U1 or confusing U with the sort of levels.
const engine = new TTAssistEngine();
engine.configure(config);
const options = { disableMultipleApply: true, disableDestructConds: true, disableDestructEq: true };
for (const bad of ["U1", "U@", "U2"]) {
    engine.start(bad, options);
    assert.throws(() => engine.apply("exact True"));
}
engine.start("U1", options);
engine.apply("exact U");
engine.qed();
console.log("issue #47 dependent Bool branches, universes and what gate regression passed");
