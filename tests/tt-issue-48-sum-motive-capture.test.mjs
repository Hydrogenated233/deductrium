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
const target = "ΠA:U,ΠB:U,ΠC:U,((A+B)+C)→(A+(B+C))";
for (const restricted of [true, false]) {
    for (const tactic of ["cases", "destruct"]) {
        for (const name of ["C", "R", "xl", "xr", "x"]) {
            const options = {
                disableMultipleApply: restricted,
                disableDestructConds: restricted,
                disableDestructEq: restricted
            };
            const engine = new TTAssistEngine();
            engine.configure(config);
            engine.start(target, options);
            engine.apply(`intros A B ${name} s`);
            const split = engine.apply(`${tactic} s`);
            assert.equal(parser.stringify(split.goals[1].context.find(([key]) => key === "sr")[1]), name);
            const nested = engine.apply(`${tactic} sl`);
            assert.equal(parser.stringify(nested.goals[2].context.find(([key]) => key === "sr")[1]), name);
            assert.deepEqual(engine.undo(), split);
            assert.deepEqual(engine.start(target, options, nested.history), nested);
            for (const command of ["left", "assumption", "right", "left", "assumption", "right", "right", "assumption"]) {
                engine.apply(command);
            }
            const qed = JSON.parse(JSON.stringify(engine.qed()));
            assert.equal(qed.theorem, parser.stringify(parser.parseSurface(target)));
            const fresh = new TTCoreSession();
            fresh.configure(config);
            for (const prefix of ["", "sumAssoc := "]) {
                const checked = fresh.validate(0,
                    parser.parseSurface(`${prefix}${qed.proof} : ${qed.theorem}`));
                assert.equal(checked.ok, true, `${name}: ${checked.error}`);
                assert.equal(checked.inferenceComplete, true);
            }
        }
    }
}
console.log("issue #48 capture-free Sum motive specialization regression passed");
