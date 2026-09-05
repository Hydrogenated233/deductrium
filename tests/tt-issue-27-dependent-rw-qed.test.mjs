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
const target =
    "(a:U0)→(b:a→U0)→(c:a→U0)→(m:a)→(n:a)→(p:(m = n))→"
    + "(f:(b m)→(c m))→(trans (λx:a.(b x)→(c x)) p f) = "
    + "(λu:b n.trans (λx:a.c x) p (f (trans (λx:a.b x) (inveq p) u)))";

function configured() {
    const engine = new TTAssistEngine();
    engine.configure(config);
    return engine;
}

const originalLog = console.log;
try {
    console.log = () => { };

    const engine = configured();
    engine.start(target, options);
    for (const command of [
        "intro a", "intro b", "intro c", "intro m", "intro n", "intro p", "intro f"
    ]) engine.apply(command);

    const before = engine.snapshot();
    assert.throws(
        () => engine.apply("rwb p"),
        /函数作用类型不匹配|类型推断暂不支持/,
        "dependent rewrite must reject an ill-typed transport motive before it enters the proof tree"
    );
    const after = engine.snapshot();
    assert.equal(after.goals.length, 1);
    assert.equal(
        parser.stringify(after.goals[0].type),
        parser.stringify(before.goals[0].type),
        "a rejected dependent rewrite must leave the original goal intact"
    );

    const valid = configured();
    valid.start(target, options);
    for (const command of [
        "intro a", "intro b", "intro c", "intro m", "intro n", "intro p", "intro f",
        "destruct p", "rfl"
    ]) valid.apply(command);
    assert.equal(valid.snapshot().goals.length, 0);
    assert.doesNotThrow(() => valid.qed(),
        "direct path induction remains a valid proof of the dependent transport theorem");
} finally {
    console.log = originalLog;
}

console.log("GitHub issue #27 dependent rewrite validation regression passed");
