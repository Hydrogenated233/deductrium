import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const session = new TTCoreSession();
session.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 60_000,
    language: "zh"
});

const definition = parser.parse(
    "factorial2:=Lx:nat.pr1 (ind_nat (Lx:nat.natXnat) (1,1) "
    + "(Lx:nat.Lt:natXnat.(pr1 t,mul (succ x)(pr0 t))) x)"
);
const registered = session.validate(0, definition);
assert.equal(registered.ok, true, registered.error);

const core = session.engine.core;
assert.equal(
    core.semanticKernel.tryEqualResult(
        core.desugar(parser.parse("factorial2 9"), false),
        core.desugar(parser.parse("945"), false),
        [],
        { maxSteps: 1_000_000 }
    ),
    "equal",
    "closed natural recursion must not overflow the evaluator stack"
);

const table = [
    1, 1, 2, 3, 8, 15, 48, 105, 384, 945, 3840, 10395, 46080,
    135135, 645120, 2027025, 10321920, 34459425, 185794560,
    654729075, 3715891200, 13749310575, 81749606400, 316234143225,
    1961990553600
];
for (const start of [1, 2]) {
    for (let index = start; index < 25; index += 3) {
        assert.doesNotThrow(
            () => core.checkType(
                parser.parse(`factorial2 ${index} === ${table[index]}`),
                [],
                false
            ),
            `factorial2 puzzle probe ${index} must validate without a false negative`
        );
    }
}

console.log("factorial2 puzzle regression passed");
