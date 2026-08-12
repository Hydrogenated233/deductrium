import assert from "node:assert/strict";

import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh",
    userDefinitions: [[
        "zero_add",
        parser.parse(
            "(λx:nat.ind_nat (λx:nat.eq (add 0 x) x) rfl "
            + "(λx:nat.(λx_:((add 0 x)=x).trans "
            + "(λx':nat.((succ x')=(succ x))) (inveq x_) rfl)) x)"
        )
    ]],
    userDefinitionCaches: []
};
const options = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};

const engine = new TTAssistEngine();
engine.configure(config);

const recoveredCache = engine.engine.core.serializeDefinitionCache("zero_add");
assert.equal(recoveredCache?.kind, "nbe",
    "a validated user definition without a transferred cache must rebuild a semantic type cache");

let snapshot = engine.start(
    "Πx:nat,Πy:nat,eq (add x y) (add y x)",
    options
);
for (const command of ["intro x", "intro y", "destruct y", "simpl"]) {
    snapshot = engine.apply(command);
}
snapshot = engine.apply("rw zero_add _");

assert.equal(parser.stringify(snapshot.goals[0].type), "(x=x)",
    "rw zero_add _ must infer its argument after a cacheless definition is restored");

{
    const first = new TTCoreEngine();
    first.configure({ ...config, userDefinitions: [], userDefinitionCaches: [] });
    const firstResult = first.registerDefinition(parser.parse(
        "shadow:=(λx:nat.rfl):(Πx:nat,eq x x)"
    ));
    assert.equal(firstResult.ok, true, firstResult.error);

    const shadowed = new TTCoreEngine();
    shadowed.configure({
        ...config,
        userDefinitions: [
            ["shadow", parser.parse("λx:nat.rfl")],
            ["shadow", parser.parse("λx:Bool.rfl")]
        ],
        userDefinitionCaches: [["shadow", firstResult.definitionCache]]
    });

    assert.equal(shadowed.check("shadow 0b").ok, true,
        "a missing cache on the final shadowing definition must be rebuilt from that definition");
    assert.equal(shadowed.check("shadow 0").ok, false,
        "an earlier same-name cache must not be attached to the final shadowing definition");
}

console.log("cacheless user-definition rewrite regression passed");
