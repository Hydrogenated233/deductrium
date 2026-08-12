import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { Core, wrapVar } from "../js/tt/core.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

const registered = engine.registerDefinition(parser.parse("opaqueProbe:=succ 0"));
assert.equal(registered.ok, true, registered.error);
const core = engine.core;
function normalizeAst(ast) {
    return core.checkType({
        type: "whnf",
        name: "",
        nodes: [ast, wrapVar("_")]
    }, [], true);
}

function normalize(source) {
    return normalizeAst(parser.parse(source));
}

assert.equal(parser.stringify(normalize("(λx:nat.succ x) 2")), "3");
    assert.equal(
        parser.stringify(normalize(
            "ind_nat (λx:nat.nat) 0 (λx:nat.λr:nat.succ r) 3"
        )),
        "3"
    );
    assert.equal(
        parser.stringify(normalize("id2eqv rfl")),
        "(eqvrefl _)",
        "a supported id2eqv rule must run before the legacy-compatible `_` rule"
    );
    assert.equal(
        parser.stringify(normalize("opaqueProbe")),
        "opaqueProbe",
        "proof-assistant normalization must keep named definitions opaque"
    );
    assert.equal(
        parser.stringify(normalizeAst({
            type: "apply",
            name: "",
            nodes: [
                {
                    type: "L",
                    name: "g",
                    bondVarId: 777,
                    nodes: [parser.parse("True"), wrapVar("g")]
                },
                parser.parse("true")
            ]
        })),
        "g",
        "repairing orphan IDs must not capture an id-less same-name constant"
    );

console.log("pure NbE proof-assistant normalization regression passed");
