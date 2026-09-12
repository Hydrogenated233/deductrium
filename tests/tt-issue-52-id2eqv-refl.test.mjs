import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { TTCoreEngine } from "../js/tt/engine.js";
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
const engine = new TTAssistEngine();
engine.configure(config);
const independent = new TTCoreEngine();
independent.configure(config);

function checkExport(result, name) {
    const checked = independent.checkAst(
        parser.parseSurface(`${result.proof}:${result.theorem}`)
    );
    assert.equal(checked.ok, true, checked.error);
    assert.equal(checked.inferenceComplete, true);
    const saved = independent.registerDefinition(
        parser.parseSurface(`${name}:=${result.proof}:${result.theorem}`)
    );
    assert.equal(saved.ok, true, saved.error);
    assert.equal(saved.inferenceComplete, true);
    assert.doesNotMatch(result.proof + result.theorem, /\?nbe\d+/u);
}

const target = "id2eqv (refl Bool)=eqvrefl Bool";
for (const [index, commands] of [["rfl"], ["simpl", "rfl"]].entries()) {
    engine.start(target, options);
    let completed;
    engine.engine.core.withSilentErrors(() => {
        for (const command of commands) completed = engine.apply(command);
    });
    assert.equal(completed.goals.length, 0);
    const exported = engine.qed();
    assert.equal(exported.theorem, parser.stringify(parser.parseSurface(target)));
    checkExport(exported, `id2eqvBool${index}`);
    assert.deepEqual(engine.qed(), exported);
    assert.deepEqual(engine.snapshot(), completed);
    assert.equal(engine.undo().goals.length, 1);
    engine.apply("rfl");
    assert.deepEqual(engine.qed(), exported);
    engine.start(target, options, commands);
    assert.deepEqual(engine.qed(), exported);
}

// Conversion must work in both directions, inside larger terms, and with
// a symbolic universe. It must not depend on Bool or a user definition.
for (const [index, [proposition, commands]] of [
    ["eqvrefl nat=id2eqv (refl nat)", ["rfl"]],
    ["id2eqv (refl True)=eqvrefl True", ["rfl"]],
    ["id2eqv rfl=eqvrefl Bool", ["rfl"]],
    ["@id2eqv @0 Bool Bool (@refl @1 U Bool)=@eqvrefl @0 Bool", ["rfl"]],
    ["Πu:U@,Πa:Uu,id2eqv (refl a)=eqvrefl a", ["intros u a", "rfl"]],
    ["pr0 (id2eqv (refl Bool))=λx:Bool.x", ["rfl"]]
].entries()) {
    engine.start(proposition, options, commands);
    checkExport(engine.qed(), `id2eqvVariant${index}`);
}

// A neutral equality proof has no reflexivity computation. Failed tactics
// must leave the page intact, and malformed exports must still be rejected.
const neutral = engine.start("Πp:Bool=Bool,id2eqv p=eqvrefl Bool", options, ["intro p"]);
engine.engine.core.withSilentErrors(() => assert.throws(() => engine.apply("rfl")));
assert.deepEqual(engine.snapshot(), neutral);
assert.throws(() => engine.qed());
const invalid = independent.core.withSilentErrors(() =>
    independent.checkAst(parser.parseSurface("rfl:(id2eqv (refl Bool)=eqvrefl nat)"))
);
assert.equal(invalid.ok, false);

engine.configure({ ...config, inferDisplayMode: "@" });
engine.start(target, options, ["rfl"]);
checkExport(engine.qed(), "id2eqvExplicitMode");

// A user-defined eliminator exposes the computation result in an argument,
// not at the conversion head. Recreate the same map extraction as the UI.
engine.configure(config);
engine.start("Πa:U,Πb:U,eqv a b→a→b", options,
    ["expand eqv", "intros a b e", "cases e", "exact e0"]);
const map = engine.qed();
const mappedConfig = {
    ...config,
    userDefinitions: [["ttEqvMap", parser.parseSurface(map.proof)]]
};
engine.configure(mappedConfig);
independent.configure(mappedConfig);
for (const [index, proposition] of [
    "ttEqvMap Bool Bool (eqvrefl Bool) 0b=0b",
    "ttEqvMap Bool Bool (id2eqv (refl Bool)) 0b=0b",
    "Πa:U,Πx:a,ttEqvMap a a (id2eqv (refl a)) x=x",
    "ind_Bool (λb:Bool.Bool) 1b 0b (ttEqvMap Bool Bool (id2eqv (refl Bool)) 0b)=1b",
    "ttEqvMap Bool Bool (id2eqv (refl Bool)) (ttEqvMap Bool Bool (id2eqv (refl Bool)) 0b)=0b"
].entries()) {
    engine.start(proposition, options, index === 2 ? ["intros a x", "rfl"] : ["rfl"]);
    checkExport(engine.qed(), `id2eqvMap${index}`);
}
engine.start(
    "Πe:eqv Bool Bool,Πh:id2eqv (refl Bool)=e,0b=ttEqvMap Bool Bool e 0b",
    options,
    ["intros e h", "exact ap (λe:eqv Bool Bool.ttEqvMap Bool Bool e 0b) h"]
);
checkExport(engine.qed(), "id2eqvMapCongruence");
const mappedNeutral = engine.start(
    "Πp:Bool=Bool,ttEqvMap Bool Bool (id2eqv p) 0b=0b", options, ["intro p"]
);
engine.engine.core.withSilentErrors(() => assert.throws(() => engine.apply("rfl")));
assert.deepEqual(engine.snapshot(), mappedNeutral);

console.log("GitHub issue #52 id2eqv reflexivity, qed and independent export regression passed");
