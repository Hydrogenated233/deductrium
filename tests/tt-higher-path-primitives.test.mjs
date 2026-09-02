import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const rules = initTypeSystem();
const names = [
    "@trans3", "trans3", "@apd3", "apd3", "@ap3", "ap3",
    "@hit_ap2", "hit_ap2", "@hit_map_transport", "hit_map_transport",
    "@hit_ap2_comp", "hit_ap2_comp", "@hit_ap2_inv", "hit_ap2_inv",
    "@hit_apd2_comp", "hit_apd2_comp", "@hit_apd2_inv", "hit_apd2_inv"
    , "@hit_dep2_comp", "hit_dep2_comp", "@hit_dep2_inv", "hit_dep2_inv"
];
const trustedCoherenceNames = [
    "@hit_ap2_corrected_comp", "@hit_ap2_corrected_inv",
    "@hit_apd2_corrected_comp", "@hit_apd2_corrected_inv"
];
const definitionNames = rules
    .filter(rule => rule.ast.type === ":=")
    .map(rule => rule.ast.nodes[0]?.name)
    .filter(Boolean);

for (const name of names) {
    assert.equal(
        definitionNames.filter(candidate => candidate === name).length,
        1,
        `${name} must be declared exactly once as a transparent definition`
    );
    assert.equal(
        rules.some(rule => rule.ast.type === ":" && rule.ast.nodes[0]?.name === name),
        false,
        `${name} must not also be exposed as a trusted bodyless axiom`
    );
}

for (const name of trustedCoherenceNames) {
    assert.equal(
        definitionNames.includes(name),
        false,
        `${name} is a dimension-specific coherence primitive, not a transparent alias`
    );
    assert.equal(
        rules.filter(rule => rule.ast.type === ":" && rule.ast.nodes[0]?.name === name).length,
        1,
        `${name} must be declared exactly once as a trusted coherence primitive`
    );
}

const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: [...new Set(rules.map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

for (const name of [...names, ...trustedCoherenceNames]) {
    if (names.includes(name)) {
        const definition = engine.core.state.sysDefs[name];
        assert.ok(definition, `missing system definition ${name}`);
        assert.equal(
            definition.type === "var" && definition.name === name,
            false,
            `${name} must retain an executable definition body`
        );
    }
    const synthesized = engine.core.semanticTypeChecker.trySynthesize(
        parser.parse(name),
        [],
        {
            elaborateMetas: true,
            generalizeMetas: true,
            annotateTerm: true,
            maxSteps: 300_000
        }
    );
    assert.equal(
        synthesized.status,
        "success",
        `${name} must be registered in the semantic checker`
    );
}

for (const source of [
    "trans3 (λ_:True.True) (refl (refl (refl true))) true "
        + "=== refl (trans2 (λ_:True.True) (refl (refl true)) true)",
    "apd3 (λx:True.x) (refl (refl (refl true))) "
        + "=== refl (apd2 (λx:True.x) (refl (refl true)))",
    "ap3 (λx:True.x) (refl (refl (refl true))) "
        + "=== refl (ap (λp:true=true.ap (λx:True.x) p) (refl (refl true)))",
    "@hit_ap2 _ _ True True true true (refl true) (refl true) "
        + "(λx:True.x) (refl (refl true)) === refl (refl true)",
    "hit_ap2 (λx:True.x) (refl (refl true)) === refl (refl true)",
    "hit_map_transport (λz:True.λh:True.h) true true rfl true true rfl === rfl",
    "hit_ap2_comp (λx:True.x) (refl (refl true)) (refl (refl true)) === rfl",
    "hit_ap2_inv (λx:True.x) (refl (refl true)) === rfl",
    "hit_apd2_comp (λx:True.x) (refl (refl true)) (refl (refl true)) rfl rfl === rfl",
    "hit_apd2_inv (λx:True.x) (refl (refl true)) rfl === rfl",
    "@hit_dep2_comp _ _ True true true "
        + "(refl true) (refl true) (refl true) "
        + "(λ_:True.True) true true rfl rfl rfl "
        + "(refl (refl true)) (refl (refl true)) rfl rfl === rfl",
    "@hit_dep2_inv _ _ True true true "
        + "(refl true) (refl true) (λ_:True.True) true true "
        + "rfl rfl (refl (refl true)) rfl === rfl"
]) {
    const result = engine.check(source);
    assert.equal(result.ok, true, result.error ?? source);
}

for (const source of [
    "@hit_ap2_corrected_comp @0 @0 True True true true "
        + "(refl true) (refl true) (refl true) (λx:True.x) "
        + "(refl true) (refl true) (refl true) "
        + "(refl (refl true)) (refl (refl true)) rfl rfl rfl rfl rfl rfl rfl",
    "@hit_ap2_corrected_inv @0 @0 True True true true "
        + "(refl true) (refl true) (λx:True.x) (refl true) (refl true) "
        + "(refl (refl true)) rfl rfl rfl rfl",
    "@hit_apd2_corrected_comp @0 @0 True true true "
        + "(refl true) (refl true) (refl true) (λ_:True.True) (λx:True.x) "
        + "(refl true) (refl true) (refl true) "
        + "(refl (refl true)) (refl (refl true)) rfl rfl rfl rfl rfl rfl rfl",
    "@hit_apd2_corrected_inv @0 @0 True true true "
        + "(refl true) (refl true) (λ_:True.True) (λx:True.x) "
        + "(refl true) (refl true) (refl (refl true)) rfl rfl rfl rfl"
]) {
    const synthesized = engine.core.semanticTypeChecker.trySynthesize(
        parser.parse(source),
        [],
        {
            elaborateMetas: true,
            annotateTerm: true,
            maxSteps: 300_000
        }
    );
    assert.equal(synthesized.status, "success", source);
}

console.log("transparent third-order path primitive regression passed");
