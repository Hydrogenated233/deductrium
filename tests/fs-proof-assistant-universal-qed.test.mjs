import assert from "node:assert/strict";
import { initFormalSystem } from "../js/fs/initial.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { ASTParser } from "../js/fs/astparser.js";

const parser = new ASTParser();
const fs = initFormalSystem(true).fs;
const target = "Vx:(Va:(((x=1)&(a=1))>(x=a)))";
const assistant = new InferenceProofAssistant(fs, target);

for (const command of [
    "intros ha hb hand",
    "obtain <h1,h2> := hand",
    "rw [h1,h2]",
    "rfl"
]) assistant.apply(command);

const result = assistant.qed();
assert.equal(result.committed, true);
assert.equal(fs.propositions.length, 1);
assert.doesNotThrow(() => fs.expandMacroWithProp(0),
    "expanding a deferred proof must restore universal binders introduced by the assistant");
assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), parser.stringifyTight(parser.parse(target)));

// The complete unique-existence example should expand through generated c/v
// macros instead of hundreds of quantified a1/a2/a3/mp primitives.
{
    const fullFs = initFormalSystem(true).fs;
    fullFs.fastmetarules = "cvuqe><:#zZQR";
    fullFs.generateDeduction(":dE!,<.<>2");
    const fullTarget = "E!x:(x=1)";
    const full = new InferenceProofAssistant(fullFs, fullTarget);
    for (const command of [
        "apply :dE!,<.<>2 $21=a",
        "constructor",
        "apply .Erp $2=1",
        "rfl",
        "intros ha hb hand",
        "obtain <h1,h2> := hand",
        "rw [h1,h2]",
        "rfl"
    ]) full.apply(command);
    full.qed();
    fullFs.expandMacroWithProp(0);
    const names = fullFs.propositions.map(proposition => proposition.from?.deductionIdx ?? "");
    assert.ok(names.length < 64, `macro-preserving expansion should stay compact, got ${names.length} rows`);
    assert.ok(names.some(name => /^v+c/.test(name)), "conditional proof steps should retain c-prefixed macros");
    const primitiveCount = names.filter(name => /^(?:v+)?(?:a1|a2|a3|mp)$/.test(name)).length;
    assert.ok(primitiveCount < 20, `primitive Hilbert steps should not dominate expansion, got ${primitiveCount}`);
    assert.equal(parser.stringifyTight(fullFs.propositions.at(-1).value),
        parser.stringifyTight(parser.parse(fullTarget)));
}

// Closed propositional tautologies use one lazy MCPT node even when the user
// entered an explicit tactic proof.
{
    const pureFs = initFormalSystem(true).fs;
    const pure = new InferenceProofAssistant(pureFs, "A>(B>A)");
    pure.apply("intros ha hb");
    pure.apply("exact ha");
    pure.qed();
    pureFs.expandMacroWithProp(0);
    assert.equal(pureFs.propositions.length, 1);
    assert.equal(pureFs.propositions[0].deferredKind, "cpt");
    assert.match(pureFs.propositions[0].from?.deductionIdx ?? "", /^__tauto_/);
}

// Without the MCPT unlock, the same proof falls back to ordinary c-prefixed
// macro materialization and typed `tauto` is rejected.
{
    const fallbackFs = initFormalSystem(true).fs;
    const fallback = new InferenceProofAssistant(fallbackFs, "A>(B>A)", { allowMcpt: false });
    fallback.apply("intros ha hb");
    fallback.apply("exact ha");
    fallback.qed();
    assert.equal(fallbackFs.propositions[0].from?.assistant?.allowMcpt, false);
    fallbackFs.expandMacroWithProp(0);
    assert.equal(fallbackFs.propositions.some(proposition => proposition.deferredKind === "cpt"), false);
    assert.ok(fallbackFs.propositions.some(proposition => /^c/.test(proposition.from?.deductionIdx ?? "")));
    assert.equal(parser.stringifyTight(fallbackFs.propositions.at(-1).value), "A>(B>A)");

    const lockedTauto = new InferenceProofAssistant(initFormalSystem(true).fs, "A>A", { allowMcpt: false });
    assert.throws(() => lockedTauto.apply("tauto"), /未解锁MCPT/);
}

// Existing e-prefixed metatheorem rules remain visible as macro steps.
{
    const existFs = initFormalSystem(true).fs;
    existFs.fastmetarules = "cvuqe><:#zZQR";
    existFs.metaExistTheorem(".&1", "test");
    existFs.addHypothese(parser.parse("Ex:(A&B)"));
    const exist = new InferenceProofAssistant(existFs, "Ex:A");
    exist.apply("apply e.&1");
    exist.apply("exact p0");
    exist.qed();
    existFs.expandMacroWithProp(1);
    assert.ok(existFs.propositions.some(proposition => proposition.from?.deductionIdx === "e.&1"));
}

// Preserve the exact reverse intro order when implication and universal
// binders are interleaved: Vx:(A > Vy:P) is not Vx:Vy:(A > P).
{
    const mixedFs = initFormalSystem(true).fs;
    const mixedTarget = "Vx:(A>(Vy:(x=x)))";
    const mixed = new InferenceProofAssistant(mixedFs, mixedTarget);
    mixed.apply("intros x h y");
    mixed.apply("rfl");
    mixed.qed();
    assert.doesNotThrow(() => mixedFs.expandMacroWithProp(0));
    assert.equal(parser.stringifyTight(mixedFs.propositions.at(-1).value),
        parser.stringifyTight(parser.parse(mixedTarget)));
}

console.log("inference universal-intro qed expansion regression passed");
