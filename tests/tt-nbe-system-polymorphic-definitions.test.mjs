import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
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

for (const source of ["isProp True", "isSet nat"]) {
    const result = engine.core.semanticTypeChecker.trySynthesize(
        parser.parse(source),
        [],
        { elaborateMetas: true, annotateTerm: true }
    );
    assert.equal(result.status, "success",
        `${source} must elaborate through its polymorphic system definition`);
    assert.doesNotMatch(parser.stringify(result.term), /(^|[ (])_([ )]|$)/,
        `${source} must not retain an unresolved definition hole`);
}

const levelPolymorphic = engine.core.semanticTypeChecker.trySynthesize(
    parser.parse("Πu:U@,Πa:Uu,a→a"),
    [],
    { elaborateMetas: true }
);
assert.equal(levelPolymorphic.status, "success",
    "bound universe levels must remain valid in symbolic max/succ expressions");

const propositionApplication = engine.core.semanticTypeChecker.trySynthesize(
    parser.parse("λh:isProp True.λx:True,h x"),
    [],
    { elaborateMetas: true }
);
assert.equal(propositionApplication.status, "success",
    "hole-containing transparent type aliases must expose their function WHNF");

const prepareClosed = source => engine.core.markBondVars(
    engine.core.desugar(parser.parse(source), false),
    []
);
const propositionAssertion = engine.core.semanticTypeChecker.tryCheck(
    prepareClosed("λa:U.λh:(Πx:a,Πy:a,x=y).h"),
    prepareClosed("Πa:U,isProp a→isProp a"),
    [],
    { elaborateMetas: true, annotateTerm: true }
);
assert.equal(propositionAssertion.status, "success",
    "a transparent polymorphic alias must equal its expansion under a Pi binder");

const ispTT = "ispTT:=(λa:U.(λh:(Πx:a,(Πy:a,(x=y))).(λh':a.pair (λf:(a→True).((Σg:(True→a),(Πx:a,(x=(g (f x)))))×(Σh:(True→a),(Πx:True,(x=(f (h x))))))) (λh'':a.true) ((pair (λg:(True→a).(Πx:a,(x=(g true)))) (λh'':True.h') (λx:a.h x h')),((λh'':True.h'),(λx:True.ind_True (λx:True.(x=true)) rfl x)))))):(Πa:U,((isProp a)→(a→(a≃True))))";
assert.doesNotThrow(
    () => engine.core.checkDefinition(parser.parse(ispTT), []),
    "the original ispTT assertion must accept isProp through its transparent definition"
);

let levelContextTerm = engine.core.markBondVars(
    engine.core.desugar(parser.parse("λu:U@.λa:Uu.True"), false),
    []
);
const levelContext = [];
while (levelContextTerm.type === "L") {
    levelContext.unshift([
        levelContextTerm.name,
        levelContextTerm.nodes[0],
        levelContextTerm.bondVarId
    ]);
    levelContextTerm = levelContextTerm.nodes[1];
}
const contextualLevelHole = engine.core.semanticTypeChecker.tryCheck(
    parser.parse("a"),
    parser.parse("U_"),
    levelContext,
    { elaborateMetas: true }
);
assert.equal(contextualLevelHole.status, "success",
    "a universe hole may be solved by a visible U@ binder");

const higherOrderProjection = engine.core.semanticTypeChecker.trySynthesize(
    parser.parse("ap pr0"),
    [],
    {
        elaborateMetas: true,
        generalizeMetas: true,
        annotateTerm: true
    }
);
assert.equal(higherOrderProjection.status, "success",
    "a local elaboration meta with a known Pi type must be usable as a function");

const declaration = parser.parse("semanticIsProp:=isProp True");
const prepared = engine.core.checkDefinition(declaration, []);
assert.equal(prepared.definitionCache?.kind, "nbe",
    "a polymorphic system definition must produce a native semantic cache");
assert.doesNotMatch(parser.stringify(prepared.filledDefinition), /(^|[ (])_([ )]|$)/,
    "the stored definition must contain a fully elaborated proof term");

console.log("polymorphic system-definition NbE regression passed");
