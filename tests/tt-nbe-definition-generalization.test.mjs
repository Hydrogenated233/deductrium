import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    disableSimpleFn: false,
    disableSimpleEq: false,
    inferDisplayMode: "_",
    timeout: Number.MAX_SAFE_INTEGER,
    language: "zh"
};

const session = new TTCoreSession();
session.configure(config);
const checker = session.engine.core.semanticTypeChecker;
const polymorphicRightInjection = parser.parse("La:U,Lx:a,inr x");

assert.equal(
    checker.trySynthesize(polymorphicRightInjection, [], {
        elaborateMetas: true,
        maxSteps: 100_000
    }).status,
    "unsupported",
    "ordinary synthesis must still reject an underconstrained result type"
);

const generalized = checker.trySynthesize(polymorphicRightInjection, [], {
    elaborateMetas: true,
    generalizeMetas: true,
    annotateTerm: true,
    maxSteps: 100_000
});
assert.equal(generalized.status, "success");
assert.equal(generalized.generalizedMetas?.length, 2);
assert.equal(
    parser.stringify(generalized.term),
    parser.stringify(polymorphicRightInjection),
    "hidden @inr parameters must remain compact in the stored definition"
);

checker.setConstantType(
    "@dependentImplicit",
    parser.parse("Πa:U,Πb:a→U,Πx:a,b x")
);
const higherOrderGeneralized = checker.trySynthesize(
    parser.parse("@dependentImplicit _ _"),
    [],
    {
        elaborateMetas: true,
        generalizeMetas: true,
        annotateTerm: true,
        maxSteps: 100_000
    }
);
assert.equal(higherOrderGeneralized.status, "success",
    "definition schemes must generalize safe dependent implicit parameters");
assert.equal(higherOrderGeneralized.generalizedMetas?.length, 2);
assert.equal(
    checker.trySynthesize(parser.parse("λx:True._"), [], {
        elaborateMetas: true,
        generalizeMetas: true,
        annotateTerm: true,
        maxSteps: 100_000
    }).status,
    "unsupported",
    "definition generalization must not accept an unfinished proof body"
);

const definitions = [
    "falseSumF_p:=La:U,ind_Sum (Lz:False+a,a) (Lq:False,ind_False (Lw:False,a) q) (Lx:a,x)",
    "falseSumG_p:=La:U,Lx:a,inr x",
    "falseSumGF_p:=La:U,ind_Sum (Lz:False+a,z=falseSumG_p a (falseSumF_p a z)) (Lq:False,ind_False (Lw:False,(inl w)=falseSumG_p a (falseSumF_p a (inl w))) q) (Lx:a,refl(inr x))",
    "falseSumFG_p:=La:U,Lx:a,refl x",
    "falseSumEqv_p:=La:U,pair (Lf:(False+a)->a,(Sg:a->False+a,Pz:False+a,z=g(f z))X(Sh:a->False+a,Pz:a,z=f(h z))) (falseSumF_p a) ((pair (Lg:a->False+a,Pz:False+a,z=g(falseSumF_p a z)) (falseSumG_p a) (falseSumGF_p a)),(pair (Lh:a->False+a,Pz:a,z=falseSumF_p a (h z)) (falseSumG_p a) (falseSumFG_p a)))"
];

const first = session.validate(0, parser.parse(definitions[0]));
assert.equal(first.ok, true, first.error);
const generalizedDefinition = session.validate(1, parser.parse(definitions[1]));
assert.equal(generalizedDefinition.ok, true, generalizedDefinition.error);
assert.equal(generalizedDefinition.definitionCache.kind, "nbe");
assert.equal(generalizedDefinition.definitionCache.metas.length, 2);
assert.ok(generalizedDefinition.definitionCache.metas.every(meta => meta.expectedType),
    "native generalized metas must retain their expected types");
assert.doesNotMatch(parser.stringify(generalizedDefinition.filledDefinition), /\?nbe|@inr/);

const restored = new TTCoreSession();
restored.configure(config, session.getDefinitionSlots(2));
for (let index = 2; index < definitions.length; index++) {
    const result = restored.validate(index, parser.parse(definitions[index]));
    assert.equal(result.ok, true,
        `restored generalized scheme must preserve theorem ${index}: ${result.error ?? "unknown"}`);
}

const restoredChecker = restored.engine.core.semanticTypeChecker;
assert.equal(
    restoredChecker.trySynthesize(
        parser.parse("falseSumG_p True true"),
        [],
        { elaborateMetas: true, maxSteps: 100_000 }
    ).status,
    "unsupported",
    "a bare use remains underconstrained after scheme restoration"
);
assert.equal(
    restoredChecker.tryCheck(
        parser.parse("falseSumG_p True true"),
        parser.parse("@Sum @0 @0 False True"),
        [],
        { elaborateMetas: true, maxSteps: 100_000 }
    ).status,
    "success",
    "an expected type must instantiate the restored generalized metas"
);

console.log("definition-only semantic meta generalization regression passed");
