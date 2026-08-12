import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";
import { SemanticNbeTypeChecker } from "../js/tt/nbe-checker.js";
import { SemanticNbeKernel } from "../js/tt/nbe-kernel.js";

const parser = new ASTParser();
const kernel = new SemanticNbeKernel();
const checker = new SemanticNbeTypeChecker(kernel);

checker.replaceConstantTypes([
    ["A", parser.parse("U")],
    ["B", parser.parse("U")],
    ["a", parser.parse("A")],
    ["b", parser.parse("B")],
    ["f", parser.parse("Px:A,B")],
    ["F", parser.parse("A->U")],
    ["dep", parser.parse("Px:A,F x")],
    ["nat", parser.parse("U")],
    ["False", parser.parse("U")],
    ["True", parser.parse("U")],
    ["true", parser.parse("True")]
]);
checker.setConstantType("@max", parser.parse("U@->U@->U@"));
checker.setConstantType("@Sum", parser.parse("Pu:U@,Pv:U@,Uu->Uv->U(@max u v)"));
checker.setConstantType("polyUniverse", parser.parse("PC:U?0,C"));
checker.setConstantType("identityScheme", parser.parse("Px:?0,?0"));

function synthesized(source, context = []) {
    const result = checker.trySynthesize(parser.parse(source), context);
    assert.equal(result.status, "success", `${source}: ${result.code ?? "unknown failure"}`);
    return result.type;
}

assert.equal(parser.stringify(synthesized("A")), "U");
assert.equal(parser.stringify(synthesized("a")), "A");
assert.equal(parser.stringify(synthesized("Lx:A.x")), parser.stringify(parser.parse("Px:A,A")));
assert.equal(parser.stringify(synthesized("f a")), "B");
{
    const directKernel = new SemanticNbeKernel();
    const directChecker = new SemanticNbeTypeChecker(directKernel);
    directChecker.replaceConstantTypes([
        ["A", parser.parse("U")],
        ["B", parser.parse("U")],
        ["a", parser.parse("A")],
        ["f", parser.parse("Px:A,B")]
    ]);
    let syntacticFunctionWhnfCalls = 0;
    const originalTryWhnf = directKernel.tryWhnf;
    directKernel.tryWhnf = function countedTryWhnf(...args) {
        if (args[0]?.type === "P" || args[0]?.type === "->") {
            syntacticFunctionWhnfCalls++;
        }
        return originalTryWhnf.call(this, ...args);
    };
    const result = directChecker.trySynthesize(parser.parse("f a"), [], {
        elaborateMetas: false
    });
    assert.equal(result.status, "success");
    assert.equal(parser.stringify(result.type), "B");
    assert.equal(syntacticFunctionWhnfCalls, 0,
        "an already syntactic function type must not enter semantic WHNF");
}
assert.equal(parser.stringify(synthesized("dep a")), parser.stringify(parser.parse("F a")),
    "dependent application must substitute its argument into the codomain");
{
    const source = parser.parse("@Sum _ _ A B");
    const before = parser.stringify(source);
    const result = checker.trySynthesize(source);
    assert.equal(result.status, "success");
    assert.equal(parser.stringify(result.type), "U");
    assert.equal(parser.stringify(result.term), parser.stringify(parser.parse("@Sum @0 @0 A B")),
        "later type arguments must solve earlier implicit universe holes without mutating the source");
    assert.equal(parser.stringify(source), before,
        "local elaboration must keep the caller-owned source AST immutable");
}
assert.equal(parser.stringify(synthesized("polyUniverse A")), "A",
    "generalized metas in a cached constant type must be freshened and solved per use");
assert.equal(checker.trySynthesize(parser.parse("@Sum _ _ A")).status, "unsupported",
    "an implicit hole that is not uniquely constrained must stay on the legacy elaborator path");
assert.equal(
    checker.trySynthesize(parser.parse("La:U,Lx:a,identityScheme x")).status,
    "unsupported",
    "a cache meta created outside a binder must not capture that later local binder"
);
assert.equal(checker.trySynthesize(parser.parse("identityScheme true")).status, "unsupported",
    "general type metas must wait for full cached expected-type constraints");
{
    assert.equal(checker.setConstantSchemeSnapshot("typedPreset", {
        type: parser.parse("Px:?0,?0"),
        metas: [
            { name: "?0" },
            {
                name: "?1",
                expectedType: parser.parse("?0"),
                preset: parser.parse("true")
            }
        ]
    }), true);
    const result = checker.trySynthesize(parser.parse("typedPreset true"));
    assert.equal(result.status, "success",
        "a meta used as another term meta's expected type must accept a concrete type");
    assert.equal(parser.stringify(result.type), "True");
}
assert.equal(parser.stringify(synthesized("Px:A,B")), "U");
assert.equal(parser.stringify(synthesized("Sx:A,B")), "U");
assert.equal(parser.stringify(synthesized("Wx:A,B")), "U");

{
    const universe = synthesized("U");
    assert.equal(universe.type, "apply");
    assert.equal(universe.nodes[0].name, "U");
    assert.equal(universe.nodes[1].name, "@1");
    assert.equal(parser.stringify(synthesized("U@0")), parser.stringify(universe));
}

{
    const contextType = parser.parse("A");
    const variable = parser.parse("x");
    variable.bondVarId = 7;
    assert.equal(
        parser.stringify(checker.trySynthesize(variable, [["x", contextType, 7]]).type),
        "A"
    );
}

{
    const source = parser.parse("Lx:A.x");
    assert.equal(source.bondVarId, undefined);
    assert.equal(source.nodes[1].bondVarId, undefined);
    assert.equal(checker.trySynthesize(source).status, "success");
    assert.equal(source.bondVarId, undefined,
        "pure synthesis must not annotate the source binder");
    assert.equal(source.nodes[1].bondVarId, undefined,
        "pure synthesis must not annotate source variable references");
    assert.equal(source.checked, undefined);
}

assert.equal(checker.tryCheck(parser.parse("a"), parser.parse("A")).status, "success");
{
    let semanticEqualityCalls = 0;
    const originalTryEqualResult = kernel.tryEqualResult;
    kernel.tryEqualResult = function countedTryEqualResult(...args) {
        semanticEqualityCalls++;
        return originalTryEqualResult.call(this, ...args);
    };
    try {
        assert.equal(checker.tryCheck(parser.parse("a"), parser.parse("A")).status, "success");
        assert.equal(semanticEqualityCalls, 0,
            "strictly identical inferred and expected types must not enter semantic conversion");
    } finally {
        kernel.tryEqualResult = originalTryEqualResult;
    }
}
{
    const directKernel = new SemanticNbeKernel();
    const directChecker = new SemanticNbeTypeChecker(directKernel);
    directChecker.setConstantType("A", parser.parse("U"));
    let whnfCalls = 0;
    const originalTryWhnf = directKernel.tryWhnf;
    directKernel.tryWhnf = function countedTryWhnf(...args) {
        whnfCalls++;
        return originalTryWhnf.call(this, ...args);
    };
    const result = directChecker.trySynthesize(parser.parse("Px:A,A"), [], {
        elaborateMetas: false
    });
    assert.equal(result.status, "success");
    assert.equal(whnfCalls, 0,
        "a rigid universe type must not be normalized again just to read its level");
}
assert.deepEqual(
    checker.tryCheck(parser.parse("a"), parser.parse("B")),
    { status: "invalid", code: "type-mismatch" }
);
assert.deepEqual(
    checker.trySynthesize(parser.parse("f b")),
    { status: "invalid", code: "argument-type-mismatch" }
);
assert.deepEqual(
    checker.trySynthesize(parser.parse("missing")),
    { status: "invalid", code: "unknown-constant" }
);
assert.deepEqual(
    checker.trySynthesize(parser.parse("?m")),
    { status: "unsupported", code: "metavariable" }
);
assert.deepEqual(
    checker.trySynthesize(parser.parse("Lx:a.x")),
    { status: "invalid", code: "expected-universe" }
);

assert.equal(kernel.setDefinition("FnType", parser.parse("Px:A,B")), true);
checker.setConstantType("g", parser.parse("FnType"));
assert.equal(parser.stringify(synthesized("g a")), "B",
    "function types may delta-unfold through the shared semantic kernel");

{
    const cachedType = parser.parse("Pf:A,Pg:F f,G f g");
    cachedType.bondVarId = 41;
    cachedType.nodes[1].bondVarId = 42;
    cachedType.nodes[1].nodes[0].nodes[1].bondVarId = 41;
    cachedType.nodes[1].nodes[1].nodes[0].nodes[1].bondVarId = 41;
    cachedType.nodes[1].nodes[1].nodes[1].bondVarId = 42;
    checker.setConstantType("cachedDependent", cachedType);

    const collisionContext = [
        ["currentG", parser.parse("B"), 42],
        ["currentF", parser.parse("A"), 41]
    ];
    const result = checker.trySynthesize(parser.parse("cachedDependent"), collisionContext);
    assert.equal(result.status, "success");
    const freshType = result.type;
    const freshF = freshType.bondVarId;
    const freshG = freshType.nodes[1].bondVarId;
    assert.ok(freshF > 42 && freshG > 42 && freshF !== freshG,
        "cached constant binders must be freshened away from the current checking context");
    assert.equal(freshType.nodes[1].nodes[0].nodes[1].bondVarId, freshF,
        "dependent binder domains must keep referring to the fresh outer binder");
    assert.equal(freshType.nodes[1].nodes[1].nodes[0].nodes[1].bondVarId, freshF);
    assert.equal(freshType.nodes[1].nodes[1].nodes[1].bondVarId, freshG,
        "the result type must keep referring to the fresh inner binder");
}

{
    const reversedSourceIds = parser.parse("Px:A,Py:A,x");
    reversedSourceIds.bondVarId = 2;
    reversedSourceIds.nodes[1].bondVarId = 1;
    reversedSourceIds.nodes[1].nodes[1].bondVarId = 2;
    checker.setConstantType("reversedSourceIds", reversedSourceIds);

    const applied = checker.trySynthesize(parser.parse("reversedSourceIds a"));
    assert.equal(applied.status, "success");
    assert.equal(applied.type.type, "P");
    assert.equal(applied.type.nodes[1].name, "a",
        "fresh binder ids must not capture an outer reference whose source id matches an inner fresh id");
    assert.equal(applied.type.nodes[1].bondVarId, undefined);
}

{
    const levelType = checker.trySynthesize(
        parser.parse("@max @0 @0"),
        [["U@", null, Infinity]]
    );
    assert.equal(levelType.status, "success");
    assert.equal(levelType.type.name, "U@");
    assert.equal(levelType.type.bondVarId, undefined,
        "the universe-level sentinel context must never be quoted as a finite local binder");
}

{
    const sourceCore = new Core();
    const contextualType = sourceCore.markBondVars(
        sourceCore.desugar(parser.parse("Pa:U,Px:a,@Sum ?0 ?0 ?2 a"), false),
        []
    );
    assert.equal(
        checker.setConstantSchemeSnapshot("falseSumContextual", {
            type: contextualType,
            metas: [
                { name: "?0" },
                { name: "?2", expectedType: parser.parse("U?0") }
            ]
        }),
        true,
        "a creation context may be erased when no scheme constraint actually references it"
    );
    assert.equal(
        checker.tryCheck(
            parser.parse("falseSumContextual True true"),
            parser.parse("@Sum @0 @0 False True")
        ).status,
        "success"
    );
    assert.equal(
        checker.tryCheck(
            parser.parse("falseSumContextual"),
            parser.parse("Pa:U,Px:a,@Sum @0 @0 False a")
        ).status,
        "success"
    );
    assert.notEqual(
        checker.tryCheck(
            parser.parse("falseSumContextual"),
            parser.parse("Pa:U,Px:a,@Sum @0 @0 a a")
        ).status,
        "success",
        "an erased contextual meta must not capture binders introduced inside its own scheme"
    );

    assert.equal(
        checker.setConstantSchemeSnapshot("unclosedNativeScheme", {
            type: parser.parse("?2"),
            metas: [{ name: "?2", expectedType: parser.parse("U?0") }]
        }),
        false,
        "a native scheme must reject constraints that reference an undeclared meta"
    );

    assert.equal(
        checker.setConstantSchemeSnapshot("sentinelContextual", {
            type: parser.parse("U?0"),
            metas: [{ name: "?0", expectedType: parser.parse("U@") }]
        }),
        true,
        "the universe sentinel is not a capturable source binder"
    );
}

{
    const sourceCore = new Core();
    const captureKernel = new SemanticNbeKernel();
    const captureChecker = new SemanticNbeTypeChecker(captureKernel);
    captureChecker.setConstantType("A", parser.parse("U"));
    captureChecker.setConstantType("g", parser.parse("A->A"));
    const schemeType = sourceCore.markBondVars(
        parser.parse("Pf:(?0->?0),Pg:(?0->?0),Px:?0,@eq @0 ?0 (f x) (g x)"),
        []
    );
    assert.equal(captureChecker.setConstantSchemeSnapshot("composeLike", {
        type: schemeType,
        metas: [{ name: "?0", expectedType: parser.parse("U") }]
    }), true);
    const partial = captureChecker.trySynthesize(
        parser.parse("composeLike g"),
        [],
        { elaborateMetas: false, maxSteps: 100_000 }
    );
    assert.equal(partial.status, "success",
        "recursive checking must instantiate a compiled constant scheme without enabling input holes");
    const gIds = [];
    const collectG = ast => {
        if (ast.type === "var" && ast.name === "g") gIds.push(ast.bondVarId);
        for (const child of ast.nodes ?? []) collectG(child);
    };
    collectG(partial.type);
    assert.equal(gIds.filter(id => id === undefined).length, 1,
        "a substituted global constant must remain free below a later same-name scheme binder");
    assert.equal(gIds.filter(id => id === partial.type.bondVarId).length, 1,
        "the original scheme variable must remain bound after capture avoidance");
}

{
    const engine = new TTCoreEngine();
    engine.configure({
        unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
        inferDisplayMode: "_",
        timeout: 30_000,
        language: "zh"
    });
    const schemeChecker = engine.core.semanticTypeChecker;
    const options = { elaborateMetas: true, maxSteps: 100_000 };
    const explicitEqvRefl = schemeChecker.trySynthesize(
        parser.parse("@eqvrefl @0 True"),
        [],
        options
    );
    assert.equal(explicitEqvRefl.status, "success",
        "legacy U@: universe sentinels must remain valid semantic binder domains");
    assert.equal(
        schemeChecker.tryCheck(
            parser.parse("@eqvrefl @0 True"),
            parser.parse("eqv True True"),
            [],
            options
        ).status,
        "success",
        "the explicit equivalence reflexivity term must synthesize eqv True True"
    );
    const equalityType = schemeChecker.trySynthesize(parser.parse("eq true true"), [], options);
    assert.equal(equalityType.status, "success");
    assert.equal(parser.stringify(equalityType.type), "U");
    const dependentUniverse = schemeChecker.trySynthesize(
        parser.parse("@ind_nat @1 (Lx:nat,U) False (Ln:nat,Lh:U,@Sum @0 @0 h True) n"),
        [["n", parser.parse("nat"), 900001]],
        options
    );
    assert.equal(dependentUniverse.status, "success");
    assert.equal(parser.stringify(dependentUniverse.type), "U",
        "dependent application result types must beta-reduce before returning to the legacy checker");
    for (const name of ["@inl", "@inr", "@ind_Sum"]) {
        const explicitSumPrimitive = schemeChecker.trySynthesize(
            parser.parse(name),
            [],
            options
        );
        assert.equal(explicitSumPrimitive.status, "success",
            `${name} must not retain independent surface-syntax holes`);
    }
    assert.equal(
        schemeChecker.tryCheck(
            parser.parse("refl true"),
            parser.parse("@eq @0 True true true"),
            [],
            options
        ).status,
        "success"
    );
    assert.equal(
        schemeChecker.tryCheck(
            parser.parse("rfl"),
            parser.parse("@eq @0 True true true"),
            [],
            options
        ).status,
        "success"
    );
    assert.deepEqual(
        schemeChecker.tryCheck(
            parser.parse("rfl"),
            parser.parse("@eq @0 True true false"),
            [],
            options
        ),
        { status: "invalid", code: "type-mismatch" }
    );
    assert.equal(
        schemeChecker.tryCheck(
            parser.parse("@refl @0 (@eq @0 True true true) (@refl @0 True true)"),
            parser.parse("@eq @0 (@eq @0 True true true) rfl (@refl @0 True true)"),
            [],
            options
        ).status,
        "success",
        "conversion must constrain a bare implicit alias from the explicit opposite side"
    );
    schemeChecker.setConstantType("opaquePath", parser.parse("eq opaqueEndpoint true"));
    const opaqueInverse = schemeChecker.trySynthesize(
        parser.parse("inveq opaquePath"),
        [],
        options
    );
    assert.equal(opaqueInverse.status, "success",
        "an endpoint already trusted through a synthesized path type must not be re-synthesized");
    assert.equal(
        parser.stringify(opaqueInverse.type),
        parser.stringify(parser.parse("eq true opaqueEndpoint"))
    );
    assert.equal(
        parser.stringify(opaqueInverse.elaboratedTerm),
        parser.stringify(parser.parse("@inveq @0 True opaqueEndpoint true opaquePath")),
        "public type compaction must not rewrite the explicit kernel-ready term"
    );
    schemeChecker.setConstantType(
        "opaqueTypedPath",
        parser.parse("@eq @0 opaqueType opaqueEndpoint opaqueEndpoint")
    );
    assert.notEqual(
        schemeChecker.trySynthesize(parser.parse("inveq opaqueTypedPath"), [], options).status,
        "success",
        "synthesized-type provenance must not bypass validation of an implicit type meta"
    );
    schemeChecker.setConstantType("badPath", parser.parse("@eq @0 True 0 true"));
    assert.notEqual(
        schemeChecker.trySynthesize(parser.parse("inveq badPath"), [], options).status,
        "success",
        "synthesized-type provenance must not override an explicit endpoint type mismatch"
    );
    assert.equal(schemeChecker.trySynthesize(parser.parse("nil"), [], options).status, "unsupported");
    assert.equal(
        schemeChecker.tryCheck(parser.parse("nil"), parser.parse("List False"), [], options).status,
        "success"
    );
    assert.equal(
        schemeChecker.tryCheck(
            parser.parse("inl true"),
            parser.parse("@Sum @0 @0 True False"),
            [],
            options
        ).status,
        "success"
    );
    const sigmaContext = [
        ["m", parser.parse("Sx:a,b x"), 3],
        ["b", parser.parse("a->U"), 2],
        ["a", parser.parse("U"), 1]
    ];
    const projected = schemeChecker.trySynthesize(
        parser.parse("pr0 m"),
        sigmaContext,
        { elaborateMetas: false, maxSteps: 100_000 }
    );
    assert.equal(projected.status, "success",
        "compiled schemes must elaborate their own universe holes during recursive checking");
    assert.equal(parser.stringify(projected.type), "a");
    const pairType = schemeChecker.trySynthesize(
        parser.parse("pair (Lx:True,True) true true"),
        [],
        options
    );
    assert.equal(pairType.status, "success");
    assert.equal(parser.stringify(pairType.type), parser.stringify(parser.parse("Sx:True,True")));
    const rightUnit = engine.core.markBondVars(engine.core.desugar(Core.clone(parser.parse(
        "La:U,Lx:a,Ly:a,Lp:eq x y,ind_eq x "
        + "(Lz:a,Lq:eq x z,eq (q*(refl z)) q) (refl (refl x)) y p"
    )), false), []);
    assert.equal(
        schemeChecker.trySynthesize(rightUnit, [], options).status,
        "success",
        "nested uses of a non-recursive implicit alias must elaborate independently"
    );

    Core.semanticTypeCheckFastPathHits = 0;
    for (const source of [
        "rfl:(true=true)",
        "refl true:(true=true)",
        "nil:List False",
        "inl true:(True+False)",
        "inr true:(False+True)",
        "cons true nil:List True",
        "(true,true):(True X True)"
    ]) {
        engine.core.checkType(parser.parse(source), [], false);
    }
    assert.equal(Core.semanticTypeCheckFastPathHits, 7);
    assert.throws(
        () => engine.core.checkType(parser.parse("(true,0):(True X True)"), [], false),
        "pair elaboration must still reject a component with the wrong type"
    );
}

{
    const core = new Core();
    core.state.sysTypes.A = parser.parse("U");
    core.state.sysTypes.B = parser.parse("U");
    core.state.sysTypes.a = parser.parse("A");
    core.state.sysTypes.f = parser.parse("Px:A,B");
    core.state.sysTypes["@Sum"] = parser.parse("Pu:U@,Pv:U@,Uu->Uv->U(@max u v)");
    assert.ok(core.syncSemanticTypes() >= 5);
    assert.equal(
        parser.stringify(core.semanticTypeChecker.trySynthesize(parser.parse("a")).type),
        "A",
        "Core system types must populate the immutable checker environment"
    );
    Core.semanticTypeCheckAttempts = 0;
    Core.semanticTypeCheckHits = 0;
    Core.semanticTypeCheckFastPathHits = 0;
    assert.equal(parser.stringify(core.checkType(parser.parse("a"), [], false)), "A");
    assert.equal(
        parser.stringify(core.checkType(parser.parse("Lx:A.x"), [], false)),
        parser.stringify(parser.parse("A->A")),
        "Core.checkType must synthesize a complete closed lambda through the semantic checker"
    );
    const application = parser.parse("f a");
    const applicationHead = application.nodes[0];
    assert.equal(parser.stringify(core.checkType(application, [], false)), "B",
        "Core.checkType must synthesize a complete closed application on the immutable path");
    assert.equal(application.nodes[0], applicationHead,
        "semantic annotation must preserve existing AST node identities used by the proof assistant");
    assert.ok(application.nodes[0].checked,
        "the root semantic path must preserve child checked types used by the proof assistant");
    assert.equal(parser.stringify(application.nodes[0].checked), parser.stringify(parser.parse("A->B")));
    assert.ok(Core.semanticTypeCheckFastPathHits >= 3);
    assert.ok(Core.semanticTypeCheckAttempts >= 2);
    assert.ok(Core.semanticTypeCheckHits >= 2,
        "Core.checkType must use immutable synthesis for the constant and its type");
    const closedDefinition = core.checkDefinition(parser.parse("idA:=Lx:A,x"), []);
    assert.equal(closedDefinition.definitionCache.kind, "nbe");
    assert.deepEqual(closedDefinition.definitionCache.metas, []);
    assert.equal(countCheckedNodes(closedDefinition.filledDefinition), 0);
    const annotatedDefinition = core.checkDefinition(parser.parse("annotatedIdA:=(Lx:A,x):(A->A)"), []);
    assert.equal(annotatedDefinition.definitionCache.type.type, "P");
    assert.equal(parser.stringify(annotatedDefinition.definitionCache.type.nodes[0]), "A");
    assert.equal(parser.stringify(annotatedDefinition.definitionCache.type.nodes[1]), "A");
    const deepApplication = `${"((Lx:A,x) ".repeat(80)}a${")".repeat(80)}`;
    const deepAnnotatedDefinition = core.checkDefinition(
        parser.parse(`deepA:=${deepApplication}:A`),
        []
    );
    assert.equal(parser.stringify(deepAnnotatedDefinition.definitionCache.type), "A");
    const largeTerm = `${Array.from({ length: 40 }, (_, index) => `Lx${index}:A,`).join("")}x0`;
    const largeType = `${Array.from({ length: 40 }, (_, index) => `Px${index}:A,`).join("")}A`;
    const largeAnnotatedDefinition = core.checkDefinition(
        parser.parse(`largePi:=(${largeTerm}):(${largeType})`),
        []
    );
    assert.equal(largeAnnotatedDefinition.definitionCache.type.type, "P");
    const elaboratedDefinition = core.checkDefinition(parser.parse("sumAB:=@Sum _ _ A B"), []);
    assert.equal(
        parser.stringify(elaboratedDefinition.filledDefinition),
        parser.stringify(parser.parse("@Sum @0 @0 A B"))
    );
    assert.equal(elaboratedDefinition.definitionCache.kind, "nbe");
    assert.deepEqual(elaboratedDefinition.definitionCache.metas, []);
    core.state.defTypes.local = [parser.parse("A")];
    core.syncSemanticTypes();
    assert.equal(core.semanticTypeChecker.trySynthesize(parser.parse("local")).status, "invalid",
        "runtime caches must use the native NbE snapshot format");
    assert.equal(core.serializeDefinitionCache("local"), null,
        "a legacy partial runtime cache must not be serialized as a complete cache");

    core.state.defTypes.localDirect = parser.parse("B");
    core.syncSemanticTypes();
    assert.equal(
        core.semanticTypeChecker.trySynthesize(parser.parse("localDirect")).status,
        "invalid",
        "AST-only legacy runtime caches must be ignored"
    );
    assert.equal(core.serializeDefinitionCache("localDirect"), null);

    core.state.defTypes.genericPartial = [parser.parse("List ?1")];
    core.syncSemanticTypes();
    assert.equal(
        core.semanticTypeChecker.trySynthesize(parser.parse("genericPartial")).status,
        "invalid",
        "a legacy partial runtime cache must not install an untracked metavariable"
    );

    core.setUserDefinition("rechecked", parser.parse("a"));
    core.state.defTypes.rechecked = [parser.parse("A")];
    const rebuilt = core.checkDefinition(parser.parse("rechecked:=a"), []);
    core.restoreDefinitionCache("rechecked", rebuilt.definitionCache);
    assert.equal(
        parser.stringify(core.checkType(parser.parse("rechecked"), [], false)),
        "A",
        "an incomplete compatibility cache must be rebuilt by NbE before use"
    );
    core.setUserDefinition("local");
    assert.deepEqual(
        core.semanticTypeChecker.trySynthesize(parser.parse("local")),
        { status: "invalid", code: "unknown-constant" },
        "removing a definition must remove its semantic type cache"
    );
}

{
    // A dependent lambda argument can constrain a scheme meta through a
    // variable from the surrounding checking context, not only through the
    // binder telescope passed to convertTypes. This is the small shape behind
    // the pre/post equivalence theorem fallbacks in the K609 workload.
    const sourceCore = new Core();
    const contextKernel = new SemanticNbeKernel();
    const contextChecker = new SemanticNbeTypeChecker(contextKernel);
    contextChecker.setConstantType("B", parser.parse("U"));
    contextChecker.setConstantType("C", parser.parse("U"));
    contextChecker.setConstantType("True", parser.parse("U"));
    const schemeType = sourceCore.markBondVars(
        parser.parse("Ph:(Πy:B,?F y),True"),
        []
    );
    assert.equal(contextChecker.setConstantSchemeSnapshot("acceptContextFamily", {
        type: schemeType,
        metas: [{ name: "?F", expectedType: parser.parse("Πy:B,U") }]
    }), true);
    const contextFamily = contextChecker.trySynthesize(
        parser.parse("acceptContextFamily (λy:B,k y)"),
        [["k", parser.parse("B->C"), 900001]],
        { elaborateMetas: true, maxSteps: 65_536 }
    );
    assert.equal(contextFamily.status, "success",
        `context-bound Miller pattern must synthesize (${contextFamily.code ?? "unknown"})`);
    assert.equal(parser.stringify(contextFamily.type), "True");
}

function countCheckedNodes(ast, seen = new WeakSet()) {
    if (!ast || seen.has(ast)) return 0;
    seen.add(ast);
    let count = ast.checked ? 1 + countCheckedNodes(ast.checked, seen) : 0;
    for (const node of ast.nodes ?? []) count += countCheckedNodes(node, seen);
    return count;
}

console.log("immutable semantic NbE type checker regression passed");
