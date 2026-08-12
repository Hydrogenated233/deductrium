import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";
import {
    SemanticNbeKernel,
    tryNbeDefinitionalEqual,
    tryNbeNormalize,
    tryNbeWhnf
} from "../js/tt/nbe-kernel.js";

const parser = new ASTParser();
const equal = (left, right, context = [], options = {}) => tryNbeDefinitionalEqual(
    parser.parse(left),
    parser.parse(right),
    context,
    options
);

function parsedComputeRule(source) {
    const equation = parser.parse(source);
    const pattern = [];
    let head = equation.nodes[0];
    while (head.type === "apply") {
        pattern.unshift(head.nodes[1]);
        head = head.nodes[0];
    }
    pattern.unshift(head);
    return { name: head.name, rule: { pattern, result: equation.nodes[1] } };
}

function installComputeRules(kernel, sources) {
    const table = {};
    for (const source of sources) {
        const { name, rule } = parsedComputeRule(source);
        (table[name] ??= []).push(rule);
    }
    return kernel.replaceComputeRules(table);
}

assert.equal(equal("(Lx:A.x) a", "a"), true, "beta equality must be decided semantically");
assert.equal(parser.stringify(tryNbeNormalize(parser.parse("(Lx:A.x) a"))), "a",
    "NbE quote must expose a beta-normalized AST");
{
    let nextId = 100;
    const normalized = tryNbeNormalize(parser.parse("Lx:A.x"), [], {
        freshBondVarId: () => nextId++
    });
    assert.equal(normalized.bondVarId, 100,
        "full NbE normalization must allocate quoted binders from the owning checker session");
    assert.equal(normalized.nodes[1].bondVarId, 100);
}
assert.equal(parser.stringify(tryNbeWhnf(parser.parse("(Lx:A.x) a"))), "a",
    "read-only NbE WHNF must expose a beta-reduced head");
{
    const source = parser.parse("Lx:A.add 2 3");
    const whnf = tryNbeWhnf(source);
    assert.equal(parser.stringify(whnf), parser.stringify(source),
        "WHNF must not normalize a lambda body");
    const rigid = parser.parse("pair (add 2 3) b");
    assert.equal(parser.stringify(tryNbeWhnf(rigid)), parser.stringify(rigid),
        "WHNF must leave rigid constructor arguments syntactic");
}
assert.equal(equal("Lx:A.x", "Ly:A.y"), true, "alpha-equivalent lambdas must compare equal");
assert.equal(equal("Lx:A.x", "Ly:B.y"), false,
    "lambda parameter domains must participate in semantic equality");
assert.equal(
    equal("Lf:(A->B).(Lx:A.f x)", "Lf:(A->B).f"),
    true,
    "eta-equivalent functions must compare equal"
);
assert.equal(
    equal("(Lx:A.(Ly:B.x)) y", "Ly:B.y"),
    false,
    "a free argument must not become equal to the quoted binder"
);
assert.equal(equal("Px:A,x", "Py:A,y"), true, "dependent binder alpha-equivalence must hold");
assert.equal(equal("?m", "a"), null, "inference variables must remain outside the semantic fragment");
assert.equal(equal("(Lx:A.x) a", "a", [], { maxSteps: 1 }), null,
    "budget exhaustion must report an unsupported semantic comparison");
{
    const reflexive = parser.parse("Lx:A.Ly:B.pair F x y");
    assert.equal(
        tryNbeDefinitionalEqual(reflexive, parser.parse("Lx:A.Ly:B.pair F x y"), [], { maxSteps: 1 }),
        true,
        "syntactically identical terms should use reflexivity without evaluator steps"
    );
    assert.equal(equal("?m", "?m"), null,
        "metavariable reflexivity must remain on the elaboration fallback path");
    const sharedMeta = parser.parse("?m");
    assert.equal(tryNbeDefinitionalEqual(sharedMeta, sharedMeta), null,
        "shared metavariable syntax must not bypass elaboration fallback by reference identity");
    assert.equal(equal("_", "_", [], { rigidMetas: true }), null,
        "input holes must remain unsupported even when metavariables are rigid");
}
assert.equal(
    equal("(Lx:A.x) a", "a", [], { deadline: Date.now() - 1 }),
    null,
    "an expired semantic deadline must report an unsupported comparison"
);
assert.equal(
    tryNbeWhnf(parser.parse("(Lx:A.x) a"), [], { deadline: Date.now() - 1 }),
    null,
    "an expired WHNF deadline must not return a partial AST"
);

{
    const kernel = new SemanticNbeKernel();
    assert.equal(kernel.setDefinition("id", parser.parse("Lx:A.x")), true);
    assert.equal(parser.stringify(kernel.tryWhnf(parser.parse("id a"))), "a",
        "WHNF must delta-unfold a definition only as far as its head");
    assert.equal(
        parser.stringify(kernel.tryWhnf(parser.parse("(Lx:A.(Ly:B.x)) a"))),
        parser.stringify(parser.parse("Ly:B.a")),
        "WHNF quoting must preserve a substituted lambda body without deep reduction"
    );
    const left = parser.parse("pair ?m (id a)");
    const right = parser.parse("pair ?m a");
    assert.equal(kernel.tryEqual(left, right), null,
        "metavariables stay outside the default semantic fragment");
    assert.equal(kernel.tryEqual(left, right, [], { rigidMetas: true }), true,
        "rigid metavariables may surround a closed beta/delta reduction");
    assert.equal(
        kernel.tryEqual(parser.parse("?f a"), parser.parse("?g a"), [], { rigidMetas: true }),
        false,
        "different rigid metavariable heads must remain unequal"
    );
}

{
    const left = parser.parse("x");
    const right = parser.parse("x");
    left.bondVarId = 7;
    right.bondVarId = 7;
    assert.equal(tryNbeDefinitionalEqual(left, right, [["x", parser.parse("A"), 7]]), true);
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(kernel.setDefinition("shared", parser.parse("Lx:True.x")), true);
    assert.equal(
        kernel.setDefinition("split", parser.parse("Lx:True.pair F true (shared x)")),
        true
    );
    assert.equal(installComputeRules(kernel, ["pr1 (pair ?f ?a ?b) === ?b"]), 1);
    assert.equal(
        kernel.tryEqualResult(
            parser.parse("Px:(shared true),x"),
            parser.parse("Py:(pr1 (split true)),y")
        ),
        "equal",
        "dependent binder domains must compare after delta and iota reduction"
    );
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(
        kernel.tryEqualResult(
            parser.parse("Px:A,pair F x x"),
            parser.parse("Py:A,pair F y y")
        ),
        "equal",
        "composite bodies must compare under alpha-aligned binder identities"
    );
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(
        kernel.tryEqualResult(parser.parse("(Lx:A.x) a"), parser.parse("a")),
        "equal",
        "beta equality must be handled entirely by the semantic kernel"
    );
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(kernel.setDefinition("id", parser.parse("Lx:A.x")), true);
    assert.equal(parser.stringify(kernel.tryWhnf(parser.parse("(Lx:A.x) a"))), "a");
    assert.equal(parser.stringify(kernel.tryWhnf(parser.parse("succ (add 2 3)"))), "6");
    let nextId = 100;
    const lambdaResult = kernel.tryWhnf(
        parser.parse("(Lx:A.(Ly:B.y)) a"),
        [],
        { freshBondVarId: () => nextId++ }
    );
    assert.equal(lambdaResult.bondVarId, 100,
        "semantic WHNF must use the caller's fresh binder allocator");
    assert.equal(lambdaResult.nodes[1].bondVarId, 100,
        "a quoted binder reference must share the freshly allocated id");
    assert.equal(nextId, 101);
    assert.equal(
        parser.stringify(kernel.tryWhnf(parser.parse("(Lx:A.unknownDefinition) a"))),
        "unknownDefinition",
        "unregistered definitions must remain neutral after beta reduction"
    );
    assert.equal(kernel.setDefinition("knownDefinition", parser.parse("Lz:B.z")), true);
    assert.equal(
        parser.stringify(kernel.tryWhnf(parser.parse("(Lx:A.knownDefinition) a"))),
        parser.stringify(parser.parse("Lz:B.z")),
        "registered definitions must delta-reduce when beta exposes their head"
    );
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(
        kernel.tryEqualResult(parser.parse("(Lx:A.x) a"), parser.parse("b")),
        "unequal"
    );
    assert.equal(
        kernel.tryEqualResult(parser.parse("Lx:A.x"), parser.parse("Ly:B.y")),
        "unequal"
    );
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(kernel.setDefinition("id", parser.parse("Lx:A.x")), true);
    const left = parser.parse("pair ?m (id a)");
    const right = parser.parse("pair ?m a");
    const leftBefore = parser.stringify(left);
    const rightBefore = parser.stringify(right);
    assert.equal(kernel.tryEqualResult(left, right), "unsupported");
    assert.equal(
        kernel.tryEqualResult(left, right, [], { rigidMetas: true }),
        "equal",
        "rigid metavariables may surround a semantic delta/beta equality"
    );
    assert.equal(parser.stringify(left), leftBefore, "semantic equality must not mutate its left AST");
    assert.equal(parser.stringify(right), rightBefore, "semantic equality must not mutate its right AST");
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(
        kernel.tryEqualResult(
            parser.parse("pair F (add 2 3) ?m"),
            parser.parse("pair F 5 ?m"),
            [],
            { rigidMetas: true }
        ),
        "equal",
        "closed recursive subterms must normalize inside a rigid metavariable context"
    );
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(
        kernel.tryEqualResult(parser.parse("succ (add 2 3)"), parser.parse("6")),
        "equal",
        "nested arithmetic must normalize semantically"
    );
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(kernel.setDefinition("id", parser.parse("Lx:A.x")), true);
    assert.equal(kernel.tryEqualResult(parser.parse("id a"), parser.parse("a")), "equal");
    assert.equal(kernel.cachedDefinitionCount, 1,
        "delta/beta equality must populate the semantic definition cache");
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(kernel.setDefinition("id", parser.parse("Lx:A.x")), true);
    assert.equal(kernel.setDefinition("alias", parser.parse("id")), true);
    assert.equal(kernel.definitionCount, 2);
    assert.equal(kernel.tryEqual(parser.parse("alias a"), parser.parse("a")), true,
        "precompiled definitions must delta-reduce through dependent aliases");
    assert.equal(kernel.cachedDefinitionCount, 2);

    kernel.setDefinition("unrelated", parser.parse("c"));
    assert.equal(kernel.cachedDefinitionCount, 2,
        "adding an unrelated definition must preserve cached semantic values");

    const revision = kernel.revision;
    assert.equal(kernel.setDefinition("id", parser.parse("Lx:A.b")), true);
    assert.ok(kernel.revision > revision, "updating a definition must invalidate cached semantic values");
    assert.equal(kernel.cachedDefinitionCount, 0,
        "changing a definition must invalidate it and recursive dependents");
    assert.equal(kernel.tryEqual(parser.parse("alias a"), parser.parse("a")), false,
        "dependent semantic values must be recomputed after a definition changes");

    assert.equal(kernel.deleteDefinition("alias"), true);
    assert.equal(kernel.definitionCount, 2);
    assert.equal(kernel.tryEqual(parser.parse("alias a"), parser.parse("a")), false);
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(installComputeRules(kernel, ["pr1 (pair ?f ?a ?b) === ?b"]), 1);
    assert.equal(kernel.setDefinition("deep0", parser.parse("Lx:True.x")), true);
    for (let index = 1; index <= 12; index++) {
        assert.equal(
            kernel.setDefinition(
                `deep${index}`,
                parser.parse(`Lx:True.deep${index - 1} (deep${index - 1} x)`)
            ),
            true
        );
    }
    assert.equal(kernel.setDefinition("shared", parser.parse("Lx:True.deep12 x")), true);
    assert.equal(
        kernel.setDefinition("split", parser.parse("Lx:True.pair F true (shared x)")),
        true
    );
    assert.equal(
        kernel.tryEqual(
            parser.parse("shared true"),
            parser.parse("pr1 (split true)"),
            [],
            { maxSteps: 512 }
        ),
        true,
        "a shared definition head exposed by iota reduction must compare before its proof body unfolds"
    );
}

{
    const kernel = new SemanticNbeKernel();
    let largeType = "A";
    for (let index = 0; index < 80; index++) largeType = `Px${index}:A,${largeType}`;
    assert.equal(kernel.setDefinition("largeLeft", parser.parse(largeType)), true);
    assert.equal(kernel.setDefinition("largeRight", parser.parse(largeType)), true);
    const repeat = name => {
        let result = name;
        for (let index = 0; index < 12; index++) result = `pair F ${name} (${result})`;
        return result;
    };
    assert.equal(
        kernel.tryEqual(
            parser.parse(repeat("largeLeft")),
            parser.parse(repeat("largeRight")),
            [],
            { maxSteps: 2_000 }
        ),
        true,
        "repeated semantic value pairs must reuse a completed equality comparison"
    );
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(kernel.setDefinition("delta0", parser.parse("true")), true);
    for (let index = 1; index <= 300; index++) {
        assert.equal(
            kernel.setDefinition(`delta${index}`, parser.parse(`delta${index - 1}`)),
            true
        );
    }
    assert.equal(kernel.setDefinition("ignoreDeep", parser.parse("Lx:A.delta300")), true);
    assert.equal(
        kernel.tryEqual(
            parser.parse("ignoreDeep left"),
            parser.parse("ignoreDeep right"),
            [],
            { maxSteps: 256 }
        ),
        true,
        "lazy delta equality must avoid unfolding an unused deep result chain"
    );
    assert.equal(kernel.cachedDefinitionCount, 0,
        "lazy and barrier probes must not leak values into the eager definition cache");
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(kernel.setDefinition("definedArg", parser.parse("plainArg")), true);
    assert.equal(kernel.setDefinition("ruleOne", parser.parse("one")), true);
    assert.equal(kernel.setDefinition(
        "sharedRuleRhs",
        parser.parse("(Lx:A.one) definedArg")
    ), true);
    assert.equal(installComputeRules(kernel, [
        "chooseDefined definedArg === ruleOne",
        "chooseDefined plainArg === two"
    ]), 2);
    assert.equal(kernel.tryEqual(parser.parse("chooseDefined definedArg"), parser.parse("ruleOne")), false,
        "lazy delta must unfold transparent arguments before rigid pattern matching");
    assert.equal(
        kernel.tryEqual(parser.parse("chooseDefined definedArg"), parser.parse("sharedRuleRhs")),
        false,
        "speculative opacity must not expose a compute rule hidden by transparent delta reduction"
    );
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(kernel.setDefinition("barrierFn", parser.parse("Lx:A.a")), true);
    assert.equal(kernel.setDefinition("barrierRhs", parser.parse("(Lu:A.b) barrierFn")), true);
    assert.equal(installComputeRules(kernel, ["barrierFn ?x === b"]), 1);
    assert.equal(parser.stringify(kernel.tryNormalize(parser.parse("barrierFn c"))), "a");
    assert.equal(parser.stringify(kernel.tryNormalize(parser.parse("barrierRhs"))), "b");
    assert.equal(kernel.tryEqual(parser.parse("barrierFn c"), parser.parse("barrierRhs")), false,
        "a shared-definition barrier must not enable a rule hidden by delta reduction");
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(kernel.setDefinition("ruleAlias", parser.parse("plain")), true);
    assert.equal(kernel.setDefinition("ruleExpected", parser.parse("two")), true);
    assert.equal(installComputeRules(kernel, [
        "orderedRule ruleAlias === _",
        "orderedRule plain === two"
    ]), 2);
    assert.equal(
        kernel.tryEqual(parser.parse("orderedRule ruleAlias"), parser.parse("ruleExpected")),
        true,
        "a transparent alias must not make an earlier unsupported rule shadow the matching rule"
    );
}

{
    const kernel = new SemanticNbeKernel();
    const source = parser.parse("Lx:A.x");
    assert.equal(kernel.setDefinition("id", source), true);
    source.nodes[1].name = "b";
    assert.equal(kernel.setDefinition("id", source), true,
        "in-place source edits must invalidate semantic definition caches");
    assert.equal(kernel.tryEqual(parser.parse("id a"), parser.parse("a")), false,
        "a mutated definition must not keep the previous beta body");
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(kernel.setDefinition("id", parser.parse("Lx:A.x")), true);
    assert.equal(parser.stringify(kernel.tryWhnf(parser.parse("id a"))), "a");
    assert.equal(kernel.replaceOpaqueDefinitions(["id"]), 1);
    assert.equal(kernel.opaqueDefinitionCount, 1);
    assert.equal(
        parser.stringify(kernel.tryWhnf(parser.parse("id a"))),
        parser.stringify(parser.parse("id a")),
        "opaque definitions must remain neutral during WHNF"
    );
    assert.equal(kernel.tryEqual(parser.parse("id a"), parser.parse("a")), false,
        "opaque definitions must not delta-unfold during conversion");
    kernel.replaceOpaqueDefinitions([]);
    assert.equal(kernel.tryEqual(parser.parse("id a"), parser.parse("a")), true,
        "making a definition transparent must invalidate cached semantic values");
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(installComputeRules(kernel, [
        "ind_nat ?C ?c0 ?csucc 0 === ?c0",
        "ind_nat ?C ?c0 ?csucc (succ ?n) === ?csucc ?n (ind_nat ?C ?c0 ?csucc ?n)",
        "pr0 (pair ?f ?a ?b) === ?a",
        "ind_eq ?x ?C ?crfl ?x (refl ?x) === ?crfl",
        "head ?x === Lz:A.?x"
    ]), 5);
    assert.equal(kernel.computeRuleCount, 5);
    assert.equal(kernel.tryEqual(parser.parse("ind_nat C z s 0"), parser.parse("z")), true,
        "zero induction must iota-reduce");
    assert.equal(
        kernel.tryEqual(parser.parse("ind_nat C z s (succ 0)"), parser.parse("s 0 z")),
        true,
        "successor induction must recursively instantiate captures"
    );
    assert.equal(
        kernel.tryEqual(parser.parse("ind_nat C z s 2"), parser.parse("s 1 (s 0 z)")),
        true,
        "decimal naturals must match successor patterns"
    );
    assert.equal(kernel.tryEqual(parser.parse("pr0 (pair F a b)"), parser.parse("a")), true,
        "dependent-product projection must reduce without quoting an AST");
    assert.equal(
        kernel.tryEqual(parser.parse("ind_eq x C crfl x (refl x)"), parser.parse("crfl")),
        true,
        "repeated compute-rule captures must match equal semantic values"
    );
    assert.equal(
        kernel.tryEqual(parser.parse("ind_eq x C crfl y (refl x)"), parser.parse("crfl")),
        false,
        "a nonlinear compute rule must not match different captures"
    );
    assert.equal(
        parser.stringify(kernel.tryNormalize(parser.parse("ind_nat C z s (succ 0)"))),
        "(s 0 z)",
        "quoted semantic evaluation must expose recursive iota results"
    );
    assert.equal(kernel.tryEqual(parser.parse("head a b"), parser.parse("a")), true,
        "arguments beyond the matched prefix must remain applied to the result");
    assert.equal(kernel.setDefinition(
        "double",
        parser.parse("ind_nat (Lx:nat.nat) 0 (Lx:nat.Ly:nat.succ (succ y))")
    ), true);
    assert.equal(kernel.tryEqual(parser.parse("double (succ 0)"), parser.parse("succ (succ 0)")), true,
        "definitions must delta-unfold before their underlying iota rules run");
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(installComputeRules(kernel, [
        "choose ?x === first",
        "choose special === second"
    ]), 2);
    assert.equal(kernel.tryEqual(parser.parse("choose special"), parser.parse("first")), true,
        "compute rules must retain source-order priority");
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(installComputeRules(kernel, [
        "opaque_result ?x === _",
        "opaque_result ?x === later"
    ]), 2);
    assert.equal(kernel.tryEqual(parser.parse("opaque_result a"), parser.parse("later")), null,
        "an unsupported earlier rule must stop semantic evaluation instead of exposing a later rule");
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(installComputeRules(kernel, ["guarded (Lx:A.x) 0 === ok"]), 1);
    assert.equal(kernel.canReduce(parser.parse("guarded g n")), false,
        "binder patterns must reject an impossible open argument shape");
    assert.equal(kernel.canReduce(parser.parse("guarded g 0")), false,
        "binder patterns must reject a non-lambda argument before evaluation");
    assert.equal(kernel.tryEqual(parser.parse("guarded g n"), parser.parse("later")), false);
    assert.equal(kernel.tryEqual(parser.parse("guarded g 0"), parser.parse("ok")), false);
    assert.equal(
        kernel.tryEqual(parser.parse("guarded (Lx:A.x) 0"), parser.parse("ok")),
        true,
        "lambda-shaped computation rules must reduce in the semantic kernel"
    );
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(installComputeRules(kernel, [
        "pick (pair _ ?x) === ?x",
        "shape (Px:A,x) === ok"
    ]), 2);
    assert.equal(
        kernel.tryEqual(parser.parse("pick (pair left right)"), parser.parse("right")),
        true,
        "nested pattern wildcards must remain semantic and capture the selected argument"
    );
    assert.equal(
        kernel.tryEqual(parser.parse("shape (Px:A,x)"), parser.parse("ok")),
        true,
        "dependent-binder patterns must compare alpha-bound bodies"
    );
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(installComputeRules(kernel, [
        "ind_nat ?C ?c0 ?csucc 0 === ?c0",
        "ind_nat ?C ?c0 ?csucc (succ ?n) === ?csucc ?n (ind_nat ?C ?c0 ?csucc ?n)",
        "ind_nat (Lx:A.x) 0 s _ === ok"
    ]), 3);
    assert.equal(kernel.canReduce(parser.parse("ind_nat C 0 s n")), false,
        "unsupported overloads must not trigger a probe when supported iota shapes cannot match");
    assert.equal(kernel.canReduce(parser.parse("ind_nat C 0 s 0")), true);
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(kernel.tryEqual(parser.parse("@succ @0"), parser.parse("@1")), true);
    assert.equal(kernel.tryEqual(parser.parse("@succ (@succ @2)"), parser.parse("@4")), true);
    assert.equal(kernel.tryEqual(parser.parse("@max @0 @2"), parser.parse("@2")), true);
    assert.equal(kernel.tryEqual(parser.parse("@max u u"), parser.parse("u")), true);
    assert.equal(kernel.tryEqual(parser.parse("@max (@succ u) u"), parser.parse("@succ u")), true);
    assert.equal(
        kernel.tryEqual(parser.parse("@max u (@succ (@succ u))"), parser.parse("@succ (@succ u)")),
        true
    );
    assert.equal(
        kernel.tryEqual(parser.parse("@max u v"), parser.parse("@max v u")),
        true,
        "universe maxima must be canonicalized independently of argument order"
    );
    assert.equal(
        kernel.tryEqual(parser.parse("@max u v w"), parser.parse("@max (@max u v) w")),
        true,
        "over-saturated universe maxima must flatten to the same normal form"
    );
    assert.equal(
        kernel.tryEqual(parser.parse("@succ (@max u v)"), parser.parse("@max (@succ u) (@succ v)")),
        true,
        "successor must distribute over a universe maximum"
    );
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(kernel.tryEqual(parser.parse("add 2 3"), parser.parse("5")), true);
    assert.equal(kernel.tryEqual(parser.parse("mul 6 7"), parser.parse("42")), true);
    assert.equal(kernel.tryEqual(parser.parse("pow 2 5"), parser.parse("32")), true);
    assert.equal(kernel.tryEqual(parser.parse("pred 0"), parser.parse("0")), true);
    assert.equal(kernel.tryEqual(parser.parse("succ 41"), parser.parse("42")), true);
    assert.equal(kernel.tryEqual(parser.parse("succ 2"), parser.parse("4")), false);
    assert.equal(kernel.tryEqual(parser.parse("mul 3 4"), parser.parse("13")), false);
    assert.equal(
        kernel.tryEqual(parser.parse("add a (succ b)"), parser.parse("succ (add a b)")),
        true,
        "symbolic successor arithmetic must preserve the recursive equation"
    );
    assert.equal(installComputeRules(kernel, [
        "ind_nat ?C ?c0 ?csucc 0 === ?c0",
        "ind_nat ?C ?c0 ?csucc (succ ?n) === ?csucc ?n (ind_nat ?C ?c0 ?csucc ?n)"
    ]), 2);
    assert.equal(kernel.setDefinition(
        "double",
        parser.parse("ind_nat (Lx:nat.nat) 0 (Lx:nat.Ly:nat.succ (succ y))")
    ), true);
    assert.equal(kernel.setDefinition(
        "factorial",
        parser.parse("ind_nat (Ly:nat.nat) 1 (Lk:nat.Ln:nat.mul n (succ k))")
    ), true);
    assert.equal(kernel.tryEqual(parser.parse("double 2"), parser.parse("4")), true);
    assert.equal(kernel.tryEqual(parser.parse("factorial 5"), parser.parse("120")), true);
    assert.equal(
        kernel.tryEqual(parser.parse("pow 2 100000"), parser.parse("0"), [], { maxSteps: 64 }),
        null,
        "large powers must respect the semantic evaluation budget before allocating a huge BigInt"
    );
    assert.equal(kernel.canReduce(parser.parse("ind_nat C z s n")), false,
        "a variable eliminand must not trigger a speculative semantic attempt");
    assert.equal(kernel.canReduce(parser.parse("ind_nat C z s (succ n)")), true);
    assert.equal(kernel.canSemanticReduce(parser.parse("ind_nat C z s n")), false);
    assert.equal(kernel.canSemanticReduce(parser.parse("ind_nat C z s (succ n)")), false,
        "open natural recursion must report that semantic reduction is unavailable");
    assert.equal(kernel.canSemanticReduce(parser.parse("ind_nat C z s (succ 0)")), true);
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(installComputeRules(kernel, ["pr0 (pair ?f ?a ?b) === ?a"]), 1);
    assert.equal(
        kernel.tryEqualResult(parser.parse("pr0 (pair F a b)"), parser.parse("a")),
        "equal",
        "a registered iota rule must be decided directly by the semantic kernel"
    );
}

{
    const engine = new TTCoreEngine();
    engine.configure({
        unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
        disableSimpleFn: false,
        disableSimpleEq: false,
        inferDisplayMode: "_"
    });
    assert.ok(engine.core.semanticKernel.computeRuleCount > 300,
        "the Worker engine must precompile the registered system computation rules");
    assert.equal(
        engine.core.semanticKernel.tryEqualResult(
            parser.parse("ind_nat C z s (succ 0)"),
            parser.parse("s 0 z")
        ),
        "equal",
        "the Worker engine's semantic kernel must use its precompiled system rules"
    );
}

{
    const kernel = new SemanticNbeKernel();
    assert.equal(installComputeRules(kernel, ["pr0 (pair ?f ?a ?b) === ?a"]), 1);
    const unresolved = parser.parse("pr0 (pair F ?m b)");
    assert.equal(kernel.tryEqualResult(unresolved, unresolved), "unsupported",
        "unification terms must stay outside semantic equality, even by reflexivity");
}

console.log("independent semantic NbE kernel regression passed");
