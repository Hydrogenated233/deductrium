import assert from "node:assert/strict";
import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { cloneInductiveBundle } from "../js/tt/gui.js";
import { lowerSandboxInductive, parseSandboxInductive } from "../js/tt/sandbox.js";

const parser = new ASTParser();
const parse = source => parser.parse(source);
const pattern = (...parts) => parts.map(parse);

const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: ["True", "False"],
    inferDisplayMode: "_",
    timeout: 10_000,
    language: "zh"
});

const bundle = {
    type: ["tri", parse("U")],
    constructors: [
        ["nt", parse("tri")],
        ["0t", parse("tri")],
        ["pt", parse("tri")]
    ],
    eliminator: [
        "ind_tri",
        parse("PC:tri->U0,Pcnt:C nt,Pc0t:C 0t,Pcpt:C pt,Px:tri,C x")
    ],
    computeRules: {
        ind_tri: [
            { pattern: pattern("ind_tri", "?C", "?cnt", "?c0t", "?cpt", "nt"), result: parse("?cnt") },
            { pattern: pattern("ind_tri", "?C", "?cnt", "?c0t", "?cpt", "0t"), result: parse("?c0t") },
            { pattern: pattern("ind_tri", "?C", "?cnt", "?c0t", "?cpt", "pt"), result: parse("?cpt") }
        ]
    }
};

const registration = engine.core.registerSystemInductive(bundle);

assert.deepEqual(registration.names, ["tri", "nt", "0t", "pt", "ind_tri"]);
assert.equal(registration.computeRuleCount, 3);
for (const name of ["tri", "nt", "0t", "pt", "ind_tri"]) {
    assert.equal(engine.core.hasConst(name), true, `${name} was not registered`);
}

for (const constructor of ["nt", "0t", "pt"]) {
    const result = engine.check(`${constructor}:tri`);
    assert.equal(result.ok, true, `${constructor}: ${result.error}`);
}
assert.equal(engine.check("ind_tri").ok, true);

// The equations must be semantic iota rules, not merely a type declaration:
// each branch is definitionally equal to its corresponding method.
for (const [constructor, branch] of [["nt", "true"], ["0t", "true"], ["pt", "true"]]) {
    const result = engine.check(
        `ind_tri (Lx:tri.True) true true true ${constructor} === ${branch}`
    );
    assert.equal(result.ok, true, `${constructor} iota rule: ${result.error}`);
}

// Registration is guarded against silently replacing an existing constant.
assert.throws(
    () => engine.core.registerSystemInductive({
        type: ["tri", parse("U")],
        constructors: [["nt2", parse("tri")]],
        computeRules: {}
    }),
    /名称冲突/
);
assert.equal(engine.core.hasConst("tri2"), false);

// Semantic validation is part of the registration transaction. A malformed
// generated constructor type must not leave its type or compute-rule head in
// the persistent Core after the error is reported.
const failed = new TTCoreEngine();
failed.configure({ unlockedTypes: ["True", "False"] });
assert.throws(
    () => failed.core.registerSystemInductive({
        type: ["Broken", parse("U")],
        constructors: [["broken", parse("Missing")]],
        eliminator: ["ind_Broken", parse("Broken->Broken")],
        computeRules: {
            ind_Broken: [{
                pattern: pattern("ind_Broken", "broken"),
                result: parse("broken")
            }]
        }
    }),
    /Missing|未知|Unknown/
);
for (const name of ["Broken", "broken", "ind_Broken"]) {
    assert.equal(failed.core.hasConst(name), false, `${name} leaked after rollback`);
}
assert.equal(failed.core.state.computeRules.ind_Broken, undefined);
assert.equal(failed.core.semanticKernel.hasComputeRules("ind_Broken"), false);

// Generated entries must be types, not merely well-typed terms. Registering a
// constructor with `true` as its declared type must roll back the whole bundle.
assert.throws(
    () => failed.core.registerSystemInductive({
        type: ["BrokenSort", parse("U")],
        constructors: [["brokenSort", parse("true")]],
        computeRules: {}
    }),
    /Universe/
);
for (const name of ["BrokenSort", "brokenSort"]) {
    assert.equal(failed.core.hasConst(name), false, `${name} leaked after type-formation rollback`);
}

// The engine configuration path uses the same transaction, which is the path
// used when a creative-mode save is restored into a worker.
const configured = new TTCoreEngine();
configured.configure({
    unlockedTypes: ["True", "False"],
    trustedInductives: [bundle]
});
assert.equal(configured.core.hasConst("0t"), true);
assert.equal(configured.core.state.computeRules.ind_tri.length, 3);
assert.equal(configured.core.semanticKernel.hasComputeRules("ind_tri"), true);

const sandboxBundle = lowerSandboxInductive(parseSandboxInductive(
    "inductive triClone : U | ntClone : triClone | zeroClone : triClone | ptClone : triClone"
));
const cloned = cloneInductiveBundle(sandboxBundle);
assert.equal(cloned.recursor?.[0], "rec_triClone",
    "the creative type-layer bridge must retain the public recursor");
assert.equal(cloned.metadata?.recursorName, "rec_triClone",
    "the proof-assistant Worker bridge must retain recursor metadata");
assert.equal(cloned.metadata?.fullEliminatorName, "@ind_triClone",
    "the bridge must retain the universe-polymorphic eliminator metadata");
assert.equal(cloned.metadata?.fullRecursorName, "@rec_triClone",
    "the bridge must retain the universe-polymorphic recursor metadata");
assert.equal(cloned.metadata?.ruleSchemaVersion, 1,
    "the bridge must retain the Core-validated compute-rule schema marker");
assert.deepEqual(cloned.metadata?.constructors[0].argumentNames, [],
    "the bridge must retain canonical constructor argument names");
assert.deepEqual(cloned.metadata?.constructors[0].recursiveArguments, [],
    "the bridge must retain canonical recursive-argument metadata");
assert.equal(cloned.computeRules?.rec_triClone?.length, 3,
    "the bridge must retain all recursor iota rules");
assert.notEqual(cloned.recursor?.[1], sandboxBundle.recursor?.[1],
    "bridge snapshots must deep-clone recursor ASTs");
assert.equal(
    configured.check("ind_tri (Lx:tri.True) true true true 0t === true").ok,
    true
);

console.log("Core dynamic ordinary-inductive bundle regression passed");
