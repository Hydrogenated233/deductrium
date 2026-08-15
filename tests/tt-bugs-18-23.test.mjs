import assert from "node:assert/strict";

import { Assist } from "../js/tt/assist.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { SemanticNbeKernel } from "../js/tt/nbe-kernel.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    disableSimpleFn: false,
    disableSimpleEq: false,
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
};
const options = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};

// #18: every evidence item must be unlocked. A first available evidence must
// not make a pattern with a later unavailable evidence look applicable.
{
    const previous = Assist.eq_matches;
    const engine = new TTAssistEngine();
    try {
        Assist.eq_matches = [[
            parser.parse("$1=$1"),
            parser.parse("rfl"),
            ["rfl", "missing-evidence"]
        ]];
        engine.configure(config);
        const snapshot = engine.start("true=true", options);
        assert.equal(snapshot.tactics.includes("eq"), false,
            "eq recommendation must check all evidence constants");
    } finally {
        Assist.eq_matches = previous;
    }
}

// #19: a future/semantic zero-arity node must remain a valid rewrite tree.
{
    const assist = new Assist(new Core(), parser.parse("True"));
    const leaf = { type: "synthetic-leaf", name: "unit", nodes: [] };
    assert.strictEqual(
        assist.genReplaceFn(leaf, parser.parse("other"), "x", new Set()),
        leaf,
        "genReplaceFn must not return undefined for leaf-shaped AST nodes"
    );
}

// #20 is not a bug: id 0 is the proof assistant's "not allocated yet"
// sentinel. Core.checkType clones the context and assigns a fresh positive id
// for each check; persisting that transient id breaks later destruct branches.
{
    const engine = new TTAssistEngine();
    engine.configure(config);
    let snapshot = engine.start("Πx:True,True", options);
    snapshot = engine.apply("intro x");
    assert.equal(snapshot.goals[0].context[0][2], 0,
        "intro must leave binder-id allocation to each Core check");
    snapshot = engine.apply("exact true");
    assert.equal(snapshot.goals.length, 0);
    assert.doesNotThrow(() => engine.qed());
}

// `hyp` introduces the same kind of local binder as `intro`.
{
    const engine = new TTAssistEngine();
    engine.configure(config);
    let snapshot = engine.start("True", options);
    snapshot = engine.apply("hyp h:True");
    const target = snapshot.goals.find(goal => goal.context.some(([name]) => name === "h"));
    assert.ok(target, "hyp must create a target goal with the new hypothesis");
    assert.equal(target.context.find(([name]) => name === "h")[2], 0,
        "hyp must leave binder-id allocation to each Core check");
    assert.equal(target.type.name, "True",
        "hyp's continuation must keep the original target type");
    snapshot = engine.apply("exact true");
    snapshot = engine.apply("exact true");
    assert.equal(snapshot.goals.length, 0);
    assert.doesNotThrow(() => engine.qed());
}

// #21: portable definitions clear binder metadata with undefined rather than
// serializing a null that is outside AST's declared bondVarId type.
{
    const session = new TTCoreSession();
    session.configure(config);
    const result = session.validate(0, parser.parse("identity:=λx:True.x"));
    assert.equal(result.ok, true, result.error);
    const stored = session.getDefinitionSlots()[0][1];
    const visit = ast => {
        assert.notEqual(ast.bondVarId, null,
            "portable definitions must not retain null binder ids");
        for (const child of ast.nodes ?? []) visit(child);
    };
    visit(stored);
}

// #22: open arithmetic terms still obey their right units in NbE.
{
    const kernel = new SemanticNbeKernel();
    const context = [["x", parser.parse("nat"), 0]];
    assert.equal(kernel.tryEqual(
        parser.parse("mul x 1"), parser.parse("x"), context
    ), true, "mul x 1 must normalize to x");
    assert.equal(kernel.tryEqual(
        parser.parse("pow x 1"), parser.parse("x"), context
    ), true, "pow x 1 must normalize to x");
}

// #23: right() should identify itself in its diagnostic.
{
    const engine = new TTAssistEngine();
    engine.configure(config);
    engine.start("True", options);
    assert.throws(
        () => engine.apply("right"),
        /right策略只能作用于和类型/
    );
}

console.log("TT bugs #18-23 regression tests passed");
