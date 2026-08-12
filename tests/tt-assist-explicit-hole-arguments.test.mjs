import assert from "node:assert/strict";

import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { ASTParser } from "../js/tt/astparser.js";
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

function runSemantic(action) {
    return action();
}

function rejectsSemantic(action) {
    assert.throws(action);
}

function containsHole(ast) {
    return !!ast && (ast.type === "var" && ast.name === "_"
        || (ast.nodes ?? []).some(containsHole));
}

{
    const engine = new TTAssistEngine();
    engine.configure(config);
    let snapshot = engine.start(
        "Πf:(Πx:nat,Πy:nat,add x y=add x y),Πa:nat,Πb:nat,add a b=add a b",
        options
    );
    for (const command of ["intro f", "intro a", "intro b"]) {
        snapshot = engine.apply(command);
    }
    snapshot = runSemantic(() => engine.apply("apply f _ _"));
    assert.equal(snapshot.goals.length, 0,
        "apply f _ _ must infer both explicit holes from the current goal");
    assert.match(parser.stringify(snapshot.elem), /f a b/,
        "the inferred apply arguments must be stored in the proof term");
    assert.doesNotMatch(parser.stringify(snapshot.elem), /(^|[ (])_([ )]|$)/,
        "a completed proof term must not retain explicit holes");
}

{
    const engine = new TTAssistEngine();
    engine.configure(config);
    let snapshot = engine.start("Πf:(True→True→False),False", options);
    snapshot = engine.apply("intro f");
    snapshot = runSemantic(() => engine.apply("apply f _ _"));
    assert.equal(snapshot.goals.length, 0,
        "apply f _ _ must automatically solve holes not fixed by the target");
    assert.match(parser.stringify(snapshot.elem), /f true true/,
        "the proof assistant must use its automatic True proof for both holes");
    assert.doesNotMatch(parser.stringify(snapshot.elem), /(^|[ (])_([ )]|$)/,
        "automatically solved apply holes must not remain in the proof term");
}

{
    const engine = new TTAssistEngine();
    engine.configure(config);
    let snapshot = engine.start(
        "Πadd_assoc:(Πx:nat,Πy:nat,Πz:nat,add (add x y) z=add x (add y z)),"
        + "Πa:nat,Πb:nat,Πc:nat,add (add a b) c=add a (add b c)",
        options
    );
    for (const command of ["intro add_assoc", "intro a", "intro b", "intro c"]) {
        snapshot = engine.apply(command);
    }
    snapshot = runSemantic(() => engine.apply("rw add_assoc _ _ _"));
    assert.ok(snapshot.tactics.includes("rfl"),
        "rw add_assoc _ _ _ must infer arguments by matching the current goal");
    assert.match(parser.stringify(snapshot.elem), /add_assoc a b c/,
        "rewrite inference must store the resolved theorem arguments");
    assert.doesNotMatch(parser.stringify(snapshot.elem), /add_assoc _/,
        "rewrite proof terms must not retain user holes");
}

for (const command of ["rw add_assoc _ _ _", "rwb add_assoc _ _ _"]) {
    const engine = new TTAssistEngine();
    engine.configure({ ...config, disableSimpleEq: true });
    let snapshot = engine.start(
        "Πadd_assoc:(Πx:nat,Πy:nat,Πz:nat,eq (add (add x y) z) (add x (add y z))),"
        + "Πa:nat,Πb:nat,Πc:nat,eq (add (add a b) c) (add a (add b c))",
        options
    );
    for (const intro of ["intro add_assoc", "intro a", "intro b", "intro c"]) {
        snapshot = engine.apply(intro);
    }
    snapshot = runSemantic(() => engine.apply(command));
    assert.ok(snapshot.tactics.includes("rfl"),
        `${command} must infer rewrite arguments when equality syntax sugar is disabled`);
    assert.match(parser.stringify(snapshot.elem), /add_assoc a b c/,
        `${command} must store the inferred theorem arguments in survival mode`);
    assert.doesNotMatch(parser.stringify(snapshot.elem), /add_assoc _/,
        `${command} must not retain rewrite holes in survival mode`);
}

{
    const engine = new TTAssistEngine();
    engine.configure(config);
    engine.start("true=true", options);
    const snapshot = runSemantic(() => engine.apply("apply @inveq _ _ _ _ _"));
    assert.equal(snapshot.goals.length, 0,
        "explicit @ apply holes must be solved instead of accepted as proof holes");
    assert.match(parser.stringify(engine.assist.elem), /@inveq @0 True true true \(refl true\)/,
        "the unconstrained equality proof must be filled by the proof assistant");
    assert.equal(containsHole(engine.assist.elem), false,
        "the internal completed proof must not retain explicit input holes");
}

{
    const engine = new TTAssistEngine();
    engine.configure(config);
    engine.start("True×True", options);
    const snapshot = runSemantic(() => engine.apply("apply @pair _ _ _ _ _ _"));
    assert.equal(snapshot.goals.length, 0,
        "explicit @ constructor arguments must be automatically proved");
    assert.equal(containsHole(engine.assist.elem), false,
        "explicit @ constructor autofill must leave a closed internal term");
}

for (const command of ["rw h _", "rwb h _"]) {
    const engine = new TTAssistEngine();
    engine.configure(config);
    let snapshot = engine.start("Πh:(True→(true=true)),true=true", options);
    snapshot = engine.apply("intro h");
    snapshot = runSemantic(() => engine.apply(command));
    assert.match(parser.stringify(snapshot.elem), /h true/,
        `${command} must automatically fill the theorem argument`);
    assert.doesNotMatch(parser.stringify(snapshot.elem), /h _/,
        `${command} must not retain the theorem argument hole`);
}

for (const command of ["exact f _", "apply f _"]) {
    const engine = new TTAssistEngine();
    engine.configure(config);
    let snapshot = engine.start("Πf:(False→False),False", options);
    snapshot = engine.apply("intro f");
    const proofBefore = parser.stringify(snapshot.elem);
    rejectsSemantic(() => engine.apply(command));
    assert.equal(parser.stringify(engine.assist.elem), proofBefore,
        `${command} must roll back after its hole cannot be proved`);
    assert.equal(engine.assist.goal.length, 1,
        `${command} must restore the original goal after failure`);
}

console.log("proof-assistant explicit hole argument regression passed");
