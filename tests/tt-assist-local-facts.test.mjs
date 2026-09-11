import assert from "node:assert/strict";
import { isTTAssistTacticUnlocked, TTAssistEngine } from "../js/tt/assist-engine.js";
import { ASTParser } from "../js/tt/astparser.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_", timeout: 30_000, language: "zh"
};
const options = {
    disableMultipleApply: false, disableDestructConds: false, disableDestructEq: false
};
const engine = new TTAssistEngine();
engine.configure(config);

// A local lemma must not drop either side of the original function goal.
engine.start("True -> True", options);
let snapshot = engine.apply("have h : True");
assert.equal(snapshot.goals.length, 2);
assert.equal(parser.stringify(snapshot.goals[1].type), "(True→True)");
engine.apply("exact true");
engine.apply("intro h0");
engine.apply("exact h");
assert.equal(engine.qed().theorem, "(True→True)");

for (const command of ["have h := true", "have h : True := true"]) {
    engine.start("True", options);
    snapshot = engine.apply(command);
    assert.equal(snapshot.goals.length, 1);
    assert.equal(snapshot.goals[0].context[0][0], "h");
    assert.equal(snapshot.goals[0].context[0][1].name, "True");
    const history = snapshot.history;
    assert.equal(engine.undo().goals[0].context.length, 0);
    engine.start("True", options, history);
    engine.apply("exact h");
    engine.qed();
}

engine.start("Πn:nat,n=n", options);
engine.apply("intro n");
snapshot = engine.apply("have h := refl n");
assert.equal(snapshot.goals[0].context[0][0], "h");
engine.apply("exact h");
engine.qed();

for (const command of ["have h : False := true", "have h := missing",
    "have h", "have h : True :=", "have _ := true", "have h : 0", "have h : true"]) {
    engine.start("True", options);
    assert.throws(() => engine.apply(command));
    const recovered = engine.apply("exact true");
    assert.deepEqual(recovered.history, ["exact true"]);
    engine.qed();
}
engine.start("True", options);
snapshot = engine.apply("have h := true");
assert.throws(() => engine.apply("have h := true"), /重复/);
engine.apply("exact h");
engine.qed();

// A temporary lemma in the witness goal must not resolve the dependent goal
// before the witness itself is constructed.
engine.start("Σn:nat,n=n", options);
engine.apply("constructor");
engine.apply("have h : True := true");
engine.apply("exact 0");
engine.apply("rfl");
engine.qed();

engine.start("Σn:nat,n=n", options);
snapshot = engine.apply("use 0");
assert.equal(snapshot.goals.length, 1);
assert.equal(parser.stringify(snapshot.goals[0].type), "(0=0)");
engine.apply("rfl");
engine.qed();

for (const [target, pattern, closing] of [
    ["Πh:(True X False),True", "⟨ha,hb⟩", "exact ha"],
    ["Πh:(Σn:nat,n=n),True", "<n, hn>", "exact true"],
    ["Πh:(True X True),True", "⟨_, hb⟩", "exact hb"]
]) {
    engine.start(target, options);
    engine.apply("intro h");
    const before = engine.apply(`rcases h with ${pattern}`);
    assert.equal(before.goals[0].context.some(entry => entry[0] === "h"), false);
    engine.undo();
    snapshot = engine.apply(`rcases h with ${pattern}`);
    assert.deepEqual(snapshot, before);
    engine.apply(closing);
    engine.qed();
}

engine.start("Πh:(True X True),True", options);
engine.apply("intro h");
for (const pattern of ["⟨x,x⟩", "⟨h,hb⟩", "⟨x,⟨y,z⟩⟩"]) {
    assert.throws(() => engine.apply(`rcases h with ${pattern}`));
}
engine.apply("exact true");
engine.qed();

for (const [alias, original] of [["have", "hyp"], ["use", "ex"], ["rcases", "destruct"]]) {
    assert.equal(isTTAssistTacticUnlocked(alias, new Set()), false);
    assert.equal(isTTAssistTacticUnlocked(alias, new Set([original])), true);
    assert.equal(isTTAssistTacticUnlocked(alias), true);
}

console.log("type-theory local facts and witnesses regression passed");
