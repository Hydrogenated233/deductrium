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

for (const command of ["obtain h := true", "obtain h : True := true"]) {
    engine.start("True", options);
    const snapshot = engine.apply(command);
    assert.equal(snapshot.goals.length, 1);
    assert.equal(snapshot.goals[0].context[0][0], "h");
    assert.equal(snapshot.goals[0].context[0][1].name, "True");
    engine.apply("exact h");
    assert.equal(engine.qed().theorem, "True");
}

const target = "Πp:(Σn:nat,n=n),Σm:nat,m=m";
for (const command of [
    "obtain ⟨n, hn⟩ := p",
    "obtain <n, hn> : Σn:nat,n=n := p",
    "obtain ⟨n, hn⟩ := (λz:(Σn:nat,n=n),z) p"
]) {
    engine.start(target, options);
    const before = engine.apply("intro p");
    const snapshot = engine.apply(command);
    assert.equal(snapshot.goals.length, 1);
    assert.equal(parser.stringify(snapshot.goals[0].type), "(Σm:nat,(m=m))");
    assert.deepEqual(snapshot.goals[0].context.map(entry => entry[0]), ["n", "hn", "p"]);
    assert.equal(snapshot.goals[0].context.find(entry => entry[0] === "n")[1].name, "nat");
    assert.equal(parser.stringify(snapshot.goals[0].context.find(entry => entry[0] === "hn")[1]), "(n=n)");
    assert.deepEqual(engine.undo(), before);
    assert.deepEqual(engine.start(target, options, snapshot.history), snapshot);
    engine.apply("use n");
    engine.apply("exact hn");
    assert.equal(engine.qed().theorem, parser.stringify(parser.parse(target)));
}

for (const pattern of ["⟨_, h⟩", "<obtain, h>"]) {
    engine.start("Πp:(True X True),True", options);
    engine.apply("intro p");
    const snapshot = engine.apply(`obtain ${pattern} := p`);
    const names = snapshot.goals[0].context.map(entry => entry[0]);
    assert.equal(new Set(names).size, names.length);
    assert.equal(names.includes("_"), false);
    assert.equal(names.length, 3, "the temporary fact must be eliminated");
    engine.apply("exact h");
    engine.qed();
}

engine.start("Πp:(True X True),True", options);
engine.apply("intro p");
const destructured = engine.apply("rcases p with ⟨_, h⟩");
assert.equal(new Set(destructured.goals[0].context.map(entry => entry[0])).size, 2);
engine.apply("exact h");
engine.qed();

// A local fact must preserve pending dependent constructor goals.
engine.start("Σn:nat,n=n", options);
engine.apply("constructor");
engine.apply("obtain h := true");
engine.apply("exact 0");
engine.apply("rfl");
engine.qed();

for (const command of [
    "obtain", "obtain h : True", "obtain h : True :=",
    "obtain h : False := true", "obtain h : 0 := true",
    "obtain _ := true", "obtain p := true", "obtain h := missing",
    "obtain ⟨x, x⟩ := p", "obtain ⟨p, h⟩ := p",
    "obtain ⟨x, ⟨y, z⟩⟩ := p", "obtain ⟨x, h> := p",
    "obtain ⟨x, h⟩ := true", "obtain ⟨x, h⟩ : False := p"
]) {
    engine.start("Πp:(True X True),True", options);
    const before = engine.apply("intro p");
    assert.throws(() => engine.apply(command), undefined, command);
    const recovered = engine.apply("exact true");
    assert.deepEqual(recovered.history, [...before.history, "exact true"], command);
    assert.deepEqual(engine.undo(), before, command);
    engine.apply("exact true");
    engine.qed();
}

assert.equal(isTTAssistTacticUnlocked("obtain"), true);
assert.equal(isTTAssistTacticUnlocked("obtain", new Set()), false);
assert.equal(isTTAssistTacticUnlocked("obtain", new Set(["hyp"])), false);
assert.equal(isTTAssistTacticUnlocked("obtain", new Set(["destruct"])), false);
assert.equal(isTTAssistTacticUnlocked("obtain", new Set(["hyp", "destruct"])), true);

console.log("type-theory obtain regression passed");
