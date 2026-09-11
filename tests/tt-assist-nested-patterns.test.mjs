import assert from "node:assert/strict";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const engine = new TTAssistEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_", timeout: 30_000, language: "zh"
});
const options = {
    disableMultipleApply: false, disableDestructConds: false, disableDestructEq: false
};
const target = "Πp:(Σn:nat,Σm:nat,n=m),Σa:nat,Σb:nat,a=b";
for (const command of [
    "rcases p with ⟨n, ⟨m, h⟩⟩",
    "rcases p with <n, <m, h>>",
    "obtain ⟨n, ⟨m, h⟩⟩ := p",
    "obtain <n, <m, h>> : Σn:nat,Σm:nat,n=m := p",
    "rintro ⟨n, ⟨m, h⟩⟩"
]) {
    let before = engine.start(target, options);
    if (!command.startsWith("rintro")) before = engine.apply("intro p");
    const snapshot = engine.apply(command);
    assert.equal(snapshot.goals.length, 1, command);
    assert.deepEqual(snapshot.goals[0].context.map(entry => entry[0]),
        command.startsWith("obtain") ? ["n", "m", "h", "p"] : ["n", "m", "h"], command);
    assert.equal(parser.stringify(snapshot.goals[0].context.find(entry => entry[0] === "h")[1]), "(n=m)");
    assert.equal(parser.stringify(snapshot.goals[0].type), "(Σa:nat,(Σb:nat,(a=b)))");
    assert.deepEqual(engine.undo(), before);
    assert.deepEqual(engine.start(target, options, snapshot.history), snapshot);
    engine.apply("use n");
    engine.apply("use m");
    engine.apply("exact h");
    assert.equal(engine.qed().theorem, "(Πp:(Σn:nat,(Σm:nat,(n=m))),(Σa:nat,(Σb:nat,(a=b))))");
}

// Splitting a left component must substitute it in the right component type.
engine.start("Πp:(Σq:(Σn:nat,n=n),(pr0 q)=(pr0 q)),True", options);
engine.apply("intro p");
const left = engine.apply("rcases p with ⟨⟨n, hn⟩, h⟩");
assert.deepEqual(left.goals[0].context.map(entry => entry[0]), ["n", "hn", "h"]);
assert.equal(Core.getFreeVars(left.goals[0].context.find(entry => entry[0] === "h")[1]).has("p"), false);
engine.apply("have checked : n=n := h");
engine.apply("exact true");
engine.qed();

engine.start("Πp:((True X True) X (True X True)),True", options);
engine.apply("intro p");
const balanced = engine.apply("rcases p with ⟨⟨a, b⟩, ⟨c, d⟩⟩");
assert.deepEqual(balanced.goals[0].context.map(entry => entry[0]), ["a", "b", "c", "d"]);
engine.apply("exact d");
engine.qed();

for (const [pattern, closing] of [
    ["⟨p1, ⟨p0, h⟩⟩", "h"],
    ["⟨p1, ⟨h, p0⟩⟩", "p0"]
]) {
    engine.start("Πp:(True X (True X True)),True", options);
    engine.apply("intro p");
    const result = engine.apply(`rcases p with ${pattern}`);
    assert.equal(result.goals[0].context.length, 3);
    engine.apply(`exact ${closing}`);
    engine.qed();
}

for (const command of [
    "rcases p with ⟨_, ⟨_, h⟩⟩",
    "obtain ⟨_, ⟨_, h⟩⟩ := p",
    "rintro ⟨_, ⟨_, h⟩⟩"
]) {
    engine.start("Πp:(True X (True X True)),True", options);
    if (!command.startsWith("rintro")) engine.apply("intro p");
    const result = engine.apply(command);
    const names = result.goals[0].context.map(entry => entry[0]);
    assert.equal(names.includes("_"), false);
    assert.equal(new Set(names).size, names.length);
    assert.equal(names.length, command.startsWith("obtain") ? 4 : 3);
    engine.apply("exact h");
    engine.qed();
}

// Original targets and later constructor goals must survive nested elimination.
engine.start("Πp:(Σn:nat,Σm:nat,n=m),(pr0 p)=(pr0 p)", options);
engine.apply("intro p");
const dependent = engine.apply("rcases p with ⟨n, ⟨m, h⟩⟩");
assert.equal(Core.getFreeVars(dependent.goals[0].type).has("p"), false);
engine.apply("rfl");
engine.qed();

engine.start("Πp:(True X (True X True)),Σn:nat,n=n", options);
engine.apply("intro p");
engine.apply("constructor");
engine.apply("obtain ⟨a, ⟨b, c⟩⟩ := p");
engine.apply("exact 0");
engine.apply("rfl");
engine.qed();

for (const pattern of [
    "⟨a, ⟨b, a⟩⟩", "⟨a, ⟨b, p⟩⟩",
    "⟨⟨a, b⟩, c⟩", // The first component is True, not a pair.
    "⟨a, ⟨b, c>⟩", "<a, <b, c>⟩",
    "⟨a, ⟨b, c⟩⟩ trailing", "⟨a, b, c⟩",
    "⟨a, ⟨b,⟩⟩", "⟨a, ⟨b, c⟩", "⟨a, b | c⟩"
]) {
    for (const command of [`rcases p with ${pattern}`, `obtain ${pattern} := p`]) {
        engine.start("Πp:(True X (True X True)),True", options);
        const before = engine.apply("intro p");
        assert.throws(() => engine.apply(command), undefined, command);
        const recovered = engine.apply("exact true");
        assert.deepEqual(recovered.history, ["intro p", "exact true"]);
        assert.deepEqual(engine.undo(), before);
        engine.apply("exact true");
        engine.qed();
    }
}

const wildcardTree = depth => depth ? `<${wildcardTree(depth - 1)},${wildcardTree(depth - 1)}>` : "_";
for (const pattern of ["⟨_, ".repeat(65) + "h" + "⟩".repeat(65), wildcardTree(8)]) {
    engine.start("Πp:(True X True),True", options);
    engine.apply("intro p");
    assert.throws(() => engine.apply(`rcases p with ${pattern}`), /模式过大或嵌套过深/);
    engine.apply("exact true");
    engine.qed();
}

for (const command of [
    "rintro ⟨a, ⟨b, a⟩⟩",
    "rintro ⟨⟨a, b⟩, c⟩",
    "rintro ⟨a, ⟨b, c⟩⟩ extra"
]) {
    engine.start("Πouter:True,Πp:(True X (True X True)),True", options);
    const before = engine.apply("intro outer");
    assert.throws(() => engine.apply(command));
    assert.deepEqual(engine.apply("intro p").history, ["intro outer", "intro p"]);
    assert.deepEqual(engine.undo(), before);
    engine.apply("intro p");
    engine.apply("exact outer");
    engine.qed();
}

engine.start("Πp:(Σq:(Σn:nat,n=n),(pr0 q)=(pr0 q)),True",
    { ...options, disableDestructConds: true });
const restricted = engine.apply("intro p");
assert.throws(() => engine.apply("rcases p with ⟨⟨n, hn⟩, h⟩"), /依赖假设/);
engine.apply("exact true");
assert.deepEqual(engine.undo(), restricted);
engine.apply("exact true");
engine.qed();

console.log("type-theory nested pair patterns regression passed");
