import assert from "node:assert/strict";
import { isTTAssistTacticUnlocked, TT_ASSIST_COMMANDS, TTAssistEngine } from "../js/tt/assist-engine.js";
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
assert.equal(isTTAssistTacticUnlocked("intros", new Set(["intro"])), true);

function checkQed() {
    const result = engine.qed();
    const fresh = new TTAssistEngine();
    fresh.configure(config);
    fresh.engine.core.checkType(parser.parseSurface(`${result.proof}:${result.theorem}`), [], false);
}

engine.start("True→True→True", options);
const introduced = engine.apply("intro h k");
const cleared = engine.apply("clear h");
assert.deepEqual(cleared.goals[0].context.map(([name]) => name), ["k"]);
assert.deepEqual(engine.undo(), introduced);
assert.deepEqual(engine.start("True→True→True", options, cleared.history), cleared);
assert.throws(() => engine.apply("exact h"));
engine.apply("exact k");
checkQed();

const dependent = "Πn:nat,Πp:n=n,Πq:p=p,True";
engine.start(dependent, options);
engine.apply("intro n p q");
const reverted = engine.apply("revert n");
assert.deepEqual(reverted.goals[0].context, []);
assert.equal(parser.stringify(reverted.goals[0].type), parser.stringify(parser.parseSurface(dependent)));
assert.deepEqual(engine.start(dependent, options, reverted.history), reverted);
engine.apply("intro m hm hhm");
engine.apply("exact true");
checkQed();

engine.start("True→True→True", options);
const oneIntro = engine.apply("intro");
assert.equal(oneIntro.goals[0].context.length, 1);
const twoIntros = engine.apply("intros");
assert.equal(twoIntros.goals[0].context.length, 2);
assert.equal(new Set(twoIntros.goals[0].context.map(([name]) => name)).size, 2);
const noIntro = engine.apply("intros");
assert.deepEqual(noIntro.goals, twoIntros.goals);
engine.apply("assumption");
checkQed();

// Batch argument order cannot move a dependent binder outside its type's scope.
engine.start(dependent, options, ["intro n p q"]);
assert.deepEqual(engine.apply("revert q n").goals[0].context, []);
engine.apply("intros");
engine.apply("exact true");
checkQed();

// Pair patterns reorder the display context, not the actual binder dependencies.
engine.start("(Σn:nat,n=n)→True", options);
engine.apply("rintro ⟨n,h⟩");
const pairReverted = engine.apply("revert n");
assert.equal(parser.stringify(pairReverted.goals[0].type), "(Πn:nat,(Πh:(n=n),True))");
engine.apply("intro m hm");
engine.apply("exact true");
checkQed();

function assertRollback(target, history, command, pattern) {
    const before = engine.start(target, options, history);
    assert.throws(() => engine.apply(command), pattern);
    const observed = engine.apply(`change ${parser.stringify(before.goals[0].type)}`);
    const visible = snapshot => snapshot.goals.map(goal => ({
        type: parser.stringify(goal.type), holeName: goal.holeName,
        context: goal.context.map(([name, type, id]) => [name, parser.stringify(type), id])
    }));
    assert.deepEqual(visible(observed), visible(before));
    assert.equal(parser.stringify(observed.elem), parser.stringify(before.elem));
    assert.deepEqual(observed.history.slice(0, -1), before.history);
    assert.deepEqual(engine.undo(), before);
}
for (const command of ["clear", "revert"]) {
    assert.ok(TT_ASSIST_COMMANDS.includes(command));
    assert.equal(isTTAssistTacticUnlocked(command, new Set()), false);
    assert.equal(isTTAssistTacticUnlocked(command, new Set(["intro"])), true);
    assertRollback(dependent, ["intro n p q"], command, /至少一个/);
    assertRollback(dependent, ["intro n p q"], `${command} n missing`, /找不到局部变量/);
    assertRollback(dependent, ["intro n p q"], `${command} n n`, /重复/);
    assertRollback(dependent, ["intro n p q"], `${command} (n)`, /找不到局部变量/);
    engine.start("True", options, ["exact true"]);
    assert.throws(() => engine.apply(`${command} h`), /无证明目标/);
    checkQed();
}
assertRollback(dependent, ["intro n p q"], "clear n", /依赖.*n/);
assertRollback(dependent, ["intro n p q"], "clear p", /依赖.*p/);
assertRollback("Πn:nat,n=n", ["intro n"], "clear n", /依赖.*n/);
assertRollback("True", [], "intro", /只能作用于函数类型/);

// Batch clearing allows the complete dependent group in either input order.
for (const command of ["clear n p q", "clear q p n"]) {
    engine.start(dependent, options, ["intro n p q"]);
    assert.deepEqual(engine.apply(command).goals[0].context, []);
    engine.apply("exact true");
    checkQed();
}

// Only forward dependencies move; unrelated locals remain available.
engine.start("Πn:nat,Πp:n=n,True→True", options, ["intro n p keep"]);
const partial = engine.apply("revert p");
assert.deepEqual(partial.goals[0].context.map(([name]) => name), ["keep", "n"]);
assert.equal(parser.stringify(partial.goals[0].type), "(Πp:(n=n),True)");
engine.apply("intro hp");
engine.apply("exact keep");
checkQed();

// Local lemmas, universes, and explicitly qualified constants survive abstraction.
for (const [target, script] of [
    ["True", "have h := true\nrevert h\nintro k\nexact k"],
    ["(Σn:nat,Σp:n=n,p=p)→True",
        "rintro ⟨n,⟨p,q⟩⟩\nrevert n\nintro m hm hhm\nexact true"],
    ["Πu:U@,ΠA:Uu,A→A", "intro u A a\nrevert u\nintro v B b\nexact b"],
    ["True→(0=0)", "intro h\nrevert h\nintro k\nexact @refl @0 nat 0"],
    ["nat→Πn:nat,n=n", "intro n\nclear n\nintro m\nrfl"],
    ["True→True", "intro _\nrevert h\nintros\nassumption"]
]) {
    engine.start(target, options);
    engine.apply(script);
    checkQed();
}

// A focused branch cannot change another branch's context.
engine.start("True→True×True", options);
engine.apply(`by
  intro h
  constructor
  · revert h
    intro k
    exact k
  · exact h`);
checkQed();
engine.start("True→True×True", options);
engine.apply(`by
  intro h
  constructor
  · clear h
    exact true
  · exact h`);
checkQed();

// Resolving an abstracted witness must still update its hidden dependent sibling.
engine.start("Σn:nat,n=n", options);
engine.apply(`by
  constructor
  · have h := true
    revert h
    intro k
    exact 0
  · rfl`);
checkQed();
assertRollback("True→True×True", ["intro h", "constructor"],
    "· clear h\n  exact h", /第 2 行/);

console.log("type-theory context tactics regression passed");
