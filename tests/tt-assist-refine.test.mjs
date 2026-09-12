import assert from "node:assert/strict";
import { isTTAssistTacticUnlocked, TT_ASSIST_COMMANDS, TTAssistEngine } from "../js/tt/assist-engine.js";
import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreSession } from "../js/tt/core-session.js";
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
assert.ok(TT_ASSIST_COMMANDS.includes("refine"));
assert.equal(isTTAssistTacticUnlocked("refine", new Set()), false);
assert.equal(isTTAssistTacticUnlocked("refine", new Set(["apply"])), true);

function checkQed() {
    const result = engine.qed();
    const session = new TTCoreSession();
    session.configure(config);
    const checked = session.validate(0, parser.parseSurface(
        `refined := ${result.proof}:${result.theorem}`));
    assert.equal(checked.ok, true, checked.error);
    assert.equal(checked.inferenceComplete, true);
    assert.doesNotMatch(result.proof, /\?refine|\?nbe|\(%|\(\?#/);
    return result;
}

const initial = engine.start("nat", options);
const partial = engine.apply("refine succ _");
assert.equal(partial.goals.length, 1);
assert.equal(parser.stringify(partial.goals[0].type), "nat");
assert.deepEqual(engine.undo(), initial);
assert.deepEqual(engine.start("nat", options, partial.history), partial);
engine.apply("exact 0");
checkQed();

engine.start("Σn:nat,n=n", options);
const pair = engine.apply("refine (0, _)");
assert.equal(pair.goals.length, 1);
assert.equal(parser.stringify(pair.goals[0].type), "(0=0)");
engine.apply("rfl");
checkQed();

engine.start("nat→nat", options);
const fn = engine.apply("refine λx:nat._");
assert.deepEqual(fn.goals[0].context.map(([name]) => name), ["x"]);
assert.equal(parser.stringify(fn.goals[0].type), "nat");
engine.apply("exact x");
checkQed();

engine.start("(Πn:nat,n=n→True)→True", options);
engine.apply("intro f");
const application = engine.apply("refine f _ _");
assert.equal(application.goals.length, 2);
assert.equal(parser.stringify(application.goals[0].type), "nat");
assert.match(parser.stringify(application.goals[1].type), /\(%/);
engine.apply("exact 0");
assert.equal(parser.stringify(engine.apply("rfl").theorem),
    parser.stringify(parser.parseSurface("(Πn:nat,n=n→True)→True")));
checkQed();

engine.start("(nat→nat)→nat", options);
engine.apply("intro f");
const argument = engine.apply("refine f ((λx:nat.x) _)");
assert.equal(argument.goals.length, 1);
engine.apply("exact 0");
checkQed();

engine.start("((nat→nat)→nat)→nat", options);
engine.apply("intro f");
const callback = engine.apply("refine f (λx:nat._)");
assert.deepEqual(callback.goals[0].context.map(([name]) => name), ["x", "f"]);
engine.apply("exact x");
checkQed();

for (const hole of ["_", "?_"]) {
    const before = engine.start("True", options);
    const after = engine.apply(`refine ${hole}`);
    assert.deepEqual(after.goals, before.goals);
    engine.apply("exact true");
    checkQed();
}

engine.start("Σn:nat,n=n", options);
const dependent = engine.apply("refine (_, ?_)");
assert.equal(dependent.goals.length, 2);
assert.match(parser.stringify(dependent.goals[1].type), /\(%/);
assert.deepEqual(engine.start("Σn:nat,n=n", options, dependent.history), dependent);
engine.apply("· exact 0");
assert.equal(parser.stringify(engine.apply("· rfl").theorem), "(Σn:nat,(n=n))");
checkQed();

// Finishing the second component early must not resolve a partial outer witness.
for (const history of [
    ["refine ((_, true), _)"],
    ["constructor", "refine (_, true)"]
]) {
    engine.start("Σp:True×True,p=p", options);
    let state;
    for (const command of history) state = engine.apply(command);
    assert.equal(state.goals.length, 2);
    assert.match(parser.stringify(state.goals[1].type), /\(%/);
    engine.apply("exact true");
    engine.apply("rfl");
    checkQed();
}

for (const [target, script] of [
    ["True", "refine true"],
    ["True×True", "refine (true, true)"],
    ["Σn:nat,n=n", "refine (_, refl 0)"],
    ["((Σn:nat,n=n)→True)→True", "intro f\nrefine f (_, refl 0)"],
    ["nat→nat", "refine λx:_._\nexact x"],
    ["Πu:U@,ΠA:Uu,A→A", "refine λu:U@.λA:Uu.λx:A._\nexact x"],
    ["(Πn:nat,Πp:n=n,p=p→True)→True", "intro f\nrefine f _ _ _\nexact 0\nrfl\nrfl"],
    ["((Σn:nat,n=n)→True)→True", "intro f\nrefine f (0, _)\nrfl"],
    ["((nat→nat)→(nat→nat)→True)→True",
        "intro f\nrefine f (λx:nat._) (λx:nat._)\n· exact x\n· exact x"],
    ["Σn:nat,n=n", "constructor\nrefine succ _\nexact 0\nrfl"]
]) {
    engine.start(target, options);
    engine.apply(script);
    checkQed();
}

engine.start("Πn:nat,Πm:nat,m=m", options);
engine.apply("intro x");
const shadowed = engine.apply("refine λx:nat._");
assert.deepEqual(shadowed.goals[0].context.map(([name]) => name), ["x'", "x"]);
assert.equal(parser.stringify(shadowed.goals[0].type), "(x'=x')");
engine.apply("rfl");
checkQed();

// Constraints may solve holes or identify multiple occurrences of the same hole.
engine.start("0=0", options);
assert.equal(engine.apply("refine refl _").goals.length, 0);
checkQed();
engine.start("(Πn:nat,Πm:nat,n=m→True)→True", options);
engine.apply("intro f");
const shared = engine.apply("refine f _ _ (refl _)");
assert.equal(shared.goals.length, 1);
engine.apply("exact 0");
checkQed();

function rollback(target, history, command, pattern) {
    const before = engine.start(target, options, history);
    assert.throws(() => engine.apply(command), pattern);
    const current = engine.apply(`change ${parser.stringify(before.goals[0].type)}`);
    const visible = snapshot => snapshot.goals.map(goal => ({
        type: parser.stringify(goal.type), hole: goal.holeName,
        context: goal.context.map(([name, type]) => [name, parser.stringify(type)])
    }));
    assert.deepEqual(visible(current), visible(before));
    assert.equal(parser.stringify(current.elem), parser.stringify(before.elem));
    assert.deepEqual(current.history.slice(0, -1), before.history);
    assert.deepEqual(engine.undo(), before);
}
rollback("True", [], "refine", /需要/);
rollback("True", [], "refine ?named", /不支持命名孔位/);
rollback("True", [], "refine missing _", /missing/);
rollback("nat", [], "refine succ true", /exact|类型/);
rollback("True×True", [], "refine (true, 0)", /exact|类型/);
rollback("True→True", [], "refine λx:False._", /相等|类型/);
rollback("True→True", [], "refine λx:True.0", /exact|类型/);
rollback("True", [], "refine (λx:_.true) _", /无法确定|类型/);
engine.start("Πf:nat→nat,f=f", options);
engine.apply("intro f");
engine.apply("refine refl (λx:nat._)");
checkQed();
rollback("True×True", [], "by\n  refine (true, _)\n  exact 0", /第 3 行/);
engine.start("True", options, ["exact true"]);
assert.throws(() => engine.apply("refine _"), /无证明目标/);
checkQed();

console.log("type-theory refine templates regression passed");
