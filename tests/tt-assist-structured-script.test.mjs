import assert from "node:assert/strict";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";
import { locateTTTacticError, parseTTTacticScript } from "../js/tt/tactic-script.js";
import { expandTypeTheoryAliasesInSurface } from "../js/tt/symbol-aliases.js";

const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_", timeout: 30_000, language: "zh"
};
const options = {
    disableMultipleApply: false, disableDestructConds: false, disableDestructEq: false
};
const engine = new TTAssistEngine();
const parser = new ASTParser();
engine.configure(config);
assert.equal(expandTypeTheoryAliasesInSurface("\\cdot rfl"), "· rfl");
assert.equal(parseTTTacticScript("\\cdot rfl")[0].kind, "focus");
for (const prefix of ["", "Error: ", "TTProcessExecutionError: Error: "]) {
    assert.deepEqual(locateTTTacticError(`${prefix}第 2 行：failure`, 9),
        { lineNumber: 10, message: "failure" });
}
assert.equal(locateTTTacticError("unrelated failure", 9), null);

function checkQed() {
    const result = engine.qed();
    engine.engine.core.checkType(parser.parseSurface(`${result.proof}:${result.theorem}`), [], false);
    const fresh = new TTCoreSession();
    fresh.configure(config);
    const reloaded = fresh.validate(0,
        parser.parseSurface(`structuredProof := ${result.proof}:${result.theorem}`));
    assert.equal(reloaded.ok, true, reloaded.error);
    assert.equal(reloaded.inferenceComplete, true);
    return result;
}

const script = `by
  -- A local lemma with its own branches.
  intro h
  have pair : True×True := by
    constructor
    · exact h
    · exact h
  exact pair
qed pairProof`;
const nodes = parseTTTacticScript(script);
assert.deepEqual(nodes.map(node => node.lineNumber), [3, 4, 8, 9]);
assert.deepEqual(nodes.map(node => node.kind), ["tactic", "have", "tactic", "tactic"]);
assert.equal(nodes[1].source, `have pair : True×True := by
  constructor
  · exact h
  · exact h`);
assert.deepEqual(parseTTTacticScript(nodes[1].source)[0].body.map(node => node.kind),
    ["tactic", "focus", "focus"]);

engine.start("True→True×True", options);
const beforeHave = engine.apply(nodes[0].source);
const afterHave = engine.apply(nodes[1].source);
assert.equal(afterHave.goals.length, 1);
assert.equal(afterHave.goals[0].context[0][0], "pair");
assert.deepEqual(afterHave.history, ["intro h", nodes[1].source]);
assert.deepEqual(engine.undo(), beforeHave);
assert.deepEqual(engine.start("True→True×True", options, afterHave.history), afterHave);
engine.apply(nodes[2].source);
checkQed();

// Printed kernel constructors must not be captured by a same-named local fact.
engine.start("True→(True×True)×True", options);
engine.apply(`by
  intro h
  have pair : True×True := by
    constructor
    · exact h
    · exact h
  constructor
  · exact pair
  · exact h`);
const shadowed = checkQed();
assert.match(shadowed.proof, /@pair/);

// Whole scripts are accepted by the same engine interface used by the Worker.
// At the GUI boundary each top-level block remains a separate undo entry.
const nested = `by
  constructor
  · constructor
    · exact true
    · exact true
  · exact by
      exact true`;
const initial = engine.start("(True×True)×True", options);
const completed = engine.apply(nested);
assert.equal(completed.goals.length, 0);
const nestedQed = checkQed();
assert.deepEqual(engine.undo(), initial);
assert.deepEqual(engine.start("(True×True)×True", options, completed.history), completed);
assert.deepEqual(checkQed(), nestedQed);

// A focused witness must resolve the hidden dependent sibling, not a copy.
engine.start("Σn:nat,n=n", options);
engine.apply("constructor");
const witness = engine.apply("· exact 0");
assert.equal(witness.goals.length, 1);
assert.equal(parser.stringify(witness.goals[0].type), "(0=0)");
engine.apply("· rfl");
checkQed();
engine.start("True×True", options);
engine.apply("by\n  constructor\n  \\cdot exact true\n  \\cdot exact true");
checkQed();

// A lemma can itself be the witness of a dependent outer constructor.
engine.start("Σn:nat,n=n", options);
engine.apply("constructor");
engine.apply(`· have n : nat := by
    exact 0
  exact n`);
engine.apply("· rfl");
checkQed();

// Local facts are scoped to their branch.
engine.start("True×True", options);
engine.apply("constructor");
const branch = engine.apply(`· have local : True := by exact true
  exact local`);
assert.equal(branch.goals.length, 1);
assert.ok(!branch.goals[0].context.some(([name]) => name === "local"));
assert.throws(() => engine.apply("exact local"));
engine.apply("exact true");
checkQed();

function assertRollback(target, history, command, pattern) {
    const before = engine.start(target, options, history);
    assert.throws(() => engine.apply(command), pattern);
    // A no-op target change reads the live session without resetting it.
    const observed = engine.apply(`change ${parser.stringify(before.goals[0].type)}`);
    const visibleGoals = snapshot => snapshot.goals.map(goal => ({
        type: parser.stringify(goal.type), holeName: goal.holeName,
        context: goal.context.map(([name, type, id]) => [name, parser.stringify(type), id])
    }));
    assert.deepEqual(visibleGoals(observed), visibleGoals(before));
    assert.equal(parser.stringify(observed.elem), parser.stringify(before.elem));
    assert.deepEqual(observed.history.slice(0, -1), before.history);
    assert.deepEqual(engine.undo(), before);
}

assertRollback("True×True", ["constructor"],
    "· exact true\n  exact true", /第 2 行.*无证明目标/s);
assertRollback("True×True", [],
    "· constructor\n  exact true", /子证明尚未完成/);
assertRollback("True", [],
    "have pair : True×True := by\n  constructor\n  exact true", /子证明尚未完成/);
assertRollback("True", [],
    "have pair : True×True := by\n  constructor\n  exact true\n  exact 0", /第 4 行/);
assertRollback("True", [], "have h := by exact true", /have未提供类型或证明项/);
assertRollback("True×True", ["constructor"], "exact by\n  exact true\n  exact true",
    /无证明目标/);
for (const internal of ["toString", "resolveDependGoal", "executeFocused", "autofillTactics"]) {
    assertRollback("True", [], internal, /未知的证明策略/);
}
assertRollback("True", [], "by\n  exact true\n  qed", /未知的证明策略/);

engine.start("True→True", options);
engine.apply("intro\th");
engine.apply("exact by exact h");
checkQed();
assert.deepEqual(parseTTTacticScript("\n-- empty\n"), []);
assert.equal(parseTTTacticScript("exact true -- comment")[0].command, "exact true");
assert.equal(parseTTTacticScript("exact true .")[0].command, "exact true");
for (const malformed of [
    "by", "·", "exact by", "have h : True := by",
    "by\nexact true", "constructor\n  exact true",
    "by\n  constructor\n    · exact true",
    "by\n\texact true", "by\n  exact true\n exact true"
]) {
    assert.throws(() => parseTTTacticScript(malformed), /第 \d+ 行/);
}
assert.throws(() => parseTTTacticScript(
    `${"· ".repeat(66)}exact true`
), /嵌套过深/);
assert.throws(() => parseTTTacticScript(
    Array(4097).fill("rfl").join("\n")
), /脚本过大/);

console.log("type-theory structured tactic scripts regression passed");
