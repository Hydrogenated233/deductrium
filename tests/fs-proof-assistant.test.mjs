import assert from "node:assert/strict";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { ASTParser } from "../js/fs/astparser.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();

function makeFs() {
    return initFormalSystem(true).fs;
}

// A failed command is transactional and must not alter the draft/history.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(fs, "$0>$0");
    assistant.apply("intro h");
    const before = assistant.snapshot();
    assert.throws(() => assistant.apply("apply _"), /暂不支持/);
    assert.deepEqual(assistant.snapshot().history, before.history);
    assert.deepEqual(assistant.snapshot().goals.map(({ id, ...goal }) => goal), before.goals.map(({ id, ...goal }) => goal));
    assistant.apply("exact h");
    assert.equal(assistant.snapshot().complete, true);
    assert.equal(assistant.qed().recordMacro, false);
    assert.equal(fs.propositions.length, 1, "bare qed stores one atomic assistant step");
    assert.equal(fs.propositions[0].deferredKind, "assistant");
    assert.equal(fs.deductions[fs.propositions[0].from.deductionIdx].steps, undefined);
    assert.throws(() => assistant.qed(), /完成|complete/);
    assistant.undo();
    assert.equal(assistant.snapshot().complete, false);
    assistant.apply("exact h");
    assert.equal(assistant.qed().committed, true, "undo must allow the proof to be completed again");
}

// Reverse application fills omitted replacement parameters and creates goals
// in rule-condition order.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(fs, "A>(B>A)");
    assistant.apply("apply a1");
    assert.equal(assistant.snapshot().complete, true);
    assert.equal(assistant.qed("fooProof").recordMacro, true);
    assert.equal(fs.propositions.length, 0, "named qed follows m semantics and clears the active page");
    assert.ok(fs.deductions.fooProof);
}

// have takes the proposition first and the binding name second; the binding is
// unavailable until its subgoal has been solved.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assistant.apply("intro h");
    assistant.apply("have A h233");
    assert.throws(() => assistant.apply("exact h233"), /尚未完成|未找到证明来源/);
    assistant.apply("exact h");
    assistant.apply("exact h233");
    assert.equal(assistant.snapshot().complete, true);
    assert.ok(assistant.qed().propositions.length >= 1);
}

// Named qed is transactional: a macro-name collision must leave both the
// page rows and the rule table exactly as they were before the attempt.
{
    const fs = makeFs();
    fs.metaCompleteTheorem(parser.parse("$0>$0"), "fooExisting", "test*");
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assistant.apply("intro h");
    assistant.apply("exact h");
    const beforeRows = fs.propositions.slice();
    const beforeRules = Object.keys(fs.deductions).sort();
    assert.throws(() => assistant.qed("fooExisting"), /已存在|already exists/);
    assert.deepEqual(fs.propositions, beforeRows);
    assert.deepEqual(Object.keys(fs.deductions).sort(), beforeRules);
}

// qed naming uses the legacy macro reservation rules at every public entry
// point, including a materialized preview that has not been committed yet.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assistant.apply("intro h");
    assistant.apply("exact h");
    assert.throws(() => assistant.materializeQed("foo:bar"), /名称|name/);
    assert.throws(() => assistant.materializeQed("aReserved"), /保留|reserved/);
}

// A preview is bound to its assistant and to the exact page contents captured
// at materialization time. Same-length replacement must still invalidate it.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assistant.apply("intro h");
    assistant.apply("exact h");
    const preview = assistant.materializeQed();
    fs.propositions[0] = { value: parser.parse("B"), from: null };
    assert.throws(() => assistant.commit(preview), /过期|stale/);

    const other = new InferenceProofAssistant(fs, "A>A");
    assert.throws(() => other.commit(preview), /不属于当前证明助手/);
}

// A tauto helper name occupied by another proof must not silently bind the
// current proof to the other theorem.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(fs, "$0>$0");
    assistant.apply("tauto");
    fs.metaCompleteTheorem(parser.parse("B>B"), "__tauto_1", "test*");
    assert.throws(() => assistant.qed(), /tauto|冲突/);
}

// A materialized preview becomes stale if the selected page changes before it
// is committed; reject it without mutating the page.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assistant.apply("intro h");
    assistant.apply("exact h");
    const preview = assistant.materializeQed();
    fs.addHypothese(parser.parse("B"));
    const beforeRows = fs.propositions.slice();
    assert.throws(() => assistant.commit(preview), /过期|stale/);
    assert.deepEqual(fs.propositions, beforeRows);
}

// tauto validates through the existing MCPT implementation but materializes
// as one deferred node instead of persisting enumeration internals.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(fs, "$0>$0");
    const before = Object.keys(fs.deductions);
    assistant.apply("tauto");
    assert.deepEqual(Object.keys(fs.deductions), before, "tauto must not mutate shared rules while editing");
    const qed = assistant.qed();
    assert.equal(qed.propositions.length, 1);
    assert.equal(qed.propositions[0].deferredKind, "assistant");
    assert.equal(fs.deductions[qed.propositions[0].from.deductionIdx].deferredKind, "assistant");
    assert.equal(fs.deductions[qed.propositions[0].from.deductionIdx].steps, undefined);
}

// Omitted intro names are generated consistently for both implications and
// universal binders.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(fs, "Vx:($0>$0)");
    assistant.apply("intro");
    assert.equal(assistant.currentGoal.hypotheses[0].name, "h1");
    assert.equal(assistant.currentGoal.hypotheses[0].kind, "variable");
    assert.equal(assistant.currentGoal.hypotheses[0].proposition, undefined,
        "a universal binder must not be presented as a proposition hypothesis");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "$0>$0");
}

// `intros` introduces a named prefix atomically and can also consume every
// leading implication/universal binder when no names are supplied.
{
    const fs = makeFs();
    const named = new InferenceProofAssistant(fs, "A>(Vx:($0>$0))");
    named.apply("intros ha x");
    assert.deepEqual(named.currentGoal.hypotheses.map(h => h.name), ["ha", "x"]);
    assert.equal(named.currentGoal.hypotheses[1].kind, "variable");

    const automatic = new InferenceProofAssistant(fs, "A>(Vx:($0>$0))");
    automatic.apply("intros");
    assert.deepEqual(automatic.currentGoal.hypotheses.map(h => h.name), ["h1", "h2", "h3"]);
    assert.equal(parser.stringifyTight(automatic.currentGoal.target), "$0");
}

// Nested universal binders remain variables; only the implication premise is
// shown as a proposition hypothesis after `intros`.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(fs, "Vx:(Va:(((x=1)&(a=1))>(x=a)))");
    assistant.apply("intros ha hb hand");
    assert.deepEqual(assistant.currentGoal.hypotheses.map(h => h.kind), ["variable", "variable", "intro"]);
    assert.equal(assistant.currentGoal.hypotheses[0].proposition, undefined);
    assert.equal(assistant.currentGoal.hypotheses[1].proposition, undefined);
    assert.equal(parser.stringifyTight(assistant.currentGoal.hypotheses[2].proposition), "(ha=1)&(hb=1)");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "ha=hb");
}

// exact accepts a proposition's surface expression and resolves it within the
// active page, without crossing into another inference page.
{
    const fs = makeFs();
    fs.addHypothese(parser.parse("A"));
    const assistant = new InferenceProofAssistant(fs, "A");
    assistant.apply("exact A");
    assert.equal(assistant.snapshot().complete, true);
}

// Universal intro is capture avoiding: the user variable y must not capture a
// nested V y binder when substituting the outer x.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(fs, "Vx:Vy:x=y");
    assistant.apply("intro y");
    const shown = assistant.currentGoal.target;
    assert.equal(shown.name, "V");
    assert.notEqual(shown.nodes[0].name, "y");
    assert.equal(shown.nodes[1].nodes[0].name, "y");
}

// apply accepts a local implication and creates one goal per premise in
// left-to-right order.  qed materializes the implication chain through mp.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(fs, "A>(B>((A>(B>C))>C))");
    assistant.apply("intro ha");
    assistant.apply("intro hb");
    assistant.apply("intro h");
    assistant.apply("apply h");
    assert.deepEqual(assistant.snapshot().goals.map(goal => parser.stringifyTight(goal.target)), ["A", "B"]);
    assistant.apply("exact ha");
    assistant.apply("exact hb");
    const result = assistant.qed();
    assert.equal(result.committed, true);
    assert.equal(result.steps.length, 1, "qed emits one atomic step");
    fs.expandMacroWithProp(0);
    assert.equal(fs.deductions[result.deductionName].steps.filter(step => step.deductionIdx === "mp").length >= 2, true);
}

// Stop at the earliest implication suffix matching the target. A target which
// is itself an implication must not be split again. This is the exact
// `$`-named proposition reported by the UI.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(
        fs,
        "((~~~$>~$)>($>~~$))>((~~~$>~$)>($>~~$))"
    );
    assistant.apply("intro h1");
    assistant.apply("intro h2");
    assistant.apply("apply h1");
    assert.deepEqual(
        assistant.snapshot().goals.map(goal => parser.stringifyTight(goal.target)),
        ["~~~$>~$"]
    );
    assistant.apply("exact h2");
    assert.equal(assistant.snapshot().complete, true);
    assert.equal(assistant.qed().committed, true);
}

// `$0`/`$1` inside a local hypothesis are fixed proposition variables, not
// schema metavariables. Only shared inference rules may instantiate them.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(fs, "(~~$1>$1)>(~~$0>~~$1)");
    assistant.apply("intro h1");
    const before = assistant.snapshot();
    assert.equal(assistant.recommendations().includes("apply h1"), false);
    assert.throws(() => assistant.apply("apply h1"), /不匹配/);
    assert.deepEqual(assistant.snapshot(), before, "failed local apply must leave the goal unchanged");
}

// Page propositions can supply both the implication and its premise.  Named
// qed must copy both external premises into the recorded macro transaction.
{
    const fs = makeFs();
    fs.addHypothese(parser.parse("A>B"));
    fs.addHypothese(parser.parse("A"));
    const assistant = new InferenceProofAssistant(fs, "B");
    assistant.apply("apply p0");
    assistant.apply("exact p1");
    const result = assistant.qed("fooPageImplicationProof");
    assert.equal(result.recordMacro, true);
    assert.ok(fs.deductions.fooPageImplicationProof);
    assert.equal(fs.propositions.length, 0);
}

// Local names have priority over shared rules with the same name.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assistant.apply("intro a1");
    assistant.apply("exact a1");
    assert.equal(assistant.snapshot().complete, true);
}

// exact cannot consume a conditional source, while apply can expose its
// premise. Shared conditional rules retain the same distinction.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(fs, "(A>B)>B");
    assistant.apply("intro h");
    assert.throws(() => assistant.apply("exact h"), /不匹配/);
    assistant.apply("apply h");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "A");

    const shared = new InferenceProofAssistant(makeFs(), "A");
    assert.throws(() => shared.apply("exact mp"), /包含条件/);
}

// A pending have cannot be used recursively. `$0` in a page proposition is a
// fixed premise rather than a source parameter, so apply exposes it verbatim.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(fs, "B");
    assistant.apply("have A>B h233");
    assert.throws(() => assistant.apply("apply h233"), /尚未完成/);

    const schematicFs = makeFs();
    schematicFs.addHypothese(parser.parse("$0>B"));
    const schematic = new InferenceProofAssistant(schematicFs, "B");
    schematic.apply("apply p0");
    assert.equal(parser.stringifyTight(schematic.currentGoal.target), "$0");
}

// Recommendations are syntax candidates. apply candidates only inspect the
// local hypothesis environment, and tauto stays hidden until CPT is unlocked.
{
    const fs = makeFs();
    fs.addHypothese(parser.parse("A>B"));
    fs.addHypothese(parser.parse("A"));
    const assistant = new InferenceProofAssistant(fs, "B");
    const locked = assistant.recommendations({ ruleNames: ["mp", "a1"], canTauto: false });
    assert.equal(locked.includes("apply p0"), false, "page propositions are not apply recommendations");
    assert.equal(locked.includes("apply mp"), false, "shared rules are not apply recommendations");
    assert.equal(locked.includes("tauto"), false);
    assert.ok(assistant.recommendations({ ruleNames: ["mp"], canTauto: true }).includes("tauto"));

    const local = new InferenceProofAssistant(makeFs(), "(A>B)>B");
    local.apply("intro h");
    assert.ok(local.recommendations().includes("apply h"));

    const exactRule = new InferenceProofAssistant(makeFs(), "A>(B>A)");
    assert.ok(exactRule.recommendations({ ruleNames: ["a1"] }).includes("exact a1"));
}

// Shared rules remain manually applicable even though apply-rule candidates
// are intentionally absent from the recommendation list.
{
    const fs = makeFs();
    const assistant = new InferenceProofAssistant(fs, "A>(B>A)");
    assistant.apply("intro h");
    assistant.apply("apply a1");
    assert.equal(parser.stringifyTight(assistant.currentGoal.target), "A");
    assistant.apply("exact h");
    assert.equal(assistant.qed().committed, true);
}

console.log("inference proof-assistant model regression passed");
