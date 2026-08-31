import assert from "node:assert/strict";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { ASTParser } from "../js/fs/astparser.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();
const fs = initFormalSystem(true).fs;

// The page order is p0, p1, but the proof tree deliberately consumes p1
// before p0.  A named qed must preserve the page's premise order in the
// recorded deduction so strict #d gates can match it.
fs.addHypothese(parser.parse("$0=$1"));
fs.addHypothese(parser.parse("$1=$2"));
const assistant = new InferenceProofAssistant(fs, "$0=$2");
assistant.apply("apply a8 $0=$1 $1=$2 $2=($0=$1) $3=-1");
assistant.apply("exact p1");
assistant.apply("exact p0");
const result = assistant.qed("issue15EqTrans");

assert.deepEqual(result.propositions[0].from.conditionIdxs, [0, 1]);
assert.deepEqual(fs.deductions.issue15EqTrans.conditions.map(value => parser.stringifyTight(value)), [
    "$0=$1",
    "$1=$2"
]);

// The deferred recipe and its eventual materialization must use the same
// stable ordering, rather than reintroducing [1, 0] on expansion.
assert.deepEqual(result.propositions[0].from.assistant.premises.map(premise => premise.index), [0, 1]);
const materialized = fs.materializeDeferredDeduction("issue15EqTrans");
assert.ok(materialized.steps?.length);
assert.equal(parser.stringifyTight(materialized.conclusion), "$0=$2");

// GitHub issue #18: a named qed has the same page-scope semantics as the
// legacy `hyp ...; m name` flow.  Every leading page hypothesis is therefore
// a rule condition, even when the proof tree does not reference it directly.
const scopedFs = initFormalSystem(true).fs;
scopedFs.addHypothese(parser.parse("A>B"));
scopedFs.addHypothese(parser.parse("A"));
scopedFs.addHypothese(parser.parse("C"));
const scopedAssistant = new InferenceProofAssistant(scopedFs, "B");
scopedAssistant.apply("apply p0");
scopedAssistant.apply("exact p1");
const scopedResult = scopedAssistant.qed("issue18PageScope");

assert.deepEqual(scopedResult.propositions[0].from.conditionIdxs, [0, 1, 2]);
assert.deepEqual(
    scopedResult.propositions[0].from.assistant.premises.map(premise => premise.index),
    [0, 1, 2]
);
assert.deepEqual(
    scopedFs.deductions.issue18PageScope.conditions.map(value => parser.stringifyTight(value)),
    ["A>B", "A", "C"]
);
assert.ok(scopedFs.materializeDeferredDeduction("issue18PageScope").steps?.length);

// The reported sequence used only p0 to change both components. Rule arguments
// containing user `$` names are rigid: reject the mismatching a8 immediately
// instead of accepting it as a second schema match and failing only at qed.
const rejectedFs = initFormalSystem(true).fs;
rejectedFs.addHypothese(parser.parse("$a1=$a2"));
const rejectedAssistant = new InferenceProofAssistant(
    rejectedFs,
    "($a1@$b1)>($a2@$b2)"
);
rejectedAssistant.apply("intro h");
const rejectedSnapshot = rejectedAssistant.snapshot();
assert.throws(
    () => rejectedAssistant.apply("apply a8 $0=$a1 $1=$a2 $2=$a1@$b1 $3=-1"),
    /规则结论与当前目标不匹配/
);
assert.deepEqual(rejectedAssistant.snapshot(), rejectedSnapshot);

// A valid two-component proof uses both page hypotheses. Payload construction
// and deferred replay must retain the same complete page scope.
const reportedFs = initFormalSystem(true).fs;
reportedFs.addHypothese(parser.parse("$a1=$a2"));
reportedFs.addHypothese(parser.parse("$b1=$b2"));
const reportedAssistant = new InferenceProofAssistant(
    reportedFs,
    "($a1@$b1)<>($a2@$b2)"
);
for (const command of [
    "constructor",
    "intro h",
    "apply a8 $0=$b1 $1=$b2 $2=$a2@$b1 $3=-1",
    "exact p1",
    "apply a8 $0=$a1 $1=$a2 $2=$a1@$b1 $3=-1",
    "exact p0",
    "exact h",
    "intro h2",
    "apply a8 $0=$b2 $1=$b1 $2=$a1@$b2 $3=-1",
    "symm",
    "exact p1",
    "apply a8 $0=$a2 $1=$a1 $2=$a2@$b2 $3=-1",
    "symm",
    "exact p0",
    "exact h2"
]) reportedAssistant.apply(command);
const reportedResult = reportedAssistant.qed("issue18ReportedRepro");
assert.deepEqual(reportedResult.propositions[0].from.conditionIdxs, [0, 1]);
assert.deepEqual(
    reportedFs.deductions.issue18ReportedRepro.conditions.map(value => parser.stringifyTight(value)),
    ["$a1=$a2", "$b1=$b2"]
);
assert.ok(reportedFs.materializeDeferredDeduction("issue18ReportedRepro").steps?.length);

console.log("GitHub issues #15/#18/#19 proof-assistant premise regressions passed");
