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

console.log("GitHub issue #15 named-qed premise-order regression passed");
