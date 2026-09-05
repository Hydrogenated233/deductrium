import assert from "node:assert/strict";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { ASTParser } from "../js/fs/astparser.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();
const fs = initFormalSystem(false).fs;
fs.addDeduction("issue29Symm", parser.parse("$0=$1⊢$1=$0"), "test");
fs.addDeduction("issue29Subst", parser.parse("⊢($0=$1)>($2>#rp($2,$0,$1,$3))"), "test");
fs.addDeduction("issue29Rfl", parser.parse("⊢$0=$0"), "test");
const ruleNames = ["mp", "a1", "a2", "d3", "issue29Symm", "issue29Subst", "issue29Rfl"];

// A concrete rewrite must not be poisoned by an unrelated user metavariable
// in a sibling target branch.  The old matcher returned `false` for the whole
// traversal and then failed while locating the inverse rewrite occurrence.
const assistant = new InferenceProofAssistant(fs, "($0*3)=($0*3)", { ruleNames });
assistant.apply("have h3 := d3");
assistant.apply("rw h3");
assert.equal(parser.stringifyTight(assistant.currentGoal.target), "($0*S(2))=($0*S(2))");

// The concrete-source exception must not turn an unknown target into a match:
// when the target contains no `3`, `rw h3` still reports a missing occurrence.
const missing = new InferenceProofAssistant(fs, "($0*4)=($0*4)", { ruleNames });
missing.apply("have h3 := d3");
assert.throws(() => missing.apply("rw h3"), /未找到可改写项/);

console.log("GitHub issue #29 rw concrete rewrite regression passed");
