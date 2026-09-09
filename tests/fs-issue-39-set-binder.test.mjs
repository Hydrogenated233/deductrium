import assert from "node:assert/strict";
import { ASTParser } from "../js/fs/astparser.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();
const expected = "(0@{z@N|~(z@{0})})<>(0@N&~(0@{0}))";

// The reported proof must specialize, commit, and replay through the kernel.
for (const command of [
    "have hs := hsall 0",
    "specialize hsall 0",
    "have he := a4 z ((z@{z@N|~(z@{0})})<>(z@N&~(z@{0}))) 0"
]) {
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, expected, { allowMcpt: false });
    for (const step of [
        "have hsall : Vz:((z@{z@N|~(z@{0})})<>(z@N&~(z@{0})))",
        "intro z",
        "exact d{@|}",
        command
    ]) assistant.apply(step);
    if (command.startsWith("have he")) assistant.apply("have hs := he hsall");
    const name = command.startsWith("have") ? "hs" : "hsall";
    assert.deepEqual(assistant.currentGoal.hypotheses.find(h => h.name === name).proposition,
        parser.parse(expected));
    assistant.apply(`exact ${name}`);
    assert.equal(assistant.qed().committed, true);
    fs.expandMacroWithProp(fs.propositions.length - 1);
    assert.deepEqual(fs.propositions.at(-1).value, parser.parse(expected));
}

// Both set forms bind child 2, but never the base set (child 1).
for (const [body, result] of [
    ["z@{z@z|z=z}", "0@{z@0|z=z}"],
    ["z@{z|z@z}", "0@{z|z@0}"],
    ["z@{y@z|y=z}", "0@{y@0|y=0}"],
    ["z@{z|y@z}", "0@{0|y@0}"],
    ["z@{z@N|Ez:(z=z)}", "0@{z@N|Ez:(z=z)}"]
]) {
    for (const right of [false, true]) {
        const fs = initFormalSystem(true).fs;
        const value = parser.parse(body);
        const matches = fs.assert.getSubAstMatchTimesAndReplace(
            value, parser.parse("z"), parser.parse("0"), -1, [], [], right);
        assert.notEqual(matches, false);
        assert.equal(parser.stringifyTight(value), parser.stringifyTight(parser.parse(result)),
            `${body}, right=${right}`);
    }
    for (const command of ["have hs := h 0", "specialize h 0"]) {
        const fs = initFormalSystem(true).fs;
        fs.addHypothese(parser.parse(`Vz:(${body})`));
        const assistant = new InferenceProofAssistant(fs, result, { allowMcpt: false });
        assistant.apply("have h := p0");
        assistant.apply(command);
        const name = command.startsWith("have") ? "hs" : "h";
        assert.deepEqual(assistant.currentGoal.hypotheses.find(h => h.name === name).proposition,
            parser.parse(result), body);
        assistant.apply(`exact ${name}`);
        assert.equal(assistant.qed().committed, true);
        fs.expandMacroWithProp(fs.propositions.length - 1);
        assert.deepEqual(fs.propositions.at(-1).value, parser.parse(result));
    }
}

// Renaming the outer variable must preserve inner set binders as well.
for (const [body, result] of [
    ["z@{z@z|z=z}", "w@{z@w|z=z}"],
    ["z@{z|z@z}", "w@{z|z@w}"]
]) {
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, `Vz:(${body})`);
    assistant.apply("intro w");
    assert.deepEqual(assistant.currentGoal.target, parser.parse(result));
}

// Capture is rejected transactionally, before recording an unmaterializable
// draft. A capture-free argument remains usable after the failed command.
for (const body of ["z@{y@N|z=y}", "z@{z|y@N}"]) {
    for (const command of ["have hs := h y", "specialize h y"]) {
        const fs = initFormalSystem(true).fs;
        fs.addHypothese(parser.parse(`Vz:(${body})`));
        const assistant = new InferenceProofAssistant(fs, "0=0");
        assistant.apply("have h := p0");
        const snapshot = assistant.snapshot();
        assert.throws(() => assistant.apply(command), /显式换名/);
        assert.deepEqual(assistant.snapshot(), snapshot);
        assert.equal(fs.propositions.length, 1);
        assistant.apply("have hs := h 0");
    }
}

// Bound occurrences inside the replacement do not capture, nor do occurrences
// inserted into the unbound base of the target set.
for (const [body, term, result] of [
    ["z@{y@N|y=y}", "y", "y@{y@N|y=y}"],
    ["z@{y@z|y=y}", "y", "y@{y@y|y=y}"],
    ["z@{y@N|z=y}", "{y@N|y=y}", "{y@N|y=y}@{y@N|{y@N|y=y}=y}"]
]) {
    const fs = initFormalSystem(true).fs;
    fs.addHypothese(parser.parse(`Vz:(${body})`));
    const assistant = new InferenceProofAssistant(fs, result, { allowMcpt: false });
    assistant.apply(`have hs := p0 ${term}`);
    assert.deepEqual(assistant.currentGoal.hypotheses.at(-1).proposition, parser.parse(result));
    assistant.apply("exact hs");
    assert.equal(assistant.qed().committed, true);
    fs.expandMacroWithProp(fs.propositions.length - 1);
    assert.deepEqual(fs.propositions.at(-1).value, parser.parse(result));
}

// Quantifier capture avoidance must rename occurrences in the base of a
// nested set while leaving its shadowing binder and body intact.
for (const quantifier of ["V", "E", "E!"]) {
    for (const [set, renamed] of [
        ["{y@y|y=y}", "{y@y'|y=y}"],
        ["{y|y@y}", "{y|y@y'}"]
    ]) {
        const fs = initFormalSystem(true).fs;
        fs.addHypothese(parser.parse(`Vx:${quantifier}y:(x@${set})`));
        const target = `${quantifier}y':(y@${renamed})`;
        const assistant = new InferenceProofAssistant(fs, target, { allowMcpt: false });
        assistant.apply("have h := p0 y");
        assert.deepEqual(assistant.currentGoal.hypotheses.at(-1).proposition, parser.parse(target));
        assistant.apply("exact h");
        assert.equal(assistant.qed().committed, true);
        fs.expandMacroWithProp(fs.propositions.length - 1);
        assert.deepEqual(fs.propositions.at(-1).value, parser.parse(target));
    }
}

// The kernel must continue to reject constants in either set binder slot.
for (const set of ["{0@N|0=0}", "{0|0@N}"]) {
    const fs = initFormalSystem(true).fs;
    assert.throws(() => new InferenceProofAssistant(fs, `0@${set}`),
        /Constant symbol|常数/);
}

console.log("GitHub issue #39 set binder specialization regression passed");
