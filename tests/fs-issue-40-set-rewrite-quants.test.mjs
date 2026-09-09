import assert from "node:assert/strict";
import { ASTParser } from "../js/fs/astparser.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();
const options = { allowMcpt: false };
const spelling = value => parser.stringifyTight(value);
const expectTarget = (assistant, text) =>
    assert.equal(spelling(assistant.currentGoal.target), spelling(parser.parse(text)));

for (const [a, b, c, z] of [
    ["$a", "$b", "$c", "#z"],
    ["a", "b", "c", "#z"],
    ["a", "b", "c", "z"]
]) {
    const target = `${c}\\(${a}U${b})=(${c}\\${a})I(${c}\\${b})`;
    const left = `{${z}@${c}|~(${z}@(${a}U${b}))}`;
    const rightA = `{${z}@${c}|~(${z}@${a})}`;
    const rightB = `{${z}@${c}|~(${z}@${b})}`;
    const definitions = [
        `have hdL := d\\ $a=${c} $b=(${a}U${b}) $c=${z}`,
        `have hdA := d\\ $a=${c} $b=${a} $c=${z}`
    ];
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, target, options);
    for (const command of [...definitions, "rw hdL"]) assistant.apply(command);
    const before = assistant.snapshot();
    assistant.apply("rw hdA");
    expectTarget(assistant, `${left}=(${rightA}I(${c}\\${b}))`);
    assistant.undo();
    assert.deepEqual(assistant.snapshot(), before);
    assistant.apply("rw hdA");
    const restored = new InferenceProofAssistant(fs, target, options);
    restored.restore(JSON.parse(JSON.stringify(assistant.snapshot())));
    restored.apply(`have hdB := d\\ $a=${c} $b=${b} $c=${z}`);
    restored.apply("rw hdB");
    expectTarget(restored, `${left}=(${rightA}I${rightB})`);
    for (const command of ["rw <-hdB", "rw <-hdA", "rw <-hdL"]) restored.apply(command);
    expectTarget(restored, target);
    assert.deepEqual(fs.propositions, [], "rewriting must remain draft-only");

    // A closed identity exercises the same consecutive rewrites through qed,
    // without assuming the unproved distribution theorem from the playthrough.
    for (const name of [undefined, "issue40Rewrite"]) {
        const proofSystem = initFormalSystem(true).fs;
        const item = `(${c}\\(${a}U${b}))I(${c}\\${a})`;
        const theorem = `${item}=${item}`;
        const proof = new InferenceProofAssistant(proofSystem, theorem, options);
        for (const command of [...definitions, "rw hdL", "rw hdA", "rfl"]) proof.apply(command);
        assert.equal(proof.qed(name).committed, true);
        if (name) {
            assert.deepEqual(proofSystem.deductions[name].conditions, []);
            proofSystem.deduct({
                deductionIdx: name, conditionIdxs: [],
                replaceValues: proofSystem.deductions[name].replaceNames.map(value => parser.parse(value))
            });
        }
        proofSystem.expandMacroWithProp(0);
        assert.equal(spelling(proofSystem.propositions.at(-1).value), spelling(parser.parse(theorem)));
        assert.ok(proofSystem.propositions.every(row => row.from));
    }
}

// The matcher must still reject bound sources, unknown non-freeness, and
// destinations that would be captured, for both set constructors.
for (const [source, destination, message] of [
    ["{y@N|y=z}", "N", /未找到可改写项/],
    ["{y@N|y=$a}", "N", /捕获变量/],
    ["{y@N|y=a}", "{y@N|y=z}", /捕获|替换位置/],
    ["{z|y@N}", "N", /未找到可改写项/],
    ["{$a|y@N}", "N", /捕获变量/],
    ["{a|y@N}", "{z|y@N}", /捕获|替换位置/]
]) {
    for (const command of ["rw p0", "nth_rw 1 p0"]) {
        const fs = initFormalSystem(true).fs;
        fs.addHypothese(parser.parse(`${source}=${destination}`));
        const assistant = new InferenceProofAssistant(fs, `Vz:(${source}=${source})`, options);
        const snapshot = assistant.snapshot();
        const rows = structuredClone(fs.propositions);
        assert.throws(() => assistant.apply(command),
            error => !(error instanceof TypeError) && message.test(String(error)));
        assert.deepEqual(assistant.snapshot(), snapshot);
        assert.deepEqual(fs.propositions, rows);
    }
}

console.log("GitHub issue #40 set rewrite quantifier-scope regression passed");
