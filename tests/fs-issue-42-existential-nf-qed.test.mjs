import assert from "node:assert/strict";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { ASTParser } from "../js/fs/astparser.js";
import { initFormalSystem } from "../js/fs/initial.js";
import { SavesParser } from "../js/fs/savesparser.js";
import { expandInferenceSnapshot } from "../js/fs/inference-worker-core.js";

const parser = new ASTParser();
const commands = ["intro h", "obtain <u,hu> := h", "use u", "exact hu"];
const spelling = (fs, value) => {
    const ast = parser.parse(typeof value === "string" ? value : parser.stringifyTight(value));
    fs.assert.expand(ast, false);
    return parser.stringifyTight(ast);
};

for (const [term, binder] of [
    ["#nf($1,x,u)", "x"], ["#nf($1,u,x)", "x"],
    ["#nf($1,x,u,y)", "y"], ["a", "x"], ["$1", "x"]
]) {
    const target = `(Ex:x=${term})>(E${binder}:${binder}=${term})`;
    for (const name of [undefined, "issue42ExistentialIdentity"]) {
        const fs = initFormalSystem(true).fs;
        const assistant = new InferenceProofAssistant(fs, target, { allowMcpt: false });
        for (const command of commands) assistant.apply(command);
        assert.equal(assistant.snapshot().complete, true);
        const restored = new InferenceProofAssistant(fs, target, { allowMcpt: false });
        restored.restore(JSON.parse(JSON.stringify(assistant.snapshot())));
        assert.equal(restored.qed(name).committed, true);
        if (name) {
            assert.deepEqual(fs.deductions[name].conditions, []);
            fs.deduct({
                deductionIdx: name, conditionIdxs: [],
                replaceValues: fs.deductions[name].replaceNames.map(value => parser.parse(value))
            });
        } else if (term === "#nf($1,x,u)") {
            const save = new SavesParser(false).serialize({
                formalSystem: fs, deductions: Object.keys(fs.deductions), metarules: [],
                getProps: () => fs.propositions, pageStore: fs.inferencePages
            });
            const expanded = expandInferenceSnapshot({
                save, creative: true, fastMetaRules: "cvuqe><:#zZQR", metarules: [],
                target: { kind: "proposition", index: 0 }
            });
            const rows = JSON.parse(expanded.save).data[7].pages[0].propositions;
            assert.equal(spelling(fs, rows.at(-1)[0]), spelling(fs, target));
            assert.ok(rows.every(row => row[1] && row[1][0] !== "__assistant"));
            assert.equal(fs.propositions.length, 1);
        }
        fs.expandMacroWithProp(0);
        assert.equal(spelling(fs, fs.propositions.at(-1).value), spelling(fs, target));
        assert.ok(fs.propositions.every(row => row.from));
    }
}

// Direct identity remains valid without unpacking the existential.
{
    const fs = initFormalSystem(true).fs;
    const target = "(Ex:x=#nf($1,x,u))>(Ex:x=#nf($1,x,u))";
    const assistant = new InferenceProofAssistant(fs, target, { allowMcpt: false });
    for (const command of ["intro h", "exact h"]) assistant.apply(command);
    assistant.qed();
    fs.expandMacroWithProp(0);
    assert.equal(spelling(fs, fs.propositions.at(-1).value), spelling(fs, target));
}

// Normalizing candidates cannot turn unknown non-freeness into a guarantee.
for (const name of [undefined, "issue42InvalidGeneralization"]) {
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs,
        "#nf($0,x)>(Vy:#nf($0,x))", { allowMcpt: false });
    for (const command of ["intro h", "intro y", "exact h"]) assistant.apply(command);
    assert.equal(assistant.snapshot().complete, true);
    const before = assistant.snapshot();
    const rows = structuredClone(fs.propositions);
    const rules = Object.keys(fs.deductions);
    for (let attempt = 0; attempt < 2; attempt++) {
        assert.throws(() => assistant.qed(name), /无法确认全称变量.*不自由出现/);
        assert.deepEqual(assistant.snapshot(), before);
        assert.deepEqual(fs.propositions, rows);
        assert.deepEqual(Object.keys(fs.deductions), rules);
    }
}

console.log("GitHub issue #42 existential nf qed regression passed");
