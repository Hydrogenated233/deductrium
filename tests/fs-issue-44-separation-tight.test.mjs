import assert from "node:assert/strict";
import { ASTParser } from "../js/fs/astparser.js";
import { AssertionSystem } from "../js/fs/assertion.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { initFormalSystem } from "../js/fs/initial.js";
import { SavesParser } from "../js/fs/savesparser.js";
import { expandInferenceSnapshot } from "../js/fs/inference-worker-core.js";

const parser = new ASTParser();
const assertion = new AssertionSystem();

// Parser roundtrips also preserve grouping before semantic grammar validation.
for (const [term, expected] of [
    ["{($0>$1)|x@y}", "{($0\u2192$1)|x@y}"],
    ["{($0<>$1)|x@y}", "{($0\u2194$1)|x@y}"]
]) {
    const ast = parser.parse(term);
    assert.equal(ast.name, "|}");
    const tight = parser.stringifyTight(ast);
    assert.equal(tight, expected, "replacement expression must retain parentheses and Unicode");
    assert.deepEqual(parser.parse(tight), ast, `replacement expression roundtrip: ${term}`);
}

const terms = [
    "{p@a|(p=z|p@b)}",
    "{p@a|(~p=z>p@b)}",
    "{p@a|(p=z<>p@b)}",
    "{p@a|(p=z&p@b)}",
    "{p@a|~(p=z|p@b)}",
    "{p@a|Et:(p=z|p@b)}",
    "{p@a|p=z}",
    "{p@a|$0}",
    "{p@{q@a|(q=z|q@b)}|(p=z|p@b)}",
    "{{q@a|(q=z|q@b)}|p@a}",
    "{(pUz)|p@(aUb)}"
];

for (const term of terms) {
    const ast = parser.parse(term);
    assertion.checkGrammer(ast, "i");
    assert.deepEqual(parser.parse(parser.stringify(ast)), ast);
    const tight = parser.stringifyTight(ast);
    const restored = parser.parse(tight);
    assertion.checkGrammer(restored, "i");
    assert.deepEqual(restored, ast, `tight roundtrip: ${term}`);
    assert.equal(parser.stringifyTight(restored), tight);
}

for (const term of terms.slice(0, 6)) {
    for (const name of [undefined, "issue44Witness"]) {
        const fs = initFormalSystem(false).fs;
        const target = `Ex:x=${term}`;
        const assistant = new InferenceProofAssistant(fs, target, { allowMcpt: false });
        const initial = assistant.snapshot();
        assistant.apply(`use ${term}`);
        assistant.undo();
        assert.deepEqual(assistant.snapshot(), initial);
        assistant.apply(`use ${term}`);
        assistant.apply("rfl");
        assert.equal(assistant.snapshot().complete, true);
        const replay = new InferenceProofAssistant(fs, target, { allowMcpt: false });
        replay.restore(structuredClone(assistant.snapshot()));
        assert.equal(replay.qed(name).committed, true);
        if (name) {
            assert.deepEqual(fs.deductions[name].conditions, []);
            fs.deduct({
                deductionIdx: name, conditionIdxs: [],
                replaceValues: fs.deductions[name].replaceNames.map(value => parser.parse(value))
            });
        }
        fs.expandMacroWithProp(0);
        assert.deepEqual(fs.propositions.at(-1).value, parser.parse(target));
        assert.ok(fs.propositions.every(row => row.from));
    }
}

// The GUI's qed path serializes both the target and the resulting deferred
// proof across the worker boundary, then restores them through the save parser.
{
    const fs = initFormalSystem(false).fs;
    const saves = new SavesParser(false);
    const target = `Ex:x=${terms[0]}`;
    const rules = Object.keys(fs.deductions);
    const save = saves.serialize({
        formalSystem: fs, deductions: rules, metarules: [],
        pageStore: fs.inferencePages, getProps: () => fs.propositions
    });
    const result = expandInferenceSnapshot({
        save, creative: false, fastMetaRules: fs.fastmetarules, metarules: [],
        target: {
            kind: "qed", theorem: parser.parse(target),
            history: [`use ${terms[0]}`, "rfl"], pageId: fs.inferencePages.activeId,
            ruleNames: rules, allowMcpt: false, allowIfft: false, allowIfftEu: false
        }
    });
    assert.equal(result.qed.committed, true);
    assert.equal(fs.propositions.length, 0);
    const restored = saves.deserializeArr(initFormalSystem(false).fs, JSON.parse(result.save).data).fs;
    assert.deepEqual(restored.propositions[0].value, parser.parse(target));
    restored.expandMacroWithProp(0);
    assert.deepEqual(restored.propositions.at(-1).value, parser.parse(target));
}

console.log("GitHub issue #44 separation tight roundtrip and witness regression passed");
