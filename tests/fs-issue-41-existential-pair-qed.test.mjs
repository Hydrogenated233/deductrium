import assert from "node:assert/strict";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { ASTParser } from "../js/fs/astparser.js";
import { initFormalSystem } from "../js/fs/initial.js";
import { SavesParser } from "../js/fs/savesparser.js";
import { expandInferenceSnapshot } from "../js/fs/inference-worker-core.js";

const parser = new ASTParser();
const target = "(Vp:Vq:Vr:Vs:((p,q)=(r,s)>(p=r&q=s)))>(((En:x=(m,n))&(En:x=(k,n)))>m=k)";
const commands = [
    "intro hall",
    "intro hboth",
    "obtain <hm,hk> := hboth",
    "obtain <r,hr> := hm",
    "obtain <s,hs> := hk",
    "have heq : (m,r)=(k,s)",
    "rw <-hr",
    "rw <-hs",
    "rfl",
    "have hi := hall m r k s",
    "have hb := hi heq",
    "obtain <he,hn> := hb",
    "exact he"
];

for (const [goal, script] of [
    [target, commands],
    [target.replace("Vp:Vq:Vr:Vs:((p,q)=(r,s)>(p=r&q=s))",
        "Vu:Vv:Vw:Vt:((u,v)=(w,t)>(u=w&v=t))"), commands],
    [target.replace("En:x=(k,n)", "Et:x=(k,t)"), commands],
    [`Vm:Vk:(${target})`, ["intros m k", ...commands]]
]) {
    for (const name of [undefined, "issue41ExistentialPair"]) {
        const fs = initFormalSystem(true).fs;
        const assistant = new InferenceProofAssistant(fs, goal, { allowMcpt: false });
        for (const command of script) assistant.apply(command);
        assert.equal(assistant.snapshot().complete, true);
        const restored = new InferenceProofAssistant(fs, goal, { allowMcpt: false });
        restored.restore(JSON.parse(JSON.stringify(assistant.snapshot())));
        assert.equal(restored.qed(name).committed, true);
        if (name) {
            assert.deepEqual(fs.deductions[name].conditions, []);
            fs.deduct({
                deductionIdx: name, conditionIdxs: [],
                replaceValues: fs.deductions[name].replaceNames.map(value => parser.parse(value))
            });
        }
        if (!name && goal === target) {
            const save = new SavesParser(false).serialize({
                formalSystem: fs, deductions: Object.keys(fs.deductions), metarules: [],
                getProps: () => fs.propositions, pageStore: fs.inferencePages
            });
            const expanded = expandInferenceSnapshot({
                save, creative: true, fastMetaRules: "cvuqe><:#zZQR", metarules: [],
                target: { kind: "proposition", index: 0 }
            });
            assert.ok(JSON.parse(expanded.save).data[7].pages[0].propositions.length > 1);
            assert.equal(fs.propositions.length, 1);
        }
        fs.expandMacroWithProp(0);
        assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), parser.stringifyTight(parser.parse(goal)));
        assert.ok(fs.propositions.every(row => row.from));
    }
}

// A hidden rename rule must not become a new requirement for simple intros.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "Vx:x=x", {
        allowMcpt: false,
        ruleNames: Object.keys(fs.deductions).filter(name => name !== ".Vcn")
    });
    assistant.apply("intro y");
    assistant.apply("rfl");
    assistant.qed();
    fs.expandMacroWithProp(0);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value),
        parser.stringifyTight(parser.parse("Vx:x=x")));
    assert.ok(fs.propositions.every(row => row.from?.deductionIdx !== ".Vcn"));
}

// Reusing a completed graph must still reject generalization over a premise.
for (const name of [undefined, "issue41InvalidGeneralization"]) {
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs,
        "(Vx:F(x)@y)>(Vy:(Vx:F(x)@y))", { allowMcpt: false });
    for (const command of ["intro h", "intro y", "exact h"]) assistant.apply(command);
    const before = assistant.snapshot();
    const rows = structuredClone(fs.propositions);
    const rules = Object.keys(fs.deductions);
    assert.throws(() => assistant.qed(name), /全称变量出现在未解除的外部前提中/);
    assert.deepEqual(assistant.snapshot(), before);
    assert.deepEqual(fs.propositions, rows);
    assert.deepEqual(Object.keys(fs.deductions), rules);
}

// Schematic non-freeness is attached to the original binder, not its UI alias.
{
    const fs = initFormalSystem(true).fs;
    const goal = "#nf($0,x)>(Vx:#nf($0,x))";
    const assistant = new InferenceProofAssistant(fs, goal, { allowMcpt: false });
    for (const command of ["intro h", "intro y", "exact h"]) assistant.apply(command);
    assistant.qed();
    fs.expandMacroWithProp(0);
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value),
        parser.stringifyTight(parser.parse(goal)));
}

console.log("GitHub issue #41 existential pair qed regression passed");
