import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { initFormalSystem } from "../js/fs/initial.js";
import { ASTParser } from "../js/fs/astparser.js";

const parser = new ASTParser();
const schema = "#rp(#nf($0,x),$1,y)";
const spelling = value => parser.stringifyTight(typeof value === "string" ? parser.parse(value) : value);
for (const [target, lastFact] of [
    [`(A&${schema})>${schema}`, "hb"],
    [`(${schema}&A)>${schema}`, "ha"],
    [`(A<>${schema})>(A>${schema})`, "ha"],
    [`(A<>${schema})>(${schema}>A)`, "hb"]
]) {
    for (const name of [undefined, "issue37Projection"]) {
        const fs = initFormalSystem(true).fs;
        const assistant = new InferenceProofAssistant(fs, target, { allowMcpt: false });
        for (const command of ["intro h", "obtain <ha,hb> := h", `exact ${lastFact}`]) {
            assistant.apply(command);
        }
        assert.equal(assistant.snapshot().complete, true);
        const restored = new InferenceProofAssistant(fs, target, { allowMcpt: false });
        restored.restore(JSON.parse(JSON.stringify(assistant.snapshot())));
        restored.qed(name);
        if (name) {
            assert.deepEqual(fs.deductions[name].conditions, []);
            fs.deduct({ deductionIdx: name, conditionIdxs: [],
                replaceValues: fs.deductions[name].replaceNames.map(value => parser.parse(value)) });
        }
        fs.expandMacroWithProp(0);
        assert.equal(spelling(fs.propositions.at(-1).value), spelling(target));
    }
}

// A compound universal argument must not replace the variable restriction x
// inside #nf($0,x). Compare specialization with the real a4 deduction.
{
    const fs = initFormalSystem(true).fs;
    const source = "Vx:((x@s)<>((x@omega)&#rp(#nf($0,x),$1,x)))";
    const target = `(${source})>(Vy:((y@s)>(y@s)))`;
    const assistant = new InferenceProofAssistant(fs, target);
    assistant.apply("intro hs");
    assistant.apply("have hss := hs (yU{y})");
    const hss = assistant.snapshot().goals[0].hypotheses.find(h => h.name === "hss");
    assert.ok(spelling(hss.formalProposition).includes("#nf($0,x)"));
    assert.equal(spelling(hss.formalProposition).includes("#nf($0,yU{y})"), false);
    const axiom = fs.deduct({
        deductionIdx: "a4", conditionIdxs: [],
        replaceValues: [parser.parse("x"), parser.parse(source).nodes[1], parser.parse("yU{y}")]
    });
    assert.equal(spelling(hss.formalProposition), spelling(fs.propositions[axiom].value.nodes[1]));
    const instance = spelling(fs.propositions[axiom].value.nodes[1]);
    fs.propositions = [];
    const specializedTarget = `(${source})>(${instance})`;
    const proof = new InferenceProofAssistant(fs, specializedTarget, { allowMcpt: false });
    for (const command of ["intro hs", "have hss := hs (yU{y})", "exact hss"]) proof.apply(command);
    proof.qed();
    fs.expandMacroWithProp(0);
    assert.equal(spelling(fs.propositions.at(-1).value), spelling(specializedTarget));
}

// #nf($0,x) guarantees only x, never an arbitrary y. The complete report must
// retain this game constraint rather than silently trusting a completed tree.
const blocks = [...readFileSync(new URL("./fixtures/fs-issue-37-peano-set-induction.md", import.meta.url), "utf8")
    .matchAll(/```text\s*([\s\S]*?)```/g)].map(match => match[1].trim());
const [reportedTarget, reportedScript] = blocks;
for (const withPageTheorem of [false, true]) {
    const fs = initFormalSystem(true).fs;
    delete fs.deductions[".pn5"];
    delete fs.deductions.apn5;
    if (withPageTheorem) {
        fs.addDeduction("successorInjection",
            parser.parse("⊢Vx:Vy:((xU{x})=(yU{y})>x=y)"), "reported page fixture");
        fs.deduct({ deductionIdx: "successorInjection", conditionIdxs: [], replaceValues: [] });
    }
    const assistant = new InferenceProofAssistant(fs, reportedTarget);
    for (const command of reportedScript.split(/\r?\n/).slice(0, -1)) assistant.apply(command);
    assert.equal(assistant.snapshot().complete, true);
    const before = assistant.snapshot();
    const rows = structuredClone(fs.propositions);
    const names = Object.keys(fs.deductions);
    for (const name of [undefined, "issue37InvalidGeneralization"]) {
        assert.throws(() => assistant.qed(name),
            /无法确认全称变量在未解除的外部前提中不自由出现：y/);
        assert.deepEqual(assistant.snapshot(), before);
        assert.deepEqual(fs.propositions, rows);
        assert.deepEqual(Object.keys(fs.deductions), names);
    }
}

// No alpha-equivalence was added to exact; the explicit game rule is required.
{
    const fs = initFormalSystem(true).fs;
    fs.addHypothese(parser.parse("Vz:(z=z)"));
    const assistant = new InferenceProofAssistant(fs, "Vy:(y=y)");
    assert.throws(() => assistant.apply("exact p0"), /不匹配/);
}

console.log("GitHub issue #37 schematic obtain regression passed");
