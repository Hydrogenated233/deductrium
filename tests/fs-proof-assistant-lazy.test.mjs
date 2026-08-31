import assert from "node:assert/strict";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { ASTParser } from "../js/fs/astparser.js";
import { SavesParser } from "../js/fs/savesparser.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();
const saves = new SavesParser(true);

// Bare qed is one page row and keeps the replay recipe, not the expanded graph.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assistant.apply("intro h");
    assistant.apply("exact h");
    const result = assistant.qed();
    assert.equal(fs.propositions.length, 1);
    assert.equal(result.steps.length, 1);
    const row = fs.propositions[0];
    const deduction = fs.deductions[row.from.deductionIdx];
    assert.equal(row.deferredKind, "assistant");
    assert.equal(deduction.deferredKind, "assistant");
    assert.equal(deduction.steps, undefined);
    assert.deepEqual(deduction.deferredPayload.history, ["intro h", "exact h"]);

    const serialized = saves.serializeDeduction(deduction);
    assert.equal(serialized[2], undefined);
    assert.equal(serialized[4], "assistant");
    assert.deepEqual(serialized[5].history, ["intro h", "exact h"]);
    assert.equal(serialized[5].premises.length, 0);

    const propositionTuple = saves.serializeProposition(row);
    assert.equal(propositionTuple[2], "assistant");
    const restoredRow = saves.deserializeProposition(propositionTuple);
    assert.equal(restoredRow.deferredKind, "assistant");

    fs.expandMacroWithProp(0);
    assert.ok(fs.deductions[row.from.deductionIdx].steps?.length);
    const serializedAfterExpansion = saves.serializeDeduction(fs.deductions[row.from.deductionIdx]);
    assert.equal(serializedAfterExpansion[2], undefined,
        "materializing a lazy assistant rule must not make saved steps eager");
    assert.deepEqual(serializedAfterExpansion[5].history, ["intro h", "exact h"]);
}

// pN references are snapshotted and replayed against a private page, so a
// loaded assistant proof does not depend on the current page object identity.
{
    const source = initFormalSystem(true).fs;
    source.addHypothese(parser.parse("A>B"));
    source.addHypothese(parser.parse("A"));
    const assistant = new InferenceProofAssistant(source, "B");
    assistant.apply("apply p0");
    assistant.apply("exact p1");
    const result = assistant.qed();
    const tuple = JSON.parse(JSON.stringify(saves.serializeDeduction(source.deductions[result.deductionName])));

    const restored = initFormalSystem(true).fs;
    restored.addHypothese(parser.parse("A>B"));
    restored.addHypothese(parser.parse("A"));
    saves.deserializeDeduction(result.deductionName, restored, tuple);
    restored.propositions.push({
        value: parser.parse("B"),
        from: { deductionIdx: result.deductionName, conditionIdxs: [0, 1], replaceValues: [] }
    });
    restored.expandMacroWithProp(2);
    assert.equal(parser.stringifyTight(restored.propositions.at(-1).value), "B");
    assert.ok(restored.deductions[result.deductionName].steps?.length);
}

// Named qed keeps the legacy page-clearing behavior while storing a deferred
// rule that can be expanded later as a regular macro.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assistant.apply("intro h");
    assistant.apply("exact h");
    assistant.qed("namedAssistantProof");
    assert.equal(fs.propositions.length, 0);
    assert.equal(fs.deductions.namedAssistantProof.deferredKind, "assistant");
    assert.equal(fs.deductions.namedAssistantProof.steps, undefined);
    fs.expandMacroWithDefaultValue("namedAssistantProof");
    assert.ok(fs.deductions.namedAssistantProof.steps?.length);
}

// A bad recipe must fail before mutating the live proposition page.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assistant.apply("intro h");
    assistant.apply("exact h");
    const result = assistant.qed();
    const name = result.deductionName;
    fs.deductions[name].deferredPayload.history = ["intro h", "unknown-command"];
    const before = fs.propositions.slice();
    assert.throws(() => fs.expandMacroWithProp(0));
    assert.deepEqual(fs.propositions, before);
}

// A failed pN remap must not poison the recursion guard: fixing the payload
// and retrying should report the real replay result, not a false cycle.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assistant.apply("intro h");
    assistant.apply("exact h");
    const result = assistant.qed();
    const deduction = fs.deductions[result.deductionName];
    deduction.deferredPayload.history = ["exact p9"];
    assert.throws(() => fs.expandMacroWithProp(0), /前提定理 p9/);
    deduction.deferredPayload.history = ["intro h", "exact h"];
    fs.expandMacroWithProp(0);
    assert.ok(deduction.steps?.length);
}

// An existing page proposition can be used directly as an exact source; the
// materializer no longer inserts a redundant `.i` followed by `mp` alias.
{
    const fs = initFormalSystem(false).fs;
    fs.fastmetarules = "cvuqe><:#zZQR";
    fs.addDeduction("r", parser.parse("A⊢B"), "test");
    fs.addHypothese(parser.parse("A"));
    const assistant = new InferenceProofAssistant(fs, "C>(A>B)", {
        ruleNames: ["r"],
        fastMetaRules: fs.fastmetarules,
        allowMcpt: false
    });
    assistant.apply("intro c");
    assistant.apply("intro h");
    assistant.apply("apply r");
    assistant.apply("exact p0");
    assistant.qed();
    fs.expandMacroWithProp(1);
    assert.equal(fs.propositions.some(proposition => proposition.from?.deductionIdx === ".i"), false);
}

// Nested deferred assistant rules can be used as operands of generated
// deduction-theorem prefixes after their materializer refreshes the rule map.
{
    const fs = initFormalSystem(false).fs;
    fs.fastmetarules = "c>";
    fs.addDeduction("r", parser.parse("A⊢B"), "test");
    fs.addDeduction("t", parser.parse("B,~A⊢C"), "test");
    fs.addHypothese(parser.parse("A"));
    fs.addHypothese(parser.parse("~A"));

    const inner = new InferenceProofAssistant(fs, "B", {
        fastMetaRules: "c>",
        allowMcpt: false
    });
    inner.apply("apply r");
    inner.apply("exact p0");
    inner.qed("inner");

    fs.addHypothese(parser.parse("A"));
    fs.addHypothese(parser.parse("~A"));
    const outer = new InferenceProofAssistant(fs, "C", {
        fastMetaRules: "c>",
        allowMcpt: false
    });
    outer.apply("apply t");
    outer.apply("apply inner");
    outer.apply("exact p0");
    // `inner` was recorded with both page hypotheses in scope; the second p1
    // discharges `t`'s own `~A` premise after the rule's retained `~A` premise.
    outer.apply("exact p1");
    outer.apply("exact p1");
    outer.qed("outer");
    assert.ok(fs.generateDeduction(">>outer"));
}

// A named assistant theorem may later be used by `dt`.  Its lazy materialized
// graph contains the shared `__assistant` step, which must not be resolved as a
// persisted global rule name.
{
    const fs = initFormalSystem(true).fs;
    fs.fastmetarules = "cvuqe><:#zZQR";
    fs.addHypothese(parser.parse("A"));
    const assistant = new InferenceProofAssistant(fs, "A&A", {
        fastMetaRules: fs.fastmetarules
    });
    assistant.apply("tauto");
    assistant.qed("sVe");
    assert.doesNotThrow(() => fs.metaDeductTheorem("sVe", "test"));
    assert.equal(parser.stringifyTight(fs.deductions[">sVe"].conclusion), "A>(A&A)");
}

// The same case must survive a save/load round trip: `__assistant` is not
// serialized as a standalone deduction, but the step payload is preserved.
{
    const source = initFormalSystem(true).fs;
    source.fastmetarules = "cvuqe><:#zZQR";
    source.addHypothese(parser.parse("A"));
    const assistant = new InferenceProofAssistant(source, "A&A", {
        fastMetaRules: source.fastmetarules
    });
    assistant.apply("tauto");
    assistant.qed("sVe");
    const tuple = JSON.parse(JSON.stringify(saves.serializeDeduction(source.deductions.sVe)));

    const restored = initFormalSystem(true).fs;
    restored.fastmetarules = "cvuqe><:#zZQR";
    saves.deserializeDeduction("sVe", restored, tuple);
    assert.doesNotThrow(() => restored.metaDeductTheorem("sVe", "test"));
    assert.equal(parser.stringifyTight(restored.deductions[">sVe"].conclusion), "A>(A&A)");
}

// A universal assistant proof using an equivalence premise must expand after
// save-style replay.  The inner a4 applications carry #rp assertions that
// become rigid once the introduced $2 binder is known.
{
    const fs = initFormalSystem(true).fs;
    fs.fastmetarules = "c>:<qvu";
    fs.addHypothese(parser.parse("(V$2:($0<>$1))"));
    const assistant = new InferenceProofAssistant(fs, "(V$2:$0)<>(V$2:$1)", {
        fastMetaRules: fs.fastmetarules,
        ruleNames: Object.keys(fs.deductions),
        allowMcpt: true
    });
    for (const command of [
        "constructor",
        "intro",
        "have h:=p0 x",
        "obtain <h2,h3> := h",
        "intro $2",
        "apply h2",
        "have h4:=h1 x",
        "assumption",
        "intro",
        "have h:=p0 x",
        "obtain <h2,h3> := h",
        "intro $2",
        "apply h3",
        "have h4:=h1 x",
        "assumption"
    ]) assistant.apply(command);
    assistant.qed();
    assert.doesNotThrow(() => fs.expandMacroWithProp(1));
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "(V$2:$0)<>(V$2:$1)");
}

// The same protection applies when a normal recorded macro contains an
// assistant step, rather than being deferred itself.
{
    const fs = initFormalSystem(true).fs;
    fs.fastmetarules = "cvuqe><:#zZQR";
    fs.addHypothese(parser.parse("A"));
    const assistant = new InferenceProofAssistant(fs, "A&A", {
        fastMetaRules: fs.fastmetarules
    });
    assistant.apply("tauto");
    assistant.qed();
    fs.addMacro("sVe", "test");
    assert.doesNotThrow(() => fs.metaDeductTheorem("sVe", "test"));
    assert.equal(parser.stringifyTight(fs.deductions[">sVe"].conclusion), "A>(A&A)");
}

// A saved macro may contain a nested assistant step and then be lifted through
// two universal prefixes.  This mirrors the sVe/sVs shape from the reported
// save and must not resolve `__assistant` as a global rule name.
{
    const fs = initFormalSystem(false).fs;
    fs.fastmetarules = "cvuqe><:#zZQR";
    const pageId = fs.inferencePages.activeId;
    const nestedAssistant = {
        kind: "assistant",
        version: 1,
        pageId,
        theorem: "$1",
        history: ["have h := p0 $0", "assumption"],
        fastMetaRules: "c>:<qv",
        allowMcpt: true,
        premises: [{ pageId, index: 0, value: "(V$0:$1)" }]
    };
    const saves = new SavesParser(false);
    saves.deserializeDeduction("sVe", fs, [
        "(V$0:$1)⊢$1",
        "录制*",
        [["__assistant", [0], [], nestedAssistant]]
    ]);
    saves.deserializeDeduction("sVs", fs, [
        "(V$0:(V$1:$2))⊢(V$1:(V$0:$2))",
        "录制*",
        [["<a6", [0], ["$1"]], ["vvsVe", [-1], []]]
    ]);
    assert.doesNotThrow(() => fs.expandMacroWithDefaultValue("sVe", null));
    fs.propositions = [];
    assert.doesNotThrow(() => fs.expandMacroWithDefaultValue("sVs", null));
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value), "(V$1:(V$0:$2))");
}

// Existential/disjunction exchange from a saved proof can select an equivalent
// user `sEe` rule instead of the bundled `.Ee`.  Assertion wrappers are allowed
// to disappear during this replay, so proposition equality must be symmetric.
{
    const fs = initFormalSystem(false).fs;
    fs.fastmetarules = "c>:<qvu";
    const pageId = fs.inferencePages.activeId;
    const saves = new SavesParser(false);
    saves.deserializeDeduction("l", fs, [
        "$0<>$1⊢$1>$0",
        "录制*",
        [["<.<>2", [0], []]]
    ]);
    saves.deserializeDeduction("r", fs, [
        "$0<>$1⊢$0>$1",
        "录制*",
        [["<.<>1", [0], []]]
    ]);
    saves.deserializeDeduction("sEmp", fs, [
        "(V$x:($1>$2)),(E$x:$1)⊢(E$x:$2)",
        "录制*",
        [
            ["dE", [], ["$x", "$1"]],
            ["<r", [-1, 1], []],
            ["v<.a30", [0], []],
            ["<a5", [-1], []],
            ["<.a30", [-1], []],
            ["mp", [-1, -4], []],
            ["dE", [], ["$x", "$2"]],
            ["<l", [-1, -2], []]
        ]
    ]);
    saves.deserializeDeduction("sErp", fs, [
        "⊢#rp($1,$0,$2)>(E$0:$1)",
        "录制*",
        [
            [":dE,l", [], ["$0", "$1"]],
            [":a4,<.a30", [], ["~$1", "$0", "$2"]],
            [".ni", [], ["#rp($1,$0,$2)"],],
            [".t", [-1, -2], []],
            [".t", [-1, -4], []]
        ]
    ]);
    const ruleNames = Object.keys(fs.deductions)
        .filter(name => ![".Ee", ".Emp", ".Erp"].includes(name));
    saves.deserializeDeduction("sEe", fs, [
        "(E$0:#nf($1,$0))⊢#nf($1,$0)",
        "证明助手录制*",
        undefined,
        undefined,
        "assistant",
        {
            kind: "assistant",
            version: 1,
            pageId,
            theorem: "#nf($1,$0)",
            history: [
                "have h : ~V$0:~#nf($1,$0)",
                "apply :dE,r",
                "exact p0",
                "have h1 : (~(V$0: ~#nf($1, $0))>#nf($1, $0))",
                "apply <.a31",
                "exact a6",
                "apply h1",
                "assumption"
            ],
            fastMetaRules: "c>:<qvu",
            allowMcpt: true,
            ruleNames,
            premises: [{ pageId, index: 0, value: "(E$0:#nf($1,$0))" }]
        }
    ]);
    ruleNames.push("sEe");
    const sEorPayload = {
        kind: "assistant",
        version: 1,
        pageId,
        theorem: "(E$0:($1|$2))<>((E$0:$1)|(E$0:$2))",
        history: [
            "constructor",
            "intro",
            "obtain <x,hx> := h1",
            "obtain h1 | h2 := hx",
            "left",
            "use x",
            "assumption",
            "right",
            "use x",
            "assumption",
            "intro",
            "obtain h2 | h3 := h1",
            "obtain <x,hx> := h2",
            "use x",
            "left",
            "assumption",
            "obtain <x,hx> := h3",
            "use x",
            "right",
            "assumption"
        ],
        ruleNames,
        fastMetaRules: "c>:<qvu",
        allowMcpt: true,
        premises: []
    };
    saves.deserializeDeduction("sE|", fs, [
        "⊢(E$0:($1|$2))<>((E$0:$1)|(E$0:$2))",
        "证明助手录制*",
        undefined,
        undefined,
        "assistant",
        sEorPayload
    ]);
    assert.doesNotThrow(() => fs.expandMacroWithDefaultValue("sE|", null));
    assert.equal(parser.stringifyTight(fs.propositions.at(-1).value),
        "(E$0:($1|$2))<>((E$0:$1)|(E$0:$2))");
}

console.log("inference proof-assistant lazy atomic regression passed");
