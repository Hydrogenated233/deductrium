import assert from "node:assert/strict";
import fs from "node:fs";
import { ASTParser } from "../js/fs/astparser.js";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { SavesParser } from "../js/fs/savesparser.js";
import { expandInferenceSnapshot } from "../js/fs/inference-worker-core.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();

function saveFor(fs) {
    const saves = new SavesParser(false);
    return saves.serialize({
        formalSystem: fs,
        deductions: Object.keys(fs.deductions),
        metarules: [],
        getProps: () => fs.propositions,
        pageStore: fs.inferencePages
    });
}

// Expansion is performed against a detached snapshot and returns all generated
// rules needed to apply the result without touching the live FormalSystem.
{
    const live = initFormalSystem(false).fs;
    live.fastmetarules = "c<";
    const assistant = new InferenceProofAssistant(live, "A>A", {
        allowMcpt: false,
        fastMetaRules: "c<"
    });
    assistant.apply("intro h");
    assistant.apply("exact h");
    assistant.qed();
    const before = live.propositions.length;
    const result = expandInferenceSnapshot({
        save: saveFor(live),
        creative: false,
        fastMetaRules: "c<",
        metarules: [],
        target: { kind: "proposition", index: 0 }
    });
    assert.equal(live.propositions.length, before);
    const data = JSON.parse(result.save).data;
    assert.equal(data[7].pages[0].propositions.length, 1);
    assert.ok(data[7].pages[0].propositions[0][1]);
    assert.ok(Object.keys(result.deductions).length > 0);
}

// Inline expansion uses the same isolated protocol and preserves the target
// proposition list in the returned snapshot.
{
    const live = initFormalSystem(false).fs;
    live.propositions.push({
        value: parser.parse("A>A"),
        from: {
            deductionIdx: ".i",
            conditionIdxs: [],
            replaceValues: [parser.parse("A")]
        }
    });
    const result = expandInferenceSnapshot({
        save: saveFor(live),
        creative: false,
        fastMetaRules: "",
        metarules: [],
        target: { kind: "inline-proposition", index: 0 }
    });
    assert.ok(JSON.parse(result.save).data[7].pages[0].propositions.length > 1);
}

const gui = fs.readFileSync(new URL("../src/fs/gui.ts", import.meta.url), "utf8");
const cmd = fs.readFileSync(new URL("../src/fs/cmd.ts", import.meta.url), "utf8");
assert.match(gui, /new InferenceWorkerClient/);
assert.match(gui, /expandInferenceOffThread/);
assert.match(gui, /cancelInferenceExpansion/);
assert.match(cmd, /runExpansionInWorker/);
assert.match(cmd, /runInlineExpansionInWorker/);
assert.match(cmd, /expansionGeneration/);

console.log("inference-layer Worker expansion regression passed");
