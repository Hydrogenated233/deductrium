import assert from "node:assert/strict";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { initFormalSystem } from "../js/fs/initial.js";

for (const name of [undefined, "issue38ExplicitVcn"]) {
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(
        fs,
        "(Vz:(z=z))>Vx:Vy:(y=y)",
        { allowMcpt: false }
    );
    for (const command of [
        "intro h",
        "intro x",
        "apply .Vcn $x=z $1=(z=z) $z=y",
        "exact h"
    ]) assistant.apply(command);
    assert.equal(assistant.snapshot().complete, true);
    const result = assistant.qed(name);
    assert.equal(result.committed, true);
    assert.equal(result.propositions[0].value.name, ">");
    if (name) {
        assert.deepEqual(fs.deductions[name].conditions, []);
    }
}

console.log("GitHub issue #38 explicit .Vcn universal qed regression passed");
