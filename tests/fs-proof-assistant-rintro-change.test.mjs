import assert from "node:assert/strict";

import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { initFormalSystem } from "../js/fs/initial.js";

// `rintro` introduces and immediately destructures a conjunction.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "(A&B)>A");
    assistant.apply("rintro ⟨ha,hb⟩");
    assert.ok(assistant.currentGoal.hypotheses.some(hypothesis => hypothesis.name === "ha"));
    assistant.apply("exact ha");
    assert.equal(assistant.snapshot().complete, true);
}

// `change`/`show` preserve the proof state on failed assertion-equivalence checks.
{
    const fs = initFormalSystem(true).fs;
    const assistant = new InferenceProofAssistant(fs, "A>A");
    assistant.apply("intro h");
    assistant.apply("change A");
    assert.throws(() => assistant.apply("show B"), /不匹配|相同|命题/);
    assert.equal(assistant.currentGoal.target.name, "A");
    assistant.apply("show A");
    assistant.apply("exact h");
    assert.equal(assistant.snapshot().complete, true);
}

console.log("inference proof-assistant rintro/change regression passed");
