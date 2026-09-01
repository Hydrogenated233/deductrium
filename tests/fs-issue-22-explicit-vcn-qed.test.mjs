import assert from "node:assert/strict";
import { InferenceProofAssistant } from "../js/fs/proof-assistant.js";
import { initFormalSystem } from "../js/fs/initial.js";

const fs = initFormalSystem(true).fs;
const target = "(V$4:E$3:V$2:E$0:V$x:#nf($1,$z))>(V$4:E$3:V$2:E$0:V$z:#rp(#nf($1,$z),$x,$z))";
const assistant = new InferenceProofAssistant(fs, target);

for (const command of [
    "intros h a",
    "have ha := h a",
    "obtain <b,hb> := ha",
    "use b",
    "intro c",
    "have hc := hb c",
    "obtain <d,hd> := hc",
    "use d",
    "have hv := .Vcn $x=$x $1=$1 $z=$z",
    "exact hd",
    "exact hv"
]) assistant.apply(command);

const result = assistant.qed("issue22ExplicitVcn");
assert.equal(result.committed, true);
assert.equal(result.propositions[0].from?.assistant?.theorem.type, "sym");
assert.doesNotThrow(() => fs.materializeDeferredDeduction("issue22ExplicitVcn"));

console.log("GitHub issue #22 explicit .Vcn qed regression passed");
