import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";
import { migrateLegacyTTSave } from "../js/tt/savesparser.js";

const parser = new ASTParser();
const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 60_000,
    language: "zh"
};
const target = "Πa:U,Πb:U,Πc:U,Πd:U,a≃b→c≃d→(a×c)≃(b×d)";
const assistant = new TTAssistEngine();
assistant.configure(config);
assistant.start(target, {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
});
for (const command of [
    "intros a b c d hab hcd",
    "rw [ua hab, ua hcd]",
    "apply id2eqv",
    "rfl"
]) {
    assistant.apply(command);
}
assert.equal(assistant.snapshot().goals.length, 0);
const { proof, theorem } = assistant.qed();
assert.match(proof, /U_/u, "the rewrite motives exercise inferred universe levels");
assert.equal(theorem, parser.stringify(parser.parseSurface(target)));
const assertion = `${proof}:${theorem}`;

// The editor and restored theorem rows go through the strict parser, unlike
// the assistant's internal AST check. Qed must remain valid across that boundary.
const session = new TTCoreSession();
session.configure(config);
const result = session.validate(0, parser.parseSurface(assertion));
assert.equal(result.ok, true, result.error);
assert.equal(result.inferenceComplete, true, "expected theorem resolves the universe holes");
const definition = session.validate(1, parser.parseSurface(`productEquivalence := ${assertion}`));
assert.equal(definition.ok, true, definition.error);
assert.equal(definition.inferenceComplete, true);

const saved = migrateLegacyTTSave(JSON.parse(JSON.stringify({
    version: 3,
    items: [{ kind: "theorem", value: assertion }]
})));
assert.equal(saved.items[0].value, assertion, "existing Unicode saves need no text rewrite");
const restored = new TTCoreSession();
restored.configure(config);
const revalidated = restored.validate(0, parser.parseSurface(saved.items[0].value));
assert.equal(revalidated.ok, true, revalidated.error);

// Recognize only the exact level-hole shorthand, not every U-prefixed name.
for (const source of ["U_", "(U_)", "λx:U_.x", "Πx:U_,U_"]) {
    assert.deepEqual(parser.parseSurface(source), parser.parse(source), source);
    const roundtrip = parser.stringify(parser.parseSurface(source));
    assert.deepEqual(parser.parseSurface(roundtrip), parser.parse(source), roundtrip);
}
for (const name of ["U_foo", "U__foo", "Ufoo", "Ufoo_bar"]) {
    assert.deepEqual(parser.parseSurface(name), { type: "var", name });
    assert.equal(parser.parseSurface(`${name} : U`).nodes[0].name, name);
}

console.log("GitHub issue #45 qed universe-hole strict parsing and save roundtrip regression passed");
