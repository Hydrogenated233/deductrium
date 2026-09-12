import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";
import { SavesParser } from "../js/tt/savesparser.js";

const parser = new ASTParser();
for (const source of [
    "W x:False,False",
    "W x:A,B x",
    "W x:A,W y:B x,C x y",
    "ΠA:U,ΠB:(A→U),W x:A,B x",
    "λW:U.W",
    "W Wfoo:U,Wfoo",
    "W W:U,W"
]) {
    const ast = parser.parseSurface(source);
    const printed = parser.stringify(ast);
    assert.deepEqual(parser.parseSurface(printed), ast, source);
}
for (const name of ["Wx", "Wfoo", "WTree"]) {
    const ast = parser.parseSurface(name);
    assert.equal(ast.type, "var");
    assert.equal(ast.name, name);
    assert.equal(parser.parseSurface(`${name}:U`).nodes[0].name, name);
}
assert.throws(() => parser.parseSurface("(Wx:False,False)"));

const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_", timeout: 30_000, language: "zh"
};
const options = {
    disableMultipleApply: false, disableDestructConds: false, disableDestructEq: false
};
const target = "Πa:U,not(W x:False,a)";
const commands = ["expand not", "intros a w", "cases w", "exact w"];
const engine = new TTAssistEngine();
engine.configure(config);
const completed = engine.start(target, options, commands);
assert.equal(completed.goals.length, 0);
const result = engine.qed();
assert.equal(result.theorem, parser.stringify(parser.parseSurface(target)));
assert.deepEqual(engine.qed(), result);
assert.deepEqual(engine.snapshot(), completed);

// These are the bare/named rows stored by the GUI after qed. Exercise the
// real save adapter and independently validate both restored rows.
const items = ["", "ttWFalseElim"].map(name => ({
    kind: "theorem",
    value: `${name ? `${name}:=` : ""}${result.proof}:${result.theorem}`,
    local: false
}));
const saves = new SavesParser();
const serialized = saves.serialize({
    serializeTheoremItems: () => items,
    serializeProofSessions: () => undefined
});
let restored;
let resets = 0;
saves.deserialize({
    resetProofAssistantForSaveLoad: () => resets++,
    restoreTheoremItems: value => { restored = value; },
    queueProofSessionsRestore: () => {}
}, serialized);
assert.equal(resets, 1);
assert.deepEqual(restored, items);
const independent = new TTCoreEngine();
independent.configure(config);
for (const item of restored) {
    const ast = parser.parseSurface(item.value);
    const checked = ast.type === ":="
        ? independent.registerDefinition(ast)
        : independent.checkAst(ast);
    assert.equal(checked.ok, true, checked.error);
    assert.equal(checked.inferenceComplete, true);
}

console.log("GitHub issue #53 W binder roundtrip, qed and save/reload regression passed");
