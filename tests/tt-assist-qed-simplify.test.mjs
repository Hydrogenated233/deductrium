import assert from "node:assert/strict";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { ASTParser } from "../js/tt/astparser.js";
import { initTypeSystem } from "../js/tt/initial.js";

const config = { unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_", timeout: 30_000, language: "zh" };
const options = { disableMultipleApply: false, disableDestructConds: false, disableDestructEq: false };
const engine = new TTAssistEngine();
engine.configure(config);
engine.start("True→True", options);
engine.apply("intro h");
engine.apply("have redundant : True := h");
const done = engine.apply("exact h");
const result = engine.qed();
assert.equal(result.proof, "(λh:True.h)");
assert.equal(result.theorem, "(True→True)");
assert.deepEqual(engine.qed(), result);
assert.equal(engine.undo().goals.length, 1, "qed simplification must not change undo history");
assert.deepEqual(engine.start(done.theorem, options, done.history).history, done.history);
const parser = new ASTParser();
const fresh = new TTCoreSession();
fresh.configure(config);
assert.equal(fresh.validate(0, parser.parseSurface(`${result.proof} : ${result.theorem}`)).ok, true);

engine.start("True→True→True", options);
engine.apply("intro h");
engine.apply("have tmp : True := h");
engine.apply("exact (λh:True.tmp)");
const captureFree = engine.qed();
assert.doesNotMatch(captureFree.proof, /tmp/);
const reloaded = new TTCoreSession();
reloaded.configure(config);
const validated = reloaded.validate(0, parser.parseSurface(`${captureFree.proof} : ${captureFree.theorem}`));
assert.equal(validated.ok, true, validated.error);
const simplified = parser.parseSurface(captureFree.proof);
assert.equal(simplified.nodes[1].nodes[1].name, simplified.name,
    "inlining must preserve the outer free variable beneath a shadowing lambda");
assert.notEqual(simplified.nodes[1].name, simplified.name);
console.log("checked qed proof simplification regression passed");
