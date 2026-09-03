import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { ASTParser } from "../js/tt/astparser.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";
import {
    SandboxEnvironment,
    creativeSandboxSystemRuleIds,
    lowerSandboxHit,
    parseSandboxHit
} from "../js/tt/sandbox.js";
import { SandboxWorkerSession } from "../js/tt/sandbox-worker.js";

const parser = new ASTParser();
const source = readFileSync(
    new URL("./fixtures/hit3-composite.txt", import.meta.url),
    "utf8"
).trim();
const options = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};

const parsed = parseSandboxHit(source);
const path3 = parsed.pathLevels[2].constructors;
assert.deepEqual(path3.map(path => path.name), [
    "atomComposite3", "composeComposite3", "inverseComposite3"
], "atomic third-path syntax must remain compatible beside expression endpoints");
assert.match(parser.stringify(path3[1].left), /face01Composite3.*face12Composite3/);
assert.match(parser.stringify(path3[2].left), /inveq.*face01Composite3/);

const bundle = lowerSandboxHit(parsed);
assert.equal(bundle.metadata.kind, "hit3");
assert.ok(bundle.generatedNames.includes("ap3_composeComposite3"));
assert.ok(bundle.generatedNames.includes("apd3_inverseComposite3"));

const sandbox = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const added = sandbox.add(source);
assert.equal(added.ok, true, added.error);
for (const name of [
    "atomComposite3", "composeComposite3", "inverseComposite3",
    "ap3_composeComposite3", "apd3_composeComposite3",
    "ap3_inverseComposite3", "apd3_inverseComposite3"
]) {
    assert.equal(sandbox.check(name).ok, true, `${name} must have a formed type`);
}

assert.throws(
    () => parseSandboxHit(
        "hit BadComposite3 : U "
        + "| badBase3:BadComposite3 "
        + "| badLoop0:badBase3=badBase3 | badLoop1:badBase3=badBase3 "
        + "| badLoop2:badBase3=badBase3 "
        + "| path2 badFace01:badLoop0=badLoop1 "
        + "| path2 badFace20:badLoop2=badLoop0 "
        + "| path3 badCell:(badFace01▪badFace20)=badFace01"
    ),
    /三阶路径构造子.*(?:无法拼接|边界不一致)/,
    "non-composable second-path expressions must report a Chinese boundary error"
);

const parameterizedSource = "hit CompositeP (A : U) : U "
    + "| baseCompositeP : CompositeP A "
    + "| loop0CompositeP : Πz:A,baseCompositeP=baseCompositeP "
    + "| loop1CompositeP : Πz:A,baseCompositeP=baseCompositeP "
    + "| loop2CompositeP : Πz:A,baseCompositeP=baseCompositeP "
    + "| path2 face01CompositeP : Πz:A,loop0CompositeP z=loop1CompositeP z "
    + "| path2 face12CompositeP : Πz:A,loop1CompositeP z=loop2CompositeP z "
    + "| path2 face02CompositeP : Πz:A,loop0CompositeP z=loop2CompositeP z "
    + "| path2 face10CompositeP : Πz:A,loop1CompositeP z=loop0CompositeP z "
    + "| path3 composeCompositeP : Πz:A,(face01CompositeP z▪face12CompositeP z)=face02CompositeP z "
    + "| path3 inverseCompositeP : Πz:A,inveq (face01CompositeP z)=face10CompositeP z";
const parameterizedBundle = lowerSandboxHit(parseSandboxHit(parameterizedSource));
const parameterized = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
assert.equal(parameterized.add(parameterizedSource).ok, true);
for (const name of [
    "ap3_composeCompositeP", "apd3_composeCompositeP",
    "ap3_inverseCompositeP", "apd3_inverseCompositeP"
]) assert.equal(parameterized.check(name).ok, true, `${name} must form with uniform parameters`);

const compositeBoundarySource = "hit CompositeBoundary3 : U "
    + "| baseCB3 : CompositeBoundary3 "
    + "| pCB3 : baseCB3=baseCB3 "
    + "| qCB3 : baseCB3=baseCB3 "
    + "| path2 commCB3 : (pCB3▪qCB3)=(qCB3▪pCB3) "
    + "| path3 cellCB3 : commCB3=commCB3";
const compositeBoundaryParsed = parseSandboxHit(compositeBoundarySource);
const commBoundary = compositeBoundaryParsed.pathLevels[1].constructors[0];
assert.equal(commBoundary.leftExpression.kind, "compose");
assert.equal(commBoundary.rightExpression.kind, "compose");
const compositeBoundaryBundle = lowerSandboxHit(compositeBoundaryParsed);
assert.equal(compositeBoundaryBundle.metadata.version, 8);
const compositeBoundary = new SandboxEnvironment({
    systemRuleIds: creativeSandboxSystemRuleIds
});
const compositeBoundaryAdded = compositeBoundary.add(compositeBoundarySource);
assert.equal(compositeBoundaryAdded.ok, true, compositeBoundaryAdded.error);
for (const name of [
    "cellCB3",
    "ap3_cellCB3", "@ap3_cellCB3",
    "apd3_cellCB3", "@apd3_cellCB3"
]) {
    assert.equal(compositeBoundary.check(name).ok, true,
        `${name} must recursively compute the composite path2 boundary`);
}

const assist = new TTAssistEngine();
assist.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    trustedInductives: [bundle],
    inferDisplayMode: "_",
    timeout: 60_000,
    language: "zh"
});
let snapshot = assist.start(parser.stringify(bundle.eliminator[1]), options);
for (const command of [
    "intro C", "intro c0",
    "intro p0", "intro p1", "intro p2",
    "intro p2_0", "intro p2_1", "intro p2_2", "intro p2_3",
    "intro p3_0", "intro p3_1", "intro p3_2",
    "intro x", "induction x",
    "exact c0", "exact p0", "exact p1", "exact p2",
    "exact p2_0", "exact p2_1", "exact p2_2", "exact p2_3",
    "exact p3_0", "exact p3_1", "exact p3_2"
]) snapshot = assist.apply(command);
assert.equal(snapshot.goals.length, 0,
    "proof-assistant induction must expose and discharge composite path3 methods");
assert.match(assist.qed().proof, /ind_Composite3/);

const save = sandbox.toJSON();
for (const declaration of save.declarations) {
    assert.equal(Object.hasOwn(declaration, "hit"), false);
    assert.equal(Object.hasOwn(declaration, "generatedNames"), false);
}
const worker = new SandboxWorkerSession();
const restored = worker.handle({
    id: 1,
    kind: "load",
    save,
    options: { systemRuleIds: creativeSandboxSystemRuleIds }
});
assert.equal(restored.ok, true, restored.error);
assert.equal(restored.bridge.inductives[0].metadata.kind, "hit3");
assert.equal(worker.handle({
    id: 2,
    kind: "check",
    source: "apd3_composeComposite3",
    options: { systemRuleIds: creativeSandboxSystemRuleIds }
}).ok, true);

const register = candidate => {
    const engine = new TTCoreEngine();
    engine.configure({ unlockedTypes: creativeSandboxSystemRuleIds });
    return engine.core.registerSystemInductive(candidate);
};
assert.doesNotThrow(() => register(structuredClone(compositeBoundaryBundle)),
    "Core must certify path3 over a path2 with composite first-path boundaries");
const forged = structuredClone(bundle);
const expression = forged.metadata.pathLevels[2].constructors
    .find(path => path.name === "composeComposite3");
assert.ok(expression, "the fixture must expose expression metadata for the composite endpoint");
if (expression.leftExpression) {
    expression.leftExpression = { kind: "atom", name: "face02Composite3", arguments: [] };
}
else expression.left = parser.parse("face02Composite3");
assert.throws(
    () => register(forged),
    /三维 HIT.*(?:expression|表达式|metadata).*不一致/,
    "Core must reconstruct composite endpoint expressions instead of trusting forged metadata"
);

const forgedInverse = structuredClone(bundle);
const inverseExpression = forgedInverse.metadata.pathLevels[2].constructors
    .find(path => path.name === "inverseComposite3");
assert.ok(inverseExpression?.leftExpression,
    "the fixture must expose expression metadata for the inverse endpoint");
inverseExpression.leftExpression = { kind: "atom", name: "face10Composite3", arguments: [] };
assert.throws(
    () => register(forgedInverse),
    /三维 HIT.*(?:expression|表达式|metadata).*不一致/,
    "Core must reconstruct inverse endpoint expressions instead of trusting forged metadata"
);

console.log("sandbox composite third-path regression passed");
