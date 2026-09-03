import assert from "node:assert/strict";

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
const register = candidate => {
    const engine = new TTCoreEngine();
    engine.configure({ unlockedTypes: creativeSandboxSystemRuleIds });
    return engine.core.registerSystemInductive(candidate);
};

const source = "hit ReflCell3 : U "
    + "| baseRC : ReflCell3 "
    + "| loopRC : baseRC=baseRC "
    + "| path2 faceRC : loopRC=loopRC "
    + "| path3 cellRC : (refl loopRC)=faceRC";

const parsed = parseSandboxHit(source);
const cell = parsed.pathLevels[2].constructors[0];
assert.deepEqual(cell.leftExpression, {
    kind: "refl",
    pathName: "loopRC",
    arguments: []
});
assert.deepEqual(cell.rightExpression, {
    kind: "atom",
    name: "faceRC",
    arguments: []
});
assert.match(parser.stringify(cell.left), /refl.*loopRC/);

const bundle = lowerSandboxHit(parsed);
assert.equal(bundle.metadata.kind, "hit3");
assert.deepEqual(bundle.metadata.pathLevels[2].constructors[0].leftExpression, {
    kind: "refl",
    pathName: "loopRC",
    arguments: []
});
for (const name of ["cellRC", "ap3_cellRC", "@ap3_cellRC", "apd3_cellRC", "@apd3_cellRC"]) {
    assert.ok(bundle.generatedNames.includes(name), `${name} must be exported by path3 refl lowering`);
}
assert.doesNotThrow(() => register(structuredClone(bundle)));

const sandbox = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const added = sandbox.add(source);
assert.equal(added.ok, true, added.error);
for (const name of ["cellRC", "ap3_cellRC", "@ap3_cellRC", "apd3_cellRC", "@apd3_cellRC"]) {
    assert.equal(sandbox.check(name).ok, true, `${name} must have a formed type`);
}

const parameterizedSource = "hit ReflCellP (A:U) : U "
    + "| baseRP : ReflCellP A "
    + "| loopRP : Πz:A,baseRP=baseRP "
    + "| path2 faceRP : Πz:A,loopRP z=loopRP z "
    + "| path3 cellRP : Πz:A,(refl (loopRP z))=faceRP z";
const parameterized = parseSandboxHit(parameterizedSource);
const parameterizedRefl = parameterized.pathLevels[2].constructors[0].leftExpression;
assert.equal(parameterizedRefl.kind, "refl");
assert.equal(parameterizedRefl.pathName, "loopRP");
assert.deepEqual(parameterizedRefl.arguments.map(argument => parser.stringify(argument)), ["z"]);
const parameterizedBundle = lowerSandboxHit(parameterized);
assert.doesNotThrow(() => register(structuredClone(parameterizedBundle)));
const parameterizedSandbox = new SandboxEnvironment({
    systemRuleIds: creativeSandboxSystemRuleIds
});
assert.equal(parameterizedSandbox.add(parameterizedSource).ok, true);
assert.equal(parameterizedSandbox.check("ap3_cellRP").ok, true);
assert.equal(parameterizedSandbox.check("apd3_cellRP").ok, true);

const recursiveVisitorSource = "hit ReflVisitor3 : U "
    + "| baseRV : ReflVisitor3 "
    + "| loopRV : baseRV=baseRV "
    + "| path2 faceRV : loopRV=loopRV "
    + "| path3 composeRV : ((refl loopRV)▪faceRV)=faceRV "
    + "| path3 inverseRV : (inveq (refl loopRV))=(refl loopRV)";
const recursiveVisitor = parseSandboxHit(recursiveVisitorSource);
assert.equal(recursiveVisitor.pathLevels[2].constructors[0].leftExpression.kind, "compose");
assert.equal(
    recursiveVisitor.pathLevels[2].constructors[0].leftExpression.left.kind,
    "refl"
);
assert.equal(recursiveVisitor.pathLevels[2].constructors[1].leftExpression.kind, "inverse");
assert.equal(
    recursiveVisitor.pathLevels[2].constructors[1].leftExpression.value.kind,
    "refl"
);
const recursiveVisitorBundle = lowerSandboxHit(recursiveVisitor);
assert.doesNotThrow(() => register(structuredClone(recursiveVisitorBundle)));
for (const name of [
    "ap3_composeRV", "apd3_composeRV", "ap3_inverseRV", "apd3_inverseRV"
]) {
    assert.ok(recursiveVisitorBundle.generatedNames.includes(name));
}

const assist = new TTAssistEngine();
assist.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    trustedInductives: [bundle],
    inferDisplayMode: "_",
    timeout: 60_000,
    language: "zh"
});
const assistOptions = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};
let snapshot = assist.start(parser.stringify(bundle.eliminator[1]), assistOptions);
for (const command of [
    "intro C", "intro c0", "intro p0", "intro p2", "intro p3", "intro x",
    "induction x", "exact c0", "exact p0", "exact p2", "exact p3"
]) snapshot = assist.apply(command);
assert.equal(snapshot.goals.length, 0,
    "proof-assistant induction must expose and discharge the refl path3 coherence slot");
assert.match(assist.qed().proof, /ind_ReflCell3/);

const save = sandbox.toJSON();
assert.equal(Object.hasOwn(save.declarations[0], "hit"), false);
const worker = new SandboxWorkerSession();
const restored = worker.handle({
    id: 1,
    kind: "load",
    save: structuredClone(save),
    options: { systemRuleIds: creativeSandboxSystemRuleIds }
});
assert.equal(restored.ok, true, restored.error);
assert.equal(restored.bridge.inductives[0].metadata.kind, "hit3");
assert.equal(worker.handle({
    id: 2,
    kind: "check",
    source: "apd3_cellRC",
    options: { systemRuleIds: creativeSandboxSystemRuleIds }
}).ok, true);

for (const [label, invalidSource, error] of [
    [
        "point constructor under refl",
        "hit BadReflPoint : U | bp:BadReflPoint | lp:bp=bp "
            + "| path2 fp:lp=lp | path3 cp:(refl bp)=fp",
        /refl.*一阶路径构造子/
    ],
    [
        "second path under refl",
        "hit BadReflFace : U | bf:BadReflFace | lf:bf=bf "
            + "| path2 ff:lf=lf | path3 cf:(refl ff)=ff",
        /refl.*一阶路径构造子/
    ],
    [
        "compound path under refl",
        "hit BadReflCompound : U | bc:BadReflCompound | lc:bc=bc "
            + "| path2 fc:lc=lc | path3 cc:(refl (lc▪lc))=fc",
        /refl.*一阶路径构造子/
    ],
    [
        "unknown path under refl",
        "hit BadReflUnknown : U | bu:BadReflUnknown | lu:bu=bu "
            + "| path2 fu:lu=lu | path3 cu:(refl missingU)=fu",
        /refl.*一阶路径构造子/
    ],
    [
        "wrong path argument arity",
        "hit BadReflArity (A:U) : U | ba:BadReflArity A "
            + "| la:Πz:A,ba=ba | path2 fa:Πz:A,la z=la z "
            + "| path3 ca:Πz:A,(refl la)=fa z",
        /refl.*参数数量错误/
    ]
]) {
    assert.throws(() => parseSandboxHit(invalidSource), error, label);
}

const forgedUnknownPath = structuredClone(bundle);
forgedUnknownPath.metadata.pathLevels[2].constructors[0].leftExpression.pathName = "missingRC";
assert.throws(
    () => register(forgedUnknownPath),
    /一阶路径不存在|metadata.*不一致/,
    "Core must independently reject an unknown refl path"
);

const forgedArity = structuredClone(bundle);
forgedArity.metadata.pathLevels[2].constructors[0].leftExpression.arguments.push(
    parser.parse("true")
);
assert.throws(
    () => register(forgedArity),
    /参数数量.*telescope|metadata.*不一致/,
    "Core must independently reject forged refl argument arity"
);

const forgedShape = structuredClone(bundle);
forgedShape.metadata.pathLevels[2].constructors[0].leftExpression.extra = true;
assert.throws(
    () => register(forgedShape),
    /refl 结构无效/,
    "Core must reject unknown fields in refl metadata"
);

console.log("sandbox path3 refl endpoint regression passed");
