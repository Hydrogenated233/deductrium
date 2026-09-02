import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import {
    SandboxEnvironment,
    creativeSandboxSystemRuleIds,
    lowerSandboxHit,
    parseSandboxHit
} from "../js/tt/sandbox.js";

const parser = new ASTParser();
const headName = ast => {
    let current = ast;
    while (current?.type === "apply") current = current.nodes?.[0];
    return current?.type === "var" ? current.name : "";
};

const cubeSource = "hit Cube3 : U "
    + "| base3 : Cube3 "
    + "| loopA3 : base3 = base3 "
    + "| loopB3 : base3 = base3 "
    + "| path2 faceA3 : loopA3 = loopB3 "
    + "| path2 faceB3 : loopA3 = loopB3 "
    + "| path3 cell3 : faceA3 = faceB3";

const parsed = parseSandboxHit(cubeSource);
assert.deepEqual(parsed.threePathConstructors.map(path => path.name), ["cell3"]);
const cell = parsed.threePathConstructors[0];
assert.equal(headName(cell.left), "faceA3");
assert.equal(headName(cell.right), "faceB3");
assert.equal(cell.leftTwoPath, "faceA3");
assert.equal(cell.rightTwoPath, "faceB3");
assert.equal(headName(cell.sourcePath), "loopA3");
assert.equal(headName(cell.targetPath), "loopB3");
assert.equal(headName(cell.sourcePoint), "base3");
assert.equal(headName(cell.targetPoint), "base3");

const bundle = lowerSandboxHit(parsed);
assert.equal(bundle.metadata.version, 5);
assert.equal(bundle.metadata.kind, "hit3");
assert.equal(bundle.metadata.dimension, 3);
assert.equal(bundle.metadata.ruleSchemaVersion, 1);
assert.equal(bundle.metadata.threePathConstructors[0].name, "cell3");
assert.equal(bundle.metadata.threePathConstructors[0].computationName, undefined);
assert.ok(bundle.auxiliaryTypes.some(([name]) => name === "cell3"));
for (const name of ["apd_cell3", "@apd_cell3", "ap_cell3", "@ap_cell3"]) {
    assert.equal(bundle.auxiliaryTypes.some(([entryName]) => entryName === name), false);
    assert.equal(bundle.computeRules[name], undefined);
}
assert.equal(bundle.computeRules.cell3, undefined);

const sandbox = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const added = sandbox.add(cubeSource);
assert.equal(added.ok, true, added.error);
assert.equal(added.declarations[0].status, "valid");
assert.ok(added.declarations[0].generatedNames.includes("cell3"));
assert.equal(added.declarations[0].generatedNames.includes("apd_cell3"), false);
assert.equal(sandbox.check("cell3 : faceA3 = faceB3").ok, true);

const useInd3 = sandbox.add(
    "useInd3 := λC:Cube3→U.λc:(C base3)."
        + "λp0:((trans C loopA3 c)=c)."
        + "λp1:((trans C loopB3 c)=c)."
        + "λp2a:(p0=((trans2 C faceA3 c)▪p1))."
        + "λp2b:(p0=((trans2 C faceB3 c)▪p1))."
        + "λp3:((trans (λr:(loopA3=loopB3).p0=((trans2 C r c)▪p1)) cell3 p2a)=p2b)."
        + "ind_Cube3 C c p0 p1 p2a p2b p3"
);
assert.equal(useInd3.ok, true, useInd3.error);
assert.equal(sandbox.check("useInd3").ok, true);
assert.equal(
    sandbox.check("rec_Cube3 True true rfl rfl rfl rfl rfl base3 === true").ok,
    true
);

const bridge = sandbox.bridge();
assert.equal(bridge.inductives[0].metadata.kind, "hit3");
assert.equal(bridge.inductives[0].metadata.threePathConstructors[0].name, "cell3");
const restored = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
restored.load(JSON.parse(sandbox.serialize()));
assert.equal(restored.getDeclarations()[0].status, "valid");
assert.equal(restored.bridge().inductives[0].metadata.kind, "hit3");
assert.equal(restored.check("cell3 : faceA3 = faceB3").ok, true);

const parameterized = parseSandboxHit(
    "hit CubeP (A : U) : U "
        + "| baseP : CubeP A "
        + "| loopAP : Πz:A,baseP=baseP "
        + "| loopBP : Πz:A,baseP=baseP "
        + "| path2 faceAP : Πz:A,loopAP z=loopBP z "
        + "| path2 faceBP : Πz:A,loopAP z=loopBP z "
        + "| path3 cellP : Πz:A,faceAP A z=faceBP A z"
);
const parameterizedCell = parameterized.threePathConstructors[0];
assert.deepEqual(parameterizedCell.arguments.map(argument => argument.name), ["z"]);
assert.equal(headName(parameterizedCell.sourcePath), "loopAP");
assert.equal(headName(parameterizedCell.targetPath), "loopBP");
assert.match(parser.stringify(parameterizedCell.left), /faceAP/);
assert.match(parser.stringify(parameterizedCell.right), /faceBP/);

assert.throws(
    () => parseSandboxHit(
        "hit BadOrder3 : U | baseO3 : BadOrder3 "
            + "| loopO3 : baseO3=baseO3 "
            + "| path3 cellO3 : faceO3=faceO3 "
            + "| path2 faceO3 : loopO3=loopO3"
    ),
    /三阶路径构造子必须写在二阶路径构造子之后/
);

assert.throws(
    () => parseSandboxHit(
        "hit BadEndpoint3 : U | baseE3 : BadEndpoint3 "
            + "| loopE3 : baseE3=baseE3 "
            + "| path2 faceE3 : loopE3=loopE3 "
            + "| path3 cellE3 : loopE3=faceE3"
    ),
    /三阶路径构造子.*端点必须由 BadEndpoint3 的二阶路径构造子形成/
);

assert.throws(
    () => parseSandboxHit(
        "hit BadBoundary3 : U | baseB3 : BadBoundary3 "
            + "| loopB31 : baseB3=baseB3 "
            + "| loopB32 : baseB3=baseB3 "
            + "| loopB33 : baseB3=baseB3 "
            + "| path2 faceB31 : loopB31=loopB32 "
            + "| path2 faceB32 : loopB31=loopB33 "
            + "| path3 cellB3 : faceB31=faceB32"
    ),
    /三阶路径构造子.*二阶路径边界不一致/
);

assert.throws(
    () => parseSandboxHit(
        "hit BadArgs3 (A : U) : U | baseA3 : BadArgs3 A "
            + "| loopA31 : Πz:A,baseA3=baseA3 "
            + "| loopA32 : Πz:A,baseA3=baseA3 "
            + "| path2 faceA31 : Πz:A,loopA31 z=loopA32 z "
            + "| path2 faceA32 : Πz:A,loopA31 z=loopA32 z "
            + "| path3 cellA3 : Πx:A,Πy:A,faceA31 x=faceA32 y"
    ),
    /三阶路径构造子.*二阶路径边界不一致/
);

assert.throws(
    () => parseSandboxHit(
        cubeSource + " | path4 hyper3 : cell3=cell3"
    ),
    /最高只解析三维 HIT.*path4/
);

const register = candidate => {
    const engine = new TTCoreEngine();
    engine.configure({ unlockedTypes: creativeSandboxSystemRuleIds });
    return engine.core.registerSystemInductive(candidate);
};
assert.doesNotThrow(() => register(structuredClone(bundle)));
assert.doesNotThrow(() => register(lowerSandboxHit(parameterized)));

const wrongKind = structuredClone(bundle);
wrongKind.metadata.kind = "hit2";
wrongKind.metadata.dimension = 2;
assert.throws(() => register(wrongKind), /二维 HIT metadata 不能包含三阶路径构造子/);

const wrongBoundary = structuredClone(bundle);
wrongBoundary.metadata.threePathConstructors[0].sourcePath = parser.parse("loopB3");
assert.throws(() => register(wrongBoundary), /边界 metadata 不一致/);

const wrongEndpoint = structuredClone(bundle);
wrongEndpoint.metadata.threePathConstructors[0].left = parser.parse("faceB3");
assert.throws(() => register(wrongEndpoint), /端点与 metadata 不一致/);

const prematureComputation = structuredClone(bundle);
prematureComputation.metadata.threePathConstructors[0].computationName = "apd_cell3";
assert.throws(() => register(prematureComputation), /三维 HIT 计算定理尚未开放/);

const missingArgumentNames = structuredClone(bundle);
delete missingArgumentNames.metadata.threePathConstructors[0].argumentNames;
assert.throws(() => register(missingArgumentNames), /argumentNames 与 telescope 不一致/);

const definitionalCell = structuredClone(bundle);
definitionalCell.computeRules.cell3 = [{
    pattern: [parser.parse("cell3")],
    result: parser.parse("faceA3")
}];
assert.throws(() => register(definitionalCell), /路径构造子不能注册为定义计算规则/);

const forgedCoherence = structuredClone(bundle);
const replaceThreeCoherenceWithTrue = ast => {
    if (!ast) return;
    if ((ast.type === "P" || ast.type === "->")
        && (ast.name === "p3_0" || ast.name === "q3_0")) {
        ast.nodes[0] = parser.parse("True");
    }
    for (const child of ast.nodes ?? []) replaceThreeCoherenceWithTrue(child);
};
replaceThreeCoherenceWithTrue(forgedCoherence.eliminator[1]);
replaceThreeCoherenceWithTrue(forgedCoherence.recursor[1]);
for (const [, type] of forgedCoherence.auxiliaryTypes) {
    replaceThreeCoherenceWithTrue(type);
}
assert.throws(
    () => register(forgedCoherence),
    /三阶 coherence cell3 与 metadata 不一致/
);

console.log("sandbox third-path lowering and Core boundary regression passed");
