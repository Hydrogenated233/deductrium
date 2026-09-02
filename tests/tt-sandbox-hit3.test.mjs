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
assert.deepEqual(parsed.pathLevels[2].constructors.map(path => path.name), ["cell3"]);
assert.deepEqual(
    parsed.pathLevels.map(entry => ({
        level: entry.level,
        names: entry.constructors.map(path => path.name)
    })),
    [
        { level: 1, names: ["loopA3", "loopB3"] },
        { level: 2, names: ["faceA3", "faceB3"] },
        { level: 3, names: ["cell3"] }
    ]
);
const cell = parsed.pathLevels[2].constructors[0];
assert.equal(headName(cell.left), "faceA3");
assert.equal(headName(cell.right), "faceB3");
assert.equal(cell.leftTwoPath, "faceA3");
assert.equal(cell.rightTwoPath, "faceB3");
assert.equal(headName(cell.sourcePath), "loopA3");
assert.equal(headName(cell.targetPath), "loopB3");
assert.equal(headName(cell.sourcePoint), "base3");
assert.equal(headName(cell.targetPoint), "base3");

const bundle = lowerSandboxHit(parsed);

assert.equal(Object.hasOwn(parsed, "pathConstructors"), false);
assert.equal(Object.hasOwn(parsed, "twoPathConstructors"), false);
assert.equal(Object.hasOwn(parsed, "threePathConstructors"), false);

const sparsePathLevels = structuredClone(parsed);
sparsePathLevels.pathLevels[1].constructors = [];
assert.throws(
    () => lowerSandboxHit(sparsePathLevels),
    /第 3 阶不能越过空的低阶路径层级/
);

assert.equal(bundle.metadata.version, 7);
assert.equal(bundle.metadata.kind, "hit3");
assert.equal(bundle.metadata.dimension, 3);
assert.equal(bundle.metadata.ruleSchemaVersion, 1);
const threePathMetadata = bundle.metadata.pathLevels[2].constructors;
assert.equal(threePathMetadata[0].name, "cell3");
assert.equal(threePathMetadata[0].computationName, "apd3_cell3");
assert.equal(threePathMetadata[0].actionComputationName, "ap3_cell3");
assert.equal(bundle.metadata.threePathConstructors, undefined);
assert.ok(bundle.auxiliaryTypes.some(([name]) => name === "cell3"));
for (const name of ["apd_cell3", "@apd_cell3", "ap_cell3", "@ap_cell3"]) {
    assert.equal(bundle.auxiliaryTypes.some(([entryName]) => entryName === name), false);
    assert.equal(bundle.computeRules[name], undefined);
}
assert.equal(bundle.computeRules.cell3, undefined);
const countNodes = ast => {
    let count = 0;
    const stack = [ast];
    while (stack.length) {
        const current = stack.pop();
        if (!current) continue;
        count++;
        stack.push(...(current.nodes ?? []));
    }
    return count;
};
assert.ok(
    countNodes(bundle.auxiliaryTypes.find(([name]) => name === "apd3_cell3")[1]) > 256,
    "the regression must exercise a path3 result beyond the legacy output-node cap"
);
for (const name of ["ap3_cell3", "@ap3_cell3"]) {
    assert.ok(bundle.auxiliaryTypes.some(([entryName]) => entryName === name));
    assert.equal(bundle.computeRules[name], undefined);
}
for (const name of ["apd3_cell3", "@apd3_cell3"]) {
    assert.ok(bundle.auxiliaryTypes.some(([entryName]) => entryName === name));
    assert.equal(bundle.computeRules[name], undefined);
}

const sandbox = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const added = sandbox.add(cubeSource);
assert.equal(added.ok, true, added.error);
assert.equal(added.declarations[0].status, "valid");
assert.ok(added.declarations[0].generatedNames.includes("cell3"));
assert.equal(added.declarations[0].generatedNames.includes("apd_cell3"), false);
assert.ok(added.declarations[0].generatedNames.includes("apd3_cell3"));
assert.ok(added.declarations[0].generatedNames.includes("ap3_cell3"));
assert.equal(sandbox.check("cell3 : faceA3 = faceB3").ok, true);
assert.equal(sandbox.check("ap3_cell3").ok, true);
assert.equal(sandbox.check("@ap3_cell3").ok, true);
assert.equal(sandbox.check("apd3_cell3").ok, true);
assert.equal(sandbox.check("@apd3_cell3").ok, true);

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
const useApd3 = sandbox.add(
    "useApd3 := λC:Cube3→U.λc:(C base3)."
        + "λp0:((trans C loopA3 c)=c)."
        + "λp1:((trans C loopB3 c)=c)."
        + "λp2a:(p0=((trans2 C faceA3 c)▪p1))."
        + "λp2b:(p0=((trans2 C faceB3 c)▪p1))."
        + "λp3:((trans (λr:(loopA3=loopB3).p0=((trans2 C r c)▪p1)) cell3 p2a)=p2b)."
        + "apd3_cell3 C c p0 p1 p2a p2b p3"
);
assert.equal(useApd3.ok, true, useApd3.error);
const useAp3 = sandbox.add(
    "useAp3 := λC:U.λr:C.λq0:(r=r).λq1:(r=r)."
        + "λq2a:(q0=q1).λq2b:(q0=q1).λq3:(q2a=q2b)."
        + "ap3_cell3 C r q0 q1 q2a q2b q3"
);
assert.equal(useAp3.ok, true, useAp3.error);
assert.equal(
    sandbox.check("rec_Cube3 True true rfl rfl rfl rfl rfl base3 === true").ok,
    true
);

const bridge = sandbox.bridge();
assert.equal(bridge.inductives[0].metadata.kind, "hit3");
assert.equal(bridge.inductives[0].metadata.pathLevels[2].constructors[0].name, "cell3");
const restored = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
restored.load(JSON.parse(sandbox.serialize()));
assert.equal(restored.getDeclarations()[0].status, "valid");
assert.equal(restored.bridge().inductives[0].metadata.kind, "hit3");
assert.equal(restored.check("cell3 : faceA3 = faceB3").ok, true);
assert.equal(restored.check("ap3_cell3").ok, true);
assert.equal(restored.check("apd3_cell3").ok, true);

const parameterizedSource = "hit CubeP (A : U) : U "
    + "| baseP : CubeP A "
    + "| loopAP : Πz:A,baseP=baseP "
    + "| loopBP : Πz:A,baseP=baseP "
    + "| path2 faceAP : Πz:A,loopAP z=loopBP z "
    + "| path2 faceBP : Πz:A,loopAP z=loopBP z "
    + "| path3 cellP : Πz:A,faceAP A z=faceBP A z";
const parameterized = parseSandboxHit(parameterizedSource);
const parameterizedCell = parameterized.pathLevels[2].constructors[0];
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

const parameterizedSandbox = new SandboxEnvironment({
    systemRuleIds: creativeSandboxSystemRuleIds
});
const parameterizedAdded = parameterizedSandbox.add(parameterizedSource);
assert.equal(parameterizedAdded.ok, true, parameterizedAdded.error);
assert.equal(parameterizedSandbox.check("apd3_cellP").ok, true);
assert.equal(parameterizedSandbox.check("@apd3_cellP").ok, true);
assert.equal(parameterizedSandbox.add("useApd3P := apd3_cellP").ok, true);
assert.equal(parameterizedSandbox.add("useFullApd3P := @apd3_cellP").ok, true);

const reservedParameterSource = "hit CubeReserved (trans : U) : U "
    + "| baseR : CubeReserved trans "
    + "| loopRA : baseR=baseR | loopRB : baseR=baseR "
    + "| path2 faceRA : loopRA=loopRB | path2 faceRB : loopRA=loopRB "
    + "| path3 cellR : faceRA=faceRB";
const reservedParameterBundle = lowerSandboxHit(parseSandboxHit(reservedParameterSource));
assert.match(parser.stringify(reservedParameterBundle.type[1]), /param_trans/,
    "pathLevels must be refreshed after a reserved uniform parameter is renamed");
const reservedParameterSandbox = new SandboxEnvironment({
    systemRuleIds: creativeSandboxSystemRuleIds
});
assert.equal(
    reservedParameterSandbox.add(reservedParameterSource).ok,
    true,
    "renamed uniform parameters must propagate through all three path levels"
);

const wrongKind = structuredClone(bundle);
wrongKind.metadata.kind = "hit2";
wrongKind.metadata.dimension = 2;
assert.throws(() => register(wrongKind), /摘要与 pathLevels 不一致/);

const wrongBoundary = structuredClone(bundle);
wrongBoundary.metadata.pathLevels[2].constructors[0].sourcePath = parser.parse("loopB3");
assert.throws(() => register(wrongBoundary), /v7.*不能携带 legacy 冗余字段/);

const wrongEndpoint = structuredClone(bundle);
wrongEndpoint.metadata.pathLevels[2].constructors[0].leftExpression.name = "faceB3";
assert.throws(() => register(wrongEndpoint), /端点与 metadata 不一致/);

const wrongComputationName = structuredClone(bundle);
wrongComputationName.metadata.pathLevels[2].constructors[0].computationName = "apd_cell3";
assert.throws(
    () => register(wrongComputationName),
    /三维 HIT dependent 计算定理不存在/
);

const missingArgumentNames = structuredClone(bundle);
delete missingArgumentNames.metadata.pathLevels[2].constructors[0].argumentNames;
assert.throws(() => register(missingArgumentNames), /argumentNames 与 telescope 不一致/);

const definitionalCell = structuredClone(bundle);
definitionalCell.computeRules.cell3 = [{
    pattern: [parser.parse("cell3")],
    result: parser.parse("faceA3")
}];
assert.throws(() => register(definitionalCell), /路径构造子不能注册为定义计算规则/);

const forgedAction = structuredClone(bundle);
const actionTypes = new Map(forgedAction.auxiliaryTypes);
for (const [target, source] of [
    ["ap3_cell3", "ap2_faceA3"],
    ["@ap3_cell3", "@ap2_faceA3"]
]) {
    const index = forgedAction.auxiliaryTypes.findIndex(([name]) => name === target);
    forgedAction.auxiliaryTypes[index] = [target, structuredClone(actionTypes.get(source))];
}
assert.throws(
    () => register(forgedAction),
    /三维 HIT action 计算定理 ap3_cell3 与 metadata 不一致/
);

const forgedDependent = structuredClone(bundle);
const dependentTypes = new Map(forgedDependent.auxiliaryTypes);
for (const [target, source] of [
    ["apd3_cell3", "apd_faceA3"],
    ["@apd3_cell3", "@apd_faceA3"]
]) {
    const index = forgedDependent.auxiliaryTypes.findIndex(([name]) => name === target);
    forgedDependent.auxiliaryTypes[index] = [target, structuredClone(dependentTypes.get(source))];
}
assert.throws(
    () => register(forgedDependent),
    /三维 HIT dependent 计算定理 apd3_cell3 与 metadata 不一致/
);

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
