import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { lowerSandboxHit, parseSandboxHit } from "../js/tt/sandbox.js";

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

assert.throws(
    () => lowerSandboxHit(parsed),
    /三维 HIT 已完成结构解析.*Core lowering 尚未启用/
);

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

assert.throws(
    () => new TTCoreEngine().core.registerSystemInductive({
        type: ["UnsafeHit3", parser.parse("U")],
        constructors: [],
        metadata: {
            version: 5,
            kind: "hit3",
            dimension: 3,
            ruleSchemaVersion: 1,
            typeName: "UnsafeHit3",
            eliminatorName: "ind_UnsafeHit3",
            constructors: []
        }
    }),
    /Core 注册尚未启用.*拒绝未经认证的三阶 coherence/
);

console.log("sandbox third-path parser boundary regression passed");
