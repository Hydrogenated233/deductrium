import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

import { ASTParser } from "../js/tt/astparser.js";
import { createSandboxDeclaration } from "../js/tt/sandbox.js";
import {
    cloneInductiveBundle,
    sandboxInductiveEntryPresentation
} from "../js/tt/gui.js";
import {
    sandboxDeclarationDisplayKind,
    sandboxInductiveDisplayAsts,
    sandboxInductiveDisplaySources
} from "../js/tt/sandbox-gui.js";

const parser = new ASTParser();
const parse = source => parser.parse(source);

const bundle = {
    type: ["CircleDisplay", parse("U")],
    constructors: [["baseDisplay", parse("CircleDisplay")]],
    auxiliaryTypes: [
        ["loopDisplay", parse("baseDisplay = baseDisplay")],
        ["@apd_loopDisplay", parse("True")]
    ],
    definitions: [["ap_loopDisplay", parse("true")]],
    metadata: {
        version: 3,
        kind: "hit1",
        dimension: 1,
        typeName: "CircleDisplay",
        eliminatorName: "ind_CircleDisplay",
        constructors: [{ name: "baseDisplay", argumentTypes: [] }],
        pathConstructors: [{
            name: "loopDisplay",
            argumentTypes: [parse("True")],
            left: parse("baseDisplay"),
            right: parse("baseDisplay"),
            computationName: "apd_loopDisplay"
        }]
    }
};

const cloned = cloneInductiveBundle(bundle);
assert.equal(cloned.metadata.kind, "hit1");
assert.equal(cloned.metadata.dimension, 1);
assert.equal(cloned.metadata.version, 8);
const clonedPath = cloned.metadata.pathLevels[0].constructors[0];
assert.notEqual(clonedPath.left,
    bundle.metadata.pathConstructors[0].left);
assert.notEqual(clonedPath.argumentTypes[0],
    bundle.metadata.pathConstructors[0].argumentTypes[0]);
bundle.metadata.pathConstructors[0].left.name = "mutatedLeft";
clonedPath.right.name = "mutatedRight";
assert.equal(clonedPath.left.name, "baseDisplay");
assert.equal(bundle.metadata.pathConstructors[0].right.name, "baseDisplay");

const hit2Bundle = {
    type: ["Hit2Display", parse("U")],
    constructors: [["baseSquare", parse("Hit2Display")]],
    auxiliaryTypes: [
        ["loopSquareA", parse("baseSquare = baseSquare")],
        ["loopSquareB", parse("baseSquare = baseSquare")],
        ["squarePath", parse("loopSquareA = loopSquareB")],
        ["@apd_squarePath", parse("True")]
    ],
    definitions: [["ap_squarePath", parse("true")]],
    metadata: {
        version: 4,
        kind: "hit2",
        dimension: 2,
        typeName: "Hit2Display",
        eliminatorName: "ind_Hit2Display",
        constructors: [{ name: "baseSquare", argumentTypes: [] }],
        pathConstructors: [
            {
                name: "loopSquareA",
                argumentTypes: [],
                left: parse("baseSquare"),
                right: parse("baseSquare"),
                computationName: "apd_loopSquareA"
            },
            {
                name: "loopSquareB",
                argumentTypes: [],
                left: parse("baseSquare"),
                right: parse("baseSquare"),
                computationName: "apd_loopSquareB"
            }
        ],
        twoPathConstructors: [{
            name: "squarePath",
            argumentTypes: [],
            left: parse("loopSquareA"),
            right: parse("loopSquareB"),
            leftPath: "loopSquareA",
            rightPath: "loopSquareB",
            computationName: "apd_squarePath",
            strongComputationName: "ap2_squarePath"
        }]
    }
};

const clonedHit2 = cloneInductiveBundle(hit2Bundle);
assert.equal(clonedHit2.metadata.kind, "hit2");
assert.equal(clonedHit2.metadata.dimension, 2);
assert.equal(clonedHit2.metadata.version, 8);
const clonedTwoPath = clonedHit2.metadata.pathLevels[1].constructors[0];
assert.deepEqual(clonedTwoPath.leftExpression, {
    kind: "atom",
    name: "loopSquareA",
    arguments: []
});
assert.deepEqual(clonedTwoPath.rightExpression, {
    kind: "atom",
    name: "loopSquareB",
    arguments: []
});
hit2Bundle.metadata.twoPathConstructors[0].left.name = "mutatedLoop";
clonedTwoPath.rightExpression.name = "mutatedLoop";
assert.equal(clonedTwoPath.leftExpression.name, "loopSquareA");
assert.equal(hit2Bundle.metadata.twoPathConstructors[0].right.name, "loopSquareB");
hit2Bundle.metadata.twoPathConstructors[0].left.name = "loopSquareA";

const hit3Bundle = structuredClone(hit2Bundle);
hit3Bundle.metadata.version = 5;
hit3Bundle.metadata.kind = "hit3";
hit3Bundle.metadata.dimension = 3;
hit3Bundle.metadata.threePathConstructors = [{
    name: "cubePath",
    argumentTypes: [parse("True")],
    left: parse("squarePath"),
    right: parse("squarePath"),
    leftTwoPath: "squarePath",
    rightTwoPath: "squarePath",
    sourcePath: parse("loopSquareA"),
    targetPath: parse("loopSquareB"),
    actionComputationName: "ap3_cubePath"
}];
const clonedHit3 = cloneInductiveBundle(hit3Bundle);
assert.equal(clonedHit3.metadata.kind, "hit3");
assert.equal(clonedHit3.metadata.version, 8);
const clonedThreePath = clonedHit3.metadata.pathLevels[2].constructors[0];
assert.equal(clonedThreePath.leftExpression.name, "squarePath");
assert.equal(clonedThreePath.actionComputationName, "ap3_cubePath");
assert.notEqual(clonedThreePath.leftExpression.arguments,
    hit3Bundle.metadata.threePathConstructors[0].left.nodes);

for (const name of ["squarePath", "@squarePath"]) {
    assert.deepEqual(
        sandboxInductiveEntryPresentation(hit2Bundle, name, {
            postfix: "解构",
            category: "eliminator"
        }),
        { postfix: "构造", prefix: "sandbox HIT", category: "constructor" }
    );
}
for (const name of [
    "apd_squarePath", "@apd_squarePath", "ap_squarePath", "@ap_squarePath", "ap2_squarePath"
]) {
    assert.deepEqual(
        sandboxInductiveEntryPresentation(hit2Bundle, name, {
            postfix: "定义",
            category: "axiom"
        }),
        { postfix: "计算", prefix: "sandbox HIT", category: "compute" },
        `${name} must render as a propositional two-path HIT computation rule`
    );
}
assert.deepEqual(
    sandboxInductiveEntryPresentation(hit3Bundle, "ap3_cubePath", {
        postfix: "定义",
        category: "axiom"
    }),
    { postfix: "计算", prefix: "sandbox HIT", category: "compute" }
);

assert.deepEqual(
    sandboxInductiveEntryPresentation(bundle, "loopDisplay", {
        postfix: "解构",
        category: "eliminator"
    }),
    { postfix: "构造", prefix: "sandbox HIT", category: "constructor" }
);
assert.deepEqual(
    sandboxInductiveEntryPresentation(bundle, "@loopDisplay", {
        postfix: "解构",
        category: "eliminator"
    }),
    { postfix: "构造", prefix: "sandbox HIT", category: "constructor" }
);
for (const name of ["apd_loopDisplay", "@apd_loopDisplay", "ap_loopDisplay", "@ap_loopDisplay"]) {
    assert.deepEqual(
        sandboxInductiveEntryPresentation(bundle, name, {
            postfix: "定义",
            category: "axiom"
        }),
        { postfix: "计算", prefix: "sandbox HIT", category: "compute" },
        `${name} must render as a propositional HIT computation rule`
    );
}
assert.deepEqual(
    sandboxInductiveEntryPresentation(bundle, "ind_CircleDisplay", {
        postfix: "解构",
        category: "eliminator"
    }),
    { postfix: "解构", prefix: "sandbox HIT", category: "eliminator" }
);

const hitDeclaration = {
    kind: "hit",
    hit: {
        name: "CircleDisplay",
        parameters: [],
        indices: [],
        universe: "U",
        universeAst: parse("U"),
        pointConstructors: [{ name: "baseDisplay", typeSource: "CircleDisplay" }],
        pathLevels: [
            { level: 1, constructors: [{
                name: "loopDisplay",
                typeSource: "baseDisplay = baseDisplay"
            }] },
            { level: 2, constructors: [] },
            { level: 3, constructors: [] }
        ]
    }
};
assert.deepEqual(sandboxDeclarationDisplayKind(hitDeclaration), {
    kind: "HIT",
    trust: "一阶路径归纳",
    trustClass: "sandbox-hit"
});
assert.deepEqual(sandboxDeclarationDisplayKind({
    kind: "hit",
    hit: {
        name: "SquareDisplay",
        parameters: [],
        indices: [],
        universe: "U",
        universeAst: parse("U"),
        pointConstructors: [{ name: "baseSquare", typeSource: "SquareDisplay" }],
        pathLevels: [
            { level: 1, constructors: [
                { name: "loopSquareA", typeSource: "baseSquare = baseSquare" },
                { name: "loopSquareB", typeSource: "baseSquare = baseSquare" }
            ] },
            { level: 2, constructors: [{
                name: "squarePath",
                typeSource: "loopSquareA = loopSquareB"
            }] },
            { level: 3, constructors: [] }
        ]
    }
}), {
    kind: "HIT",
    trust: "二维高阶路径归纳",
    trustClass: "sandbox-hit"
});
const cubeDeclaration = createSandboxDeclaration(
    "hit CubeDisplay : U | baseCube : CubeDisplay "
        + "| loopCubeA : baseCube=baseCube | loopCubeB : baseCube=baseCube "
        + "| path2 faceCubeA : loopCubeA=loopCubeB "
        + "| path2 faceCubeB : loopCubeA=loopCubeB "
        + "| path3 cellCube : faceCubeA=faceCubeB",
    "display-cube"
);
assert.deepEqual(sandboxDeclarationDisplayKind(cubeDeclaration), {
    kind: "HIT",
    trust: "三维高阶路径归纳",
    trustClass: "sandbox-hit"
});
const cubeSources = sandboxInductiveDisplaySources(cubeDeclaration);
assert.equal(cubeSources.at(-1), "path3 cellCube : (faceCubeA=faceCubeB)");
const cubeEntries = sandboxInductiveDisplayAsts(cubeDeclaration);
assert.ok(cubeEntries);
assert.equal(cubeEntries.at(-1).prefix, "path3 ");
assert.equal(cubeEntries.at(-1).ast.nodes[0].name, "cellCube");
assert.deepEqual(sandboxInductiveDisplaySources(hitDeclaration), [
    "CircleDisplay : U",
    "baseDisplay : CircleDisplay",
    "loopDisplay : baseDisplay = baseDisplay"
]);
assert.deepEqual(sandboxInductiveDisplaySources({
    kind: "hit",
    source: "hit CircleDisplay : U | baseDisplay : CircleDisplay "
        + "| loopDisplay : baseDisplay = baseDisplay"
}), [
    "CircleDisplay : U",
    "baseDisplay : CircleDisplay",
    "loopDisplay : (baseDisplay=baseDisplay)"
], "disabled declarations must retain structured highlighted display after validation drops metadata");

// Display must use the parser-produced AST for constructor names.  Re-parsing
// `Loop2 : ...` as a complete source line would tokenize its leading `L` as
// the lambda marker and produce the spurious `λ(L)未匹配“.”号` diagnostic.
const loop2Declaration = createSandboxDeclaration(
    "hit Circle2 : U | Base2 : Circle2 | Loop2 : Base2 = Base2",
    "display-loop2"
);
const loop2Entries = sandboxInductiveDisplayAsts(loop2Declaration);
assert.ok(loop2Entries);
assert.equal(loop2Entries.length, 3);
assert.deepEqual(
    loop2Entries.map(entry => parser.stringify(entry.ast)),
    ["(Circle2 : U)", "(Base2 : Circle2)", "(Loop2 : (Base2=Base2))"]
);
assert.equal(loop2Entries[2].ast.nodes[0].name, "Loop2");

// Preserve compatibility with older in-memory/save-shaped declarations that
// only carry `typeSource` for constructors.
const legacyLoopEntries = sandboxInductiveDisplayAsts({
    kind: "hit",
    hit: {
        name: "Circle2",
        parameters: [],
        indices: [],
        universe: "U",
        universeAst: parse("U"),
        pointConstructors: [{ name: "Base2", typeSource: "Circle2" }],
        pathConstructors: [{ name: "Loop2", typeSource: "Base2 = Base2" }]
    }
});
assert.ok(legacyLoopEntries);
assert.equal(legacyLoopEntries[2].ast.nodes[0].name, "Loop2");

const square2Declaration = createSandboxDeclaration(
    "hit Square2 : U | Base2 : Square2 | LoopA2 : Base2 = Base2 "
        + "| LoopB2 : Base2 = Base2 | path2 SquarePath2 : LoopA2 = LoopB2",
    "display-square2"
);
const square2Entries = sandboxInductiveDisplayAsts(square2Declaration);
assert.ok(square2Entries);
assert.equal(square2Entries.at(-1).prefix, "path2 ");
assert.equal(square2Entries.at(-1).ast.nodes[0].name, "SquarePath2");

// A source-only declaration from an older save should still render names
// containing the parser's historical X marker.
const legacySurfaceEntries = sandboxInductiveDisplayAsts({
    kind: "hit",
    source: "hit SurfaceX : U | baseX : SurfaceX | loopX : baseX = baseX"
});
assert.ok(legacySurfaceEntries);
assert.equal(legacySurfaceEntries[1].ast.nodes[0].name, "baseX");

const indexHtml = await readFile(new URL("../index.html", import.meta.url), "utf8");
assert.match(indexHtml, /hit Circle2 : U \| base2 : Circle2 \| loop2 : base2 = base2/);
assert.match(indexHtml, /apd_loop2[\s\S]*ap_loop2/);
assert.match(indexHtml, /path2[\s\S]*apd_squareS[\s\S]*ap_squareS/);
assert.match(indexHtml, /ap2_squareS/);
assert.match(indexHtml, /三维 HIT 是当前面向用户的最高维度[\s\S]*path3[\s\S]*▪[\s\S]*inveq[\s\S]*ap3_名称[\s\S]*apd3_名称/);
assert.match(indexHtml, /path4[\s\S]*实验性 fixture[\s\S]*资源限制[\s\S]*明确拒绝四维及更高维/);
assert.match(indexHtml, /路径构造子的 <code>apd_<\/code>\/<code>ap_<\/code> 规则是需要显式使用的命题/);

console.log("sandbox HIT bridge and display regression passed");
