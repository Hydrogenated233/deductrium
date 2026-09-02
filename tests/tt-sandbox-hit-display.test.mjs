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
assert.notEqual(cloned.metadata.pathConstructors[0].left,
    bundle.metadata.pathConstructors[0].left);
assert.notEqual(cloned.metadata.pathConstructors[0].argumentTypes[0],
    bundle.metadata.pathConstructors[0].argumentTypes[0]);
bundle.metadata.pathConstructors[0].left.name = "mutatedLeft";
cloned.metadata.pathConstructors[0].right.name = "mutatedRight";
assert.equal(cloned.metadata.pathConstructors[0].left.name, "baseDisplay");
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
            argumentTypes: [parse("True")],
            left: parse("loopSquareA"),
            right: parse("loopSquareB"),
            leftPath: "loopSquareA",
            rightPath: "loopSquareB",
            computationName: "apd_squarePath"
        }]
    }
};

const clonedHit2 = cloneInductiveBundle(hit2Bundle);
assert.equal(clonedHit2.metadata.kind, "hit2");
assert.equal(clonedHit2.metadata.dimension, 2);
assert.equal(clonedHit2.metadata.twoPathConstructors[0].leftPath, "loopSquareA");
assert.equal(clonedHit2.metadata.twoPathConstructors[0].rightPath, "loopSquareB");
assert.notEqual(clonedHit2.metadata.twoPathConstructors[0].left,
    hit2Bundle.metadata.twoPathConstructors[0].left);
assert.notEqual(clonedHit2.metadata.twoPathConstructors[0].argumentTypes[0],
    hit2Bundle.metadata.twoPathConstructors[0].argumentTypes[0]);
hit2Bundle.metadata.twoPathConstructors[0].left.name = "mutatedLoop";
clonedHit2.metadata.twoPathConstructors[0].right.name = "mutatedLoop";
assert.equal(clonedHit2.metadata.twoPathConstructors[0].left.name, "loopSquareA");
assert.equal(hit2Bundle.metadata.twoPathConstructors[0].right.name, "loopSquareB");

for (const name of ["squarePath", "@squarePath"]) {
    assert.deepEqual(
        sandboxInductiveEntryPresentation(hit2Bundle, name, {
            postfix: "解构",
            category: "eliminator"
        }),
        { postfix: "构造", prefix: "sandbox HIT", category: "constructor" }
    );
}
for (const name of ["apd_squarePath", "@apd_squarePath", "ap_squarePath", "@ap_squarePath"]) {
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
        pathConstructors: [{
            name: "loopDisplay",
            typeSource: "baseDisplay = baseDisplay"
        }]
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
        pathConstructors: [
            { name: "loopSquareA", typeSource: "baseSquare = baseSquare" },
            { name: "loopSquareB", typeSource: "baseSquare = baseSquare" }
        ],
        twoPathConstructors: [{
            name: "squarePath",
            typeSource: "loopSquareA = loopSquareB"
        }]
    }
}), {
    kind: "HIT",
    trust: "二维高阶路径归纳",
    trustClass: "sandbox-hit"
});
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
assert.match(indexHtml, /最高维度是二维[\s\S]*path3/);
assert.match(indexHtml, /路径构造子的 <code>apd_<\/code>\/<code>ap_<\/code> 规则是需要显式使用的命题/);

console.log("sandbox HIT bridge and display regression passed");
