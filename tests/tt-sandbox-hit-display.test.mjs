import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

import { ASTParser } from "../js/tt/astparser.js";
import {
    cloneInductiveBundle,
    sandboxInductiveEntryPresentation
} from "../js/tt/gui.js";
import {
    sandboxDeclarationDisplayKind,
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

const indexHtml = await readFile(new URL("../index.html", import.meta.url), "utf8");
assert.match(indexHtml, /hit Circle2 : U \| base2 : Circle2 \| loop2 : base2 = base2/);
assert.match(indexHtml, /apd_loop2[\s\S]*ap_loop2/);
assert.match(indexHtml, /路径构造子的 <code>apd_<\/code>\/<code>ap_<\/code> 规则是需要显式使用的命题/);

console.log("sandbox HIT bridge and display regression passed");
