import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";
import {
    collectExplicitAtNames,
    compactImplicitAliasesForDisplay,
    markExplicitAtSyntax
} from "../js/tt/presentation.js";

const parser = new ASTParser();
const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

const compact = (source, userSource = "") => compactImplicitAliasesForDisplay(
    parser.parse(source),
    engine.core.opaque,
    collectExplicitAtNames(userSource)
);

const normalizeForDisplay = source => {
    const ast = engine.core.markBondVars(
        engine.core.desugar(markExplicitAtSyntax(parser.parse(source)), false),
        []
    );
    const normalized = engine.core.semanticKernel.tryNormalize(ast, [], {
        unfoldDefinitions: false,
        maxSteps: 100_000
    });
    assert.ok(normalized, `semantic normalization rejected ${source}`);
    return compactImplicitAliasesForDisplay(
        normalized,
        engine.core.opaque,
        collectExplicitAtNames(source)
    );
};

assert.equal(
    parser.stringify(normalizeForDisplay("(λx:U.x) (eq true true)")),
    "(eq true true)",
    "NbE output must not expose an implicit alias that the user did not write with @"
);
assert.equal(
    parser.stringify(normalizeForDisplay("(λx:U.x) (@eq @0 True true true)")),
    "(@eq @0 True true true)",
    "NbE output must retain an explicit @ alias from the user's source"
);

assert.equal(
    parser.stringify(compact("@eq @0 True true true")),
    "(eq true true)",
    "an elaborated implicit prefix must use the public non-@ alias"
);
assert.equal(
    parser.stringify(compact("@inveq @0 True true true (@refl @0 True true)")),
    "(inveq (refl true))",
    "nested elaborated aliases must be compacted recursively"
);
assert.equal(
    parser.stringify(compact("@eq @0 True true true", "@eq @0 True true true")),
    "(@eq @0 True true true)",
    "an @ alias explicitly written by the user must be preserved"
);
assert.equal(
    parser.stringify(compact(
        "@inveq @0 True true true (@refl @0 True true)",
        "exact @refl _ _ true"
    )),
    "(inveq (@refl _ True true))",
    "only explicitly written @ occurrences must survive nested presentation"
);

const compactMarkedSource = source => compactImplicitAliasesForDisplay(
    engine.core.desugar(markExplicitAtSyntax(parser.parse(source)), false),
    engine.core.opaque,
    collectExplicitAtNames(source)
);

assert.equal(
    parser.stringify(compactMarkedSource(
        "pair (@refl _ _ true) (refl true)"
    )),
    "(pair (@refl _ _ true) (refl true))",
    "an explicit @ occurrence must not force a same-name implicit occurrence to stay expanded"
);
assert.equal(
    parser.stringify(compactMarkedSource(
        "pair (refl true) (@refl _ _ true)"
    )),
    "(pair (refl true) (@refl _ _ true))",
    "occurrence-specific @ preservation must work in either order"
);

assert.equal(
    parser.stringify(compact("@0")),
    "_",
    "an automatically generated universe level must not leak its internal @ name"
);
assert.equal(
    parser.stringify(compactImplicitAliasesForDisplay(
        markExplicitAtSyntax(parser.parse("@0")),
        engine.core.opaque,
        collectExplicitAtNames("@0")
    )),
    "@0",
    "a universe level explicitly written by the user must be preserved"
);

console.log("proof-assistant elaboration display regression passed");
