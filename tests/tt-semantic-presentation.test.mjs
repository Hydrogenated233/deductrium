import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const session = new TTCoreSession();
session.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

const cases = [
    {
        source: "pairDisplay:=pair (λa:True,True) true true",
        display: "(pairDisplay := (pair (λa:True.True) true true))"
    },
    {
        source: "reflDisplay:=refl true",
        display: "(reflDisplay := (refl true))"
    },
    {
        source: "rflDisplay:=rfl:(true=true)",
        display: "(rflDisplay := (rfl : (true=true)))"
    },
    {
        source: "explicitDisplay:=@refl _ _ true",
        display: "(explicitDisplay := (@refl _ _ true))"
    },
    {
        source: "mixedOuterAlias:=refl (@refl _ _ true)",
        display: "(mixedOuterAlias := (refl (@refl _ _ true)))"
    },
    {
        source: "mixedOuterExplicit:=@refl _ _ (refl true)",
        display: "(mixedOuterExplicit := (@refl _ _ (refl true)))"
    }
];

for (const [index, testCase] of cases.entries()) {
    const result = session.validate(index, parser.parse(testCase.source));
    assert.equal(result.ok, true, result.error);
    assert.equal(parser.stringify(result.ast), testCase.display,
        "the displayed theorem must preserve the user's alias and @ syntax");
    const filled = parser.stringify(result.filledDefinition);
    assert.doesNotMatch(filled, /(^|[ (])_([ )]|$)/,
        "the stored definition must not retain unresolved input holes");
}

console.log("semantic elaboration presentation regression passed");
