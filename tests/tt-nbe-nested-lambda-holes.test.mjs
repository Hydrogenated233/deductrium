import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const [codeNat] = readFileSync(
    new URL("./fixtures/code-nat.txt", import.meta.url),
    "utf8"
).split(/\r?\n/).map(line => line.trim()).filter(Boolean);

const session = new TTCoreSession();
session.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: Number.MAX_SAFE_INTEGER,
    language: "zh"
});

const fastPathHitsBefore = Core.semanticTypeCheckFastPathHits;
const result = session.validate(0, parser.parse(codeNat));
assert.equal(result.ok, true, result.error);
assert.ok(Core.semanticTypeCheckFastPathHits > fastPathHitsBefore,
    "nested expected lambdas must elaborate their domain/body holes bidirectionally");
assert.equal(result.definitionCache?.kind, "nbe");
assert.doesNotMatch(parser.stringify(result.filledDefinition), /(^|[ (])_([ )]|$)/,
    "the stored code_nat definition must not retain unresolved holes");

const additionalDefinitions = [
    "ftr:=ind_nat(λ_:_._)True(λ_:_.λa:_.True→a)",
    "ftreq:=ind_nat(λa:_.ftr a→_)(λa:_.a=true)(λa:_.λb:ftr a→_.λc:ftr(succ a).Πd:True,b (c d))",
    "invList:=λa:U.λb:List a.ind_List(λ_:_._)(λc:_.c)(λd:_.λ_:_.λe:_.λc:_.e(cons d c))b nil",
    "joinList:=λa:U.λp:List a.λq:List a.ind_List(λ_:_._)p(λy:_.λ_:_.(λx:_.ind_List(λ_:_._)(cons x nil)(λh:_.λ_:_.cons h))y)q"
];

for (const [offset, source] of additionalDefinitions.entries()) {
    const before = Core.semanticTypeCheckFastPathHits;
    const nested = session.validate(offset + 1, parser.parse(source));
    assert.equal(nested.ok, true, nested.error);
    assert.ok(Core.semanticTypeCheckFastPathHits > before,
        `${source.slice(0, source.indexOf(":="))} must use nested-lambda NbE elaboration`);
    assert.equal(nested.definitionCache?.kind, "nbe");
    assert.doesNotMatch(parser.stringify(nested.filledDefinition), /(^|[ (])_([ )]|$)/,
        "stored nested-lambda definitions must not retain unresolved holes");
}

console.log("nested-lambda semantic elaboration regression passed");
