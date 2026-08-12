import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const session = new TTCoreSession();
session.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    disableSimpleFn: false,
    disableSimpleEq: false,
    inferDisplayMode: "_",
    timeout: Number.MAX_SAFE_INTEGER,
    language: "zh"
});

const trueOnly = session.validate(0, parser.parse(
    "trueonlyc:=Lx:True,ind_True (Lz:True,eq z true) (refl true) x"
));
assert.equal(trueOnly.ok, true, trueOnly.error);

const source = "mini:=(La:U,Lt:True,Lh:((inr t)=(inr true))->False,"
    + "ind_False (Lq:False,a) (h (ap inr (trueonlyc t)))):"
    + "(Pa:U,Pt:True,(((@inr @0 @0 a True t)=(@inr @0 @0 a True true))->False)->a)";
const fastPathHitsBefore = Core.semanticTypeCheckFastPathHits;
const result = session.validate(1, parser.parse(source));

assert.equal(result.ok, true, result.error);
assert.ok(Core.semanticTypeCheckFastPathHits > fastPathHitsBefore,
    "elaboration must compact unresolved registered alias prefixes before rejecting the term");
assert.equal(result.definitionCache?.kind, "nbe",
    "compacting hidden alias parameters must retain a native semantic cache");
assert.doesNotMatch(parser.stringify(result.filledDefinition), /\?nbe|\b_\b/,
    "the stored definition must not retain semantic elaboration metas");

console.log("semantic elaborated-term compaction regression passed");
