import assert from "node:assert/strict";
import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

for (const source of [
    "completed := (0,rfl):(Sn:nat,n=n)",
    "completed := (0,refl 0):(Sn:nat,n=n)",
    "completed := (_,refl 0):(Sn:nat,n=n)",
    "completed := (0,rfl):(Sn:_,n=n)",
    "completed := (0,true):(Sn:_,True)",
    // K609 theorem 145 minimized: the pair also occurs in a binder type.
    "completed := Lb:U,Lc:U,Lf:True->b X c,Lq:Py:b,Pz:c,f true=(y,z),q"
]) {
    const session = new TTCoreSession();
    session.configure({
        unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
        inferDisplayMode: "_",
        timeout: 30_000,
        language: "zh"
    });
    const result = session.validate(0, parser.parse(source));
    assert.equal(result.ok, true, `${source}: ${result.error}`);
    assert.equal(result.inferenceComplete, true, `${source} must leave no motive holes`);
}

function check(source, context = []) {
    const ast = parser.parse(source);
    engine.core.checkType(ast, context, false, undefined, true);
    assert.doesNotMatch(JSON.stringify(ast), /\?nbe/);
    return ast.type === ":" ? ast.nodes[0] : ast;
}

const open = check("(?refine0,?refine1):(Sn:nat,n=n)");
assert.equal(open.type, ",");
assert.equal(open.nodes[0].name, "?refine0");
assert.equal(parser.stringify(open.nodes[0].checked), "nat");
assert.equal(open.nodes[1].name, "?refine1");
assert.equal(parser.stringify(open.nodes[1].checked), "(?refine0=?refine0)");

const inferred = check("(_,refl 0):(Sn:nat,n=n)");
assert.equal(inferred.type, ",");
assert.equal(inferred.nodes[0].name, "_");
assert.equal(inferred.nodes[0].checked.type, ":");
assert.equal(inferred.nodes[0].checked.nodes[0].name, "0");
assert.equal(parser.stringify(inferred.nodes[0].checked.nodes[1]), "nat");
assert.equal(parser.stringify(inferred.nodes[1].checked), "(0=0)");

const fixed = check("(0,?refine1):(Sn:nat,n=n)");
assert.equal(parser.stringify(fixed.nodes[1].checked), "(0=0)");

for (const source of [
    "(true,0):True X nat",
    "(pair (Ln:nat.n=n) 0 (refl 0)):(Sn:nat,n=n)"
]) check(source);

const nestedPair = check("((?refine0,?refine1),?refine2):(Sp:(Sn:nat,n=n),p=p)");
assert.equal(nestedPair.nodes[0].type, ",");
assert.equal(parser.stringify(nestedPair.nodes[0].nodes[0].checked), "nat");
assert.equal(parser.stringify(nestedPair.nodes[0].nodes[1].checked), "(?refine0=?refine0)");

const nested = check("f (?refine0,?refine1):True", [
    ["f", parser.parse("(Sn:nat,n=n)->True"), 0]
]).nodes[1];
assert.equal(nested.type, ",");
assert.equal(parser.stringify(nested.nodes[0].checked), "nat");
assert.equal(parser.stringify(nested.nodes[1].checked), "(?refine0=?refine0)");

const scoped = check("f (Ln:nat.(?refine0,?refine1)):True", [
    ["f", parser.parse("(Pn:nat,Sm:nat,m=n)->True"), 0]
]).nodes[1].nodes[1];
assert.equal(scoped.type, ",");
assert.equal(parser.stringify(scoped.nodes[0].checked), "nat");
assert.equal(parser.stringify(scoped.nodes[1].checked), "(?refine0=n)");

for (const source of [
    "(true,refl 0):(Sn:nat,n=n)",
    "(0,true):(Sn:nat,n=n)",
    "(0,refl 1):(Sn:nat,n=n)",
    "(pair (Ln:nat.True) 0 true):(Sn:nat,n=n)",
    "(pair (Ln:nat.True) _ true):(Sn:nat,n=n)",
    "(0,refl 0):nat"
]) {
    assert.throws(() => check(source), undefined, source);
}

const foreignTarget = engine.core.markBondVars(
    engine.core.desugar(parser.parse("(0,_):(Sn:nat,?foreign)"), true), []
);
assert.deepEqual(engine.core.semanticTypeChecker.tryCheck(
    foreignTarget.nodes[0], foreignTarget.nodes[1], [],
    { elaborateMetas: true, allowUnsolvedTermMetas: true }
), { status: "unsupported", code: "metavariable" },
"unregistered target metas must not become motive solutions");

console.log("target-directed semantic pair checking regression passed");
