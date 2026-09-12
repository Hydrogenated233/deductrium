import assert from "node:assert/strict";
import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";

const parser = new ASTParser();
const core = new Core();
core.state.userDefs.d = parser.parseSurface("Bool");
core.state.sysDefs.eqv = parser.parseSurface("eqvBody");

function expand(source, position, expected, occurrences, name = "d", context = []) {
    const ast = parser.parseSurface(source);
    const count = [position, 1];
    const changed = core.expandDef(ast, context, name, count);
    assert.equal(parser.stringify(ast), parser.stringify(parser.parseSurface(expected)),
        `${source}, occurrence ${position}`);
    assert.equal(changed, source !== expected);
    assert.equal(count[1], occurrences + 1, "count only eligible original occurrences");
    return ast;
}

// Both truncation surface nodes are unary, including when nested or unmatched.
for (const source of ["[[d]]", "[d]", "[[[d]]]"]) {
    for (const position of [0, 1, -1]) {
        expand(source, position, source.replace("d", "Bool"), 1);
    }
    for (const position of [2, -2]) expand(source, position, source, 1);
    expand(source.replace("d", "Bool"), 0, source.replace("d", "Bool"), 0);
}
for (const [position, expected] of [
    [0, "[[Bool]]→([Bool],Bool)"],
    [1, "[[Bool]]→([d],d)"],
    [2, "[[d]]→([Bool],d)"],
    [3, "[[d]]→([d],Bool)"],
    [-1, "[[d]]→([d],Bool)"],
    [-2, "[[d]]→([Bool],d)"],
    [-3, "[[Bool]]→([d],d)"],
    [4, "[[d]]→([d],d)"],
    [-4, "[[d]]→([d],d)"]
]) expand("[[d]]→([d],d)", position, expected, 3);

// Binder domains use the outer scope in both directions; only bodies shadow d.
for (const [prefix, separator] of [["Π", ","], ["λ", "."], ["Σ", ","], ["W ", ","]]) {
    const source = `${prefix}d:d${separator}[[d]]`;
    const expected = `${prefix}d:Bool${separator}[[d]]`;
    for (const position of [0, 1, -1]) {
        expand(source, position, expected, 1);
        const bound = core.markBondVars(parser.parseSurface(source), []);
        const bodyId = bound.nodes[1].nodes[0].bondVarId;
        assert.ok(bodyId > 0);
        assert.equal(core.expandDef(bound, [], "d", [position, 1]), true);
        assert.equal(parser.stringify(bound), parser.stringify(parser.parseSurface(expected)));
        assert.equal(bound.nodes[1].nodes[0].bondVarId, bodyId);
    }
    expand(source, -2, source, 1);
    expand(source, -1, source, 0, "d", [["d", parser.parseSurface("U"), 0]]);
}
for (const position of [0, 1, -1]) {
    expand("Πd:d,Πd:d,[[d]]", position, "Πd:Bool,Πd:d,[[d]]", 1);
}
expand("[[d]]", -1, "[[d]]", 0, "d", [["d", parser.parseSurface("U"), 0]]);
const markedLocal = parser.parseSurface("[d]");
markedLocal.nodes[0].bondVarId = 100;
assert.equal(core.expandDef(markedLocal, [], "d"), false);

// Selection must traverse the original equivalence arguments, whether the
// parent was selected or skipped, and must not revisit the inserted body.
const equivalences = "(a≃b)≃(c≃e)";
for (const [position, expected] of [
    [0, "eqvBody (eqvBody a b) (eqvBody c e)"],
    [1, "eqvBody (a≃b) (c≃e)"],
    [-1, "eqvBody (a≃b) (c≃e)"],
    [2, "(eqvBody a b)≃(c≃e)"],
    [-2, "(a≃b)≃(eqvBody c e)"],
    [3, "(a≃b)≃(eqvBody c e)"],
    [-3, "(eqvBody a b)≃(c≃e)"],
    [4, equivalences],
    [-4, equivalences]
]) expand(equivalences, position, expected, 3, "eqv");
expand("Bool≃Bool", 2, "Bool≃Bool", 1, "eqv");
expand("Bool≃Bool", -2, "Bool≃Bool", 1, "eqv");
expand("[[d]]≃[d]", 0, "eqvBody [[Bool]] [Bool]", 3, new Set(["d", "eqv"]));
expand("[[d]]≃[d]", -2, "[[d]]≃[Bool]", 3, new Set(["d", "eqv"]));
core.state.sysDefs.eqv = parser.parseSurface("d");
expand("a≃b", 0, "d a b", 1, new Set(["d", "eqv"]));

console.log("GitHub issue #54 unary expansion, binder scope and occurrence traversal passed");
