import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";

const parser = new ASTParser();

// The strict entry point accepts the Unicode surface notation.
for (const source of [
    "λx:U.x",
    "Πx:U,x",
    "Σx:U,x",
    "A → B",
    "A × B",
    "W x:U,x"
]) {
    assert.doesNotThrow(() => parser.parseSurface(source), source);
}

// Reserved parser letters are still valid in user names.  The compact parser
// used to split these names as binders/operators; parseSurface must restore
// the exact name in every AST variable/binder.
for (const name of [
    "List", "LiftU", "Loop2", "LambdaThing", "Lfoo", "Pfoo", "Sfoo",
    "Xfoo", "P", "S", "X", "Wfoo", "Ufoo", "U_foo"
]) {
    const ast = parser.parseSurface(name);
    assert.equal(ast.type, "var", name);
    assert.equal(ast.name, name, name);
}
for (const source of ["Ufoo", "U_foo"]) {
    const ast = parser.parseSurface(source);
    assert.equal(ast.type, "var", source);
    assert.equal(ast.name, source, source);
}
assert.equal(parser.stringify(parser.parseSurface("Uu")), "(Uu)");
const uApplication = parser.parseSurface("Ubar(baz)");
assert.equal(uApplication.type, "apply");
assert.equal(uApplication.nodes[0].name, "Ubar");
assert.equal(parser.stringify(parser.parseSurface("SurfaceX(foo)")), "(SurfaceX foo)");
assert.equal(parser.stringify(parser.parseSurface("ind_SurfaceX(foo)")), "(ind_SurfaceX foo)");
assert.equal(parser.parseSurface("λList:U.List").name, "List");
assert.equal(parser.parseSurface("ΠLfoo:U,Lfoo").name, "Lfoo");
assert.equal(parser.parseSurface("ΣPfoo:U,Pfoo").name, "Pfoo");
assert.equal(parser.parseSurface("Ufoo").name, "Ufoo");
assert.equal(parser.parseSurface("U_foo").name, "U_foo");
assert.equal(parser.parseSurface("Ufoo : U").nodes[0].name, "Ufoo");
assert.equal(parser.parseSurface("U_foo : U").nodes[0].name, "U_foo");

// A user-defined name ending in X remains a name even when immediately
// applied to a parenthesized argument.  The legacy migration layer handles
// compact products, while the strict surface parser must not reject these
// modern applications as old `X` products.
for (const source of ["SurfaceX(foo)", "@SurfaceX(foo)"]) {
    assert.doesNotThrow(() => parser.parseSurface(source), source);
}

// Declaration names may begin with legacy marker letters. They are not
// binders unless the parser's body delimiter follows the parameter type.
for (const [source, expectedName] of [
    ["Pfoo : U", "Pfoo"],
    ["Lfoo : U", "Lfoo"],
    ["Sfoo : U", "Sfoo"],
    ["Xfoo : U", "Xfoo"],
    ["Pfoo := U", "Pfoo"]
]) {
    const declaration = parser.parseSurface(source);
    assert.ok(declaration.type === ":" || declaration.type === ":=", source);
    assert.equal(declaration.nodes[0].type, "var", source);
    assert.equal(declaration.nodes[0].name, expectedName, source);
}

// New user-facing input no longer accepts the old ASCII spelling.  The
// compatibility parse() method remains available for internal/migration use.
for (const source of [
    "Lx:U.x",
    "Px:U,x",
    "Sx:U,x",
    "A->B",
    "A~=B",
    "A===B",
    "A*B",
    "AXB",
    "A X B"
]) {
    assert.throws(
        () => parser.parseSurface(source),
        /不再支持旧语法/u,
        source
    );
    assert.doesNotThrow(() => parser.parse(source), `legacy parse: ${source}`);
}

console.log("strict surface parser regression passed");
