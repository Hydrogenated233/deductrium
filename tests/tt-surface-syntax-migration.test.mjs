import assert from "node:assert/strict";

import {
   hasLegacySurfaceSyntax,
    hasModernSurfaceSyntax,
   migrateLegacyDeclarationSource,
    migrateLegacyProofCommand,
    migrateLegacyProofHistory,
    migrateLegacyProofScript,
    migrateLegacySurfaceExpression
} from "../js/tt/surface-syntax-migration.js";

// Binders are converted without normalising the user's whitespace.
assert.equal(
    migrateLegacySurfaceExpression("Lx:T.x"),
    "λx:T.x"
);
assert.equal(
   migrateLegacySurfaceExpression("Pa:U,Pb:U,(aXb)->a"),
    "Πa:U,Πb:U,(a×b)→a"
);
assert.equal(
    migrateLegacySurfaceExpression("Sx:nat,eq x 1"),
    "Σx:nat,eq x 1"
);
assert.equal(
    migrateLegacySurfaceExpression("L x : T . x"),
    "λ x : T . x"
);
assert.equal(
    migrateLegacySurfaceExpression("L x : T , x"),
    "λ x : T , x"
);
assert.equal(migrateLegacySurfaceExpression("a->b"), "a→b");
assert.equal(migrateLegacySurfaceExpression("a~=b"), "a≃b");
assert.equal(migrateLegacySurfaceExpression("a===b"), "a≡b");
assert.equal(migrateLegacySurfaceExpression("p*q"), "p▪q");
// Backslash aliases saved before the editor's Space handler are migrated too.
assert.equal(migrateLegacySurfaceExpression("\\lambda x:U.x"), "λ x:U.x");
assert.equal(migrateLegacySurfaceExpression("\\p x:U,x"), "Π x:U,x");
assert.equal(migrateLegacySurfaceExpression("f \\s x:U,x"), "f Σ x:U,x");
assert.equal(migrateLegacySurfaceExpression("a \\x b"), "a × b");
// A draft can be saved before the Space-triggered keyboard alias expands;
// migrate the one-character alias as a unit instead of leaving `\\▪`.
assert.equal(migrateLegacySurfaceExpression("\\*"), "▪");
assert.equal(migrateLegacySurfaceExpression("f \\* g"), "f ▪ g");
// Long marker-prefixed identifiers are ambiguous in a bare expression and
// must remain names.  The explicit migration option is reserved for legacy
// save/history fields that intentionally use that compact binder spelling.
assert.equal(migrateLegacySurfaceExpression("Pfoo:U,x"), "Pfoo:U,x");
assert.equal(migrateLegacySurfaceExpression("Lambdax:U.x"), "Lambdax:U.x");
assert.equal(
    migrateLegacySurfaceExpression("Pfoo:U,x", { allowLongBinders: true }),
    "Πfoo:U,x"
);
// An escaped backslash is not the alias itself.  The following star remains
// subject to the ordinary legacy-operator migration.
assert.equal(migrateLegacySurfaceExpression("\\\\*"), "\\\\▪");

// Both separated and compact X forms were tokenised as products by the
// legacy parser, so all valid term-adjacent forms are migrated.
assert.equal(migrateLegacySurfaceExpression("A X B"), "A × B");
assert.equal(migrateLegacySurfaceExpression("A X(B)"), "A ×(B)");
assert.equal(migrateLegacySurfaceExpression("(A)XB"), "(A)×B");
assert.equal(migrateLegacySurfaceExpression("aXb"), "a×b");
assert.equal(migrateLegacySurfaceExpression("natXnat"), "nat×nat");
assert.equal(migrateLegacySurfaceExpression("FalseXFalse"), "False×False");
assert.equal(migrateLegacySurfaceExpression("aXbXc"), "a×b×c");
assert.equal(migrateLegacySurfaceExpression("(aXb)"), "(a×b)");
// `X` is also legal inside a user identifier.  Save migration must not turn
// names/applications into products merely because a parenthesis follows.
for (const source of [
    "SurfaceX(foo)",
    "@SurfaceX(foo)",
    "fooXbar",
    "myXname"
]) {
    assert.equal(
        migrateLegacySurfaceExpression(source),
        source,
        `${source} must remain a user identifier/application`
    );
}
// The unambiguous compact forms remain supported, including a parenthesized
// right operand when the left operand is a one-character legacy term.
assert.equal(migrateLegacySurfaceExpression("aX(b)"), "a×(b)");
assert.equal(migrateLegacySurfaceExpression("A X B"), "A × B");
assert.equal(migrateLegacySurfaceExpression("(A)XB"), "(A)×B");
// Names ending in X must remain names when an application follows.  Sandbox
// HITs commonly generate names such as SurfaceX; treating the suffix as the
// legacy product operator corrupts the name during save migration.
assert.equal(migrateLegacySurfaceExpression("SurfaceX (foo)"), "SurfaceX (foo)");
assert.equal(migrateLegacySurfaceExpression("ind_SurfaceX (foo)"), "ind_SurfaceX (foo)");
assert.equal(migrateLegacySurfaceExpression("SurfaceX(foo)"), "SurfaceX(foo)");
assert.equal(migrateLegacySurfaceExpression("ind_SurfaceX(foo)"), "ind_SurfaceX(foo)");
assert.equal(migrateLegacySurfaceExpression("Xfoo"), "Xfoo");

// Names and already-modern syntax are stable and migration is idempotent.
for (const source of [
    "List", "LiftU", "Loop2", "Pushout", "Wedge", "South", "Sus", "Sum",
    "S1", "S2", "S3", "S4", "LEM", "L", "P", "S", "X", "L:U", "P:U"
]) {
    assert.equal(migrateLegacySurfaceExpression(source), source, source);
}
for (const source of [
    "λx:T.x", "Πx:U,x", "Σx:nat,eq x 1", "A × B", "A×(B)"
]) {
    assert.equal(migrateLegacySurfaceExpression(source), source, source);
}

const legacy = "Pa:U,Pb:U,(aXb)->(bXa)";
const migrated = migrateLegacySurfaceExpression(legacy);
assert.equal(migrateLegacySurfaceExpression(migrated), migrated);
assert.equal(hasLegacySurfaceSyntax(legacy), true);
assert.equal(hasLegacySurfaceSyntax(migrated), false);
assert.equal(hasLegacySurfaceSyntax("List"), false);
assert.equal(hasModernSurfaceSyntax(migrated), true);
assert.equal(hasModernSurfaceSyntax("List"), false);

// Declaration names/separators are not rewritten; only the declaration body
// is migrated.
assert.equal(
    migrateLegacyDeclarationSource("List:=Lx:U.x"),
    "List:=λx:U.x"
);
assert.equal(
    migrateLegacyDeclarationSource("commaLambda:=Lx:U,x"),
    "commaLambda:=λx:U,x"
);
assert.equal(
    migrateLegacyDeclarationSource("xXy:=aXb"),
    "xXy:=a×b"
);
assert.equal(
    migrateLegacyDeclarationSource("myType : Px:U,U"),
    "myType : Πx:U,U"
);
assert.equal(
    migrateLegacyDeclarationSource("def:=(Lx:U.x):Pa:U,U"),
    "def:=(λx:U.x):Πa:U,U"
);

// Proof command names, rule names, and user names remain byte-for-byte; only
// expression arguments are migrated.
assert.equal(migrateLegacyProofCommand("exact Lx:T.x"), "exact λx:T.x");
assert.equal(migrateLegacyProofCommand("exact aXb->c"), "exact a×b→c");
assert.equal(migrateLegacyProofCommand("exact p*q"), "exact p▪q");
assert.equal(migrateLegacyProofCommand("  apply f List"), "  apply f List");
assert.equal(migrateLegacyProofCommand("qed legacyName"), "qed legacyName");
assert.equal(migrateLegacyProofCommand(".Vcn $0=$1 Lx:T.x"), ".Vcn $0=$1 λx:T.x");

const history = Object.freeze([
    "intro x .",
    "exact Lx:T.x",
    "qed legacyName"
]);
const migratedHistory = migrateLegacyProofHistory(history);
assert.deepEqual(migratedHistory, [
    "intro x .",
    "exact λx:T.x",
    "qed legacyName"
]);
assert.deepEqual(history, [
    "intro x .",
    "exact Lx:T.x",
    "qed legacyName"
]);

const script = "intro x .\r\nexact Lx:T.x\nqed legacyName";
assert.equal(
    migrateLegacyProofScript(script),
    "intro x .\r\nexact λx:T.x\nqed legacyName"
);

// Quoted/comment text is not source syntax.
assert.equal(
   migrateLegacySurfaceExpression('\"Lx:T.x\" // Px:U,U\n Lx:T.x'),
   '\"Lx:T.x\" // Px:U,U\n λx:T.x'
);
assert.equal(
    migrateLegacySurfaceExpression('\"a->b ~= c === d * e X f\" /* Lx:T.x */ a->b'),
    '\"a->b ~= c === d * e X f\" /* Lx:T.x */ a→b'
);

console.log("surface syntax migration regression passed");
