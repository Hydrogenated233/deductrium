import assert from "node:assert/strict";
import {
    SandboxEnvironment,
    sandboxEnabledInMode,
    parseSandboxDeclaration,
    parseSandboxInductive,
    lowerSandboxInductive,
    creativeSandboxSystemRuleIds
} from "../js/tt/sandbox.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { ASTParser } from "../js/tt/astparser.js";

assert.equal(sandboxEnabledInMode("creative"), true);
assert.equal(sandboxEnabledInMode("survival"), false);

const nat2 = parseSandboxInductive("inductive Nat2 : U | zero2 : Nat2 | succ2 : Nat2 -> Nat2");
assert.equal(nat2.name, "Nat2");
assert.equal(nat2.universe, "U");
assert.deepEqual(nat2.parameters, []);
assert.deepEqual(nat2.constructors.map(ctor => ctor.name), ["zero2", "succ2"]);
assert.equal(nat2.constructors[0].arguments.length, 0);
assert.equal(nat2.constructors[1].arguments[0], "Nat2");
assert.deepEqual(nat2.constructors[1].argumentAsts[0].recursiveTelescope, []);
assert.equal(typeof nat2.constructors[1].argumentAsts[0].type, "object",
    "constructor argument types must be stored as ASTs, not split strings");
assert.throws(() => parseSandboxInductive("inductive Bad : U | mk : Box Bad -> Bad"), /嵌套递归/);
assert.throws(
    () => parseSandboxInductive("inductive BadNeg : U | mkNeg : (BadNeg -> nat) -> BadNeg"),
    /严格正/
);
assert.throws(
    () => parseSandboxInductive(
        "inductive BadParam (A : U) (B : U) : U | mkBad : BadParam B A"
    ),
    /索引归纳|返回参数/
);
assert.throws(
    () => parseSandboxInductive(
        "inductive RecursiveParameter (x : RecursiveParameter) : U "
        + "| mkRecursiveParameter : RecursiveParameter x"
    ),
    /参数.*不能递归引用/
);
assert.throws(() => parseSandboxInductive("inductive Empty : U"), /至少需要一个构造子/);

// Stage-2 v1 parameters are uniform, non-indexed binders. Constructor types
// remain structured ASTs, and recursive functions receive pointwise induction
// hypotheses instead of being rejected by the old string/arrow splitter.
const list2Signature = parseSandboxInductive(
    "inductive List2 (A : U) : U | nil2 : List2 A | cons2 : A -> List2 A -> List2 A"
);
assert.equal(list2Signature.parameters.length, 1);
assert.equal(list2Signature.parameters[0].name, "A");
assert.equal(list2Signature.parameters[0].typeSource, "U");
assert.deepEqual(
    list2Signature.constructors[1].argumentAsts.map(argument => [
        argument.typeSource,
        argument.recursiveTelescope?.length ?? null
    ]),
    [["A", null], ["(List2 A)", 0]]
);

const list2Sandbox = new SandboxEnvironment();
const list2Result = list2Sandbox.add(
    "inductive List2 (A : U) : U | nil2 : List2 A | cons2 : A -> List2 A -> List2 A"
);
assert.equal(list2Result.ok, true, list2Result.error);
assert.equal(list2Sandbox.check("nil2 True : List2 True").ok, true);
assert.equal(list2Sandbox.check("cons2 True true (nil2 True) : List2 True").ok, true);
assert.equal(
    list2Sandbox.check(
        "ind_List2 True (Lxs:List2 True.True) true "
        + "(Lx:True.Lxs:List2 True.Lih:True.true) "
        + "(cons2 True true (nil2 True)) === true"
    ).ok,
    true
);
assert.equal(
    list2Sandbox.check(
        "rec_List2 True (List2 True) (nil2 True) "
        + "(Lx:True.Lxs:List2 True.Lih:List2 True.cons2 True x ih) "
        + "(cons2 True true (nil2 True)) === cons2 True true (nil2 True)"
    ).ok,
    true
);

const functionRecursiveSandbox = new SandboxEnvironment({
    systemRuleIds: ["True", "False", "nat", "nat.ind"]
});
const functionRecursive = functionRecursiveSandbox.add(
    "inductive TreeF (A : U) : U "
    + "| leafF : A -> TreeF A "
    + "| nodeF : (nat -> TreeF A) -> TreeF A"
);
assert.equal(functionRecursive.ok, true, functionRecursive.error);
assert.equal(
    functionRecursiveSandbox.check(
        "ind_TreeF True (Lt:TreeF True.True) "
        + "(Lx:True.true) "
        + "(Lf:nat->TreeF True.Lih:Pn:nat.True.true) "
        + "(nodeF True (Ln:nat.leafF True true)) === true"
    ).ok,
    true,
    "a strictly-positive function argument must receive a pointwise induction hypothesis"
);

const universeParameterizedSandbox = new SandboxEnvironment();
const universeParameterized = universeParameterizedSandbox.add(
    "inductive BoxU (u : U@) (A : Uu) : Uu | boxU : A -> BoxU u A"
);
assert.equal(universeParameterized.ok, true, universeParameterized.error);
assert.equal(
    universeParameterizedSandbox.check("boxU @0 True true : BoxU @0 True").ok,
    true
);

// Stage-2 v1 lowers a three-way ordinary inductive, including the numeric
// constructor name, into a complete type/constructor/eliminator bundle.
const triSignature = parseSandboxInductive(
    "inductive tri : U | nt : tri | 0t : tri | pt : tri"
);
const triBundle = lowerSandboxInductive(triSignature);
assert.deepEqual(triBundle.generatedNames, [
    "tri", "nt", "0t", "pt", "ind_tri", "@ind_tri", "rec_tri", "@rec_tri"
]);
assert.equal(triBundle.auxiliaryTypes.some(([name]) => name === "@ind_tri"), true);
assert.equal(triBundle.auxiliaryTypes.some(([name]) => name === "@rec_tri"), true);
assert.equal(triBundle.computeRules.ind_tri.length, 3);
assert.equal(triBundle.computeRules.rec_tri.length, 3);
assert.equal(triBundle.metadata.recursorName, "rec_tri");

const triSandbox = new SandboxEnvironment();
const triResult = triSandbox.add(
    "inductive tri : U | nt : tri | 0t : tri | pt : tri"
);
assert.equal(triResult.ok, true, triResult.error);
assert.equal(triResult.declarations[0].status, "valid");
assert.equal(triSandbox.engine.core.getInductiveMetadata("tri").recursorName, "rec_tri");
assert.equal(triSandbox.check("nt:tri").ok, true);
for (const constructor of ["nt", "0t", "pt"]) {
    const result = triSandbox.check(
        `ind_tri (Lx:tri.True) true true true ${constructor} === true`
    );
    assert.equal(result.ok, true, `${constructor} iota: ${result.error}`);
}
for (const constructor of ["nt", "0t", "pt"]) {
    const result = triSandbox.check(
        `rec_tri tri nt 0t pt ${constructor} === ${constructor}`
    );
    assert.equal(result.ok, true, `${constructor} recursor iota: ${result.error}`);
}
assert.equal(
    triSandbox.check("@rec_tri @0 tri nt 0t pt 0t === 0t").ok,
    true,
    "the explicit universe-polymorphic recursor must use the same controlled iota rules"
);

// A recursive first-order constructor is accepted in the same slice and its
// induction hypothesis is reflected in the generated branch type/rule.
const nat2Sandbox = new SandboxEnvironment();
const nat2Result = nat2Sandbox.add(
    "inductive Nat2 : U | zero2 : Nat2 | succ2 : Nat2 -> Nat2"
);
assert.equal(nat2Result.ok, true, nat2Result.error);
assert.equal(nat2Sandbox.check("succ2 zero2:Nat2").ok, true);
assert.equal(
    nat2Sandbox.check(
        "ind_Nat2 (Lx:Nat2.True) true (Lx:Nat2.Lih:True.true) (succ2 zero2) === true"
    ).ok,
    true
);
assert.equal(
    nat2Sandbox.check(
        "rec_Nat2 Nat2 zero2 (Ln:Nat2.Lih:Nat2.succ2 ih) (succ2 (succ2 zero2)) === succ2 (succ2 zero2)"
    ).ok,
    true,
    "recursive recursor iota must pass the recursively computed result to its branch"
);

const recursorLifecycle = new SandboxEnvironment();
const recursorDeclaration = recursorLifecycle.add(
    "inductive OldRec : U | oldZero : OldRec | oldSucc : OldRec -> OldRec"
).declarations[0];
assert.equal(recursorLifecycle.check("rec_OldRec").ok, true);
assert.equal(recursorLifecycle.setEnabled(recursorDeclaration.id, false).ok, true);
for (const oldName of ["rec_OldRec", "@rec_OldRec"]) {
    assert.equal(recursorLifecycle.check(oldName).ok, false,
        `${oldName} must disappear when its declaration is disabled`);
}
assert.equal(recursorLifecycle.engine.core.state.computeRules.rec_OldRec, undefined);
assert.equal(recursorLifecycle.engine.core.state.computeRules["@rec_OldRec"], undefined);
assert.equal(recursorLifecycle.setEnabled(recursorDeclaration.id, true).ok, true);
assert.equal(recursorLifecycle.replace(
    "inductive NewRec : U | newOnly : NewRec",
    recursorDeclaration.id
).ok, true);
for (const oldName of ["OldRec", "rec_OldRec", "@rec_OldRec"]) {
    assert.equal(recursorLifecycle.check(oldName).ok, false,
        `${oldName} must remain absent after replacement`);
}
assert.equal(recursorLifecycle.engine.core.state.computeRules.rec_OldRec, undefined);
assert.equal(recursorLifecycle.engine.core.state.computeRules["@rec_OldRec"], undefined);
assert.equal(recursorLifecycle.check("rec_NewRec True true newOnly === true").ok, true,
    "replacement must install only the new recursor and its iota rules");

// A user-defined inductive type can provide the names used by a transparent
// definition.  This mirrors the UI example and guards the `:=` declaration
// path independently from the lowercase built-in `nat` prelude.
const namedNatSandbox = new SandboxEnvironment();
assert.equal(
    namedNatSandbox.add("inductive Nat : U | zeroN : Nat | succn : Nat -> Nat").ok,
    true
);
const namedNatDefinition = namedNatSandbox.add(
    "addn := Ly:Nat.ind_Nat (Lx:Nat.Nat) y (Lx:Nat.Lz:Nat.succn z)"
);
assert.equal(namedNatDefinition.ok, true, namedNatDefinition.error);
assert.equal(namedNatDefinition.declarations.at(-1).kind, "definition");
assert.equal(namedNatSandbox.bridge().definitions.some(([name]) => name === "addn"), true);

// Generated names participate in ordinary sandbox conflict detection; a
// constructor cannot silently shadow a prior inductive type or constructor.
const generatedConflict = new SandboxEnvironment();
generatedConflict.add("tri : U");
const conflictResult = generatedConflict.add("inductive Other : U | tri : Other");
assert.equal(conflictResult.ok, false);
assert.match(conflictResult.declarations[1].error, /名称冲突/);
assert.equal(generatedConflict.bridge().inductives.length, 0);

const sandbox = new SandboxEnvironment();
let result = sandbox.add("A : U");
assert.equal(result.ok, true);
result = sandbox.add("base : A");
assert.equal(result.ok, true);
result = sandbox.add("loop : base = base");
assert.equal(result.ok, true);
assert.deepEqual(sandbox.declarations.map(item => [item.name, item.kind, item.status]), [
    ["A", "type", "valid"],
    ["base", "term", "valid"],
    ["loop", "proposition", "valid"]
]);

// A trusted declaration may only enter the bridge when its RHS is itself a
// type. Synthesizing an arbitrary term is insufficient: `base` and `true`
// have types, but neither of those types is a Universe. An unconstrained hole
// must also remain invalid instead of becoming a trusted schematic axiom.
const typeFormation = new SandboxEnvironment();
assert.equal(typeFormation.add("A : U").ok, true);
assert.equal(typeFormation.add("base : A").ok, true);
assert.equal(typeFormation.add("endo : A -> A").ok, true);
assert.equal(typeFormation.add("family : Pz:U,z").ok, true);
assert.equal(typeFormation.add("resolved : @eq _ True true true").ok, true);
for (const source of ["Bad : base", "badSort : true", "holeType : _"]) {
    const invalid = typeFormation.add(source);
    assert.equal(invalid.declarations.at(-1).status, "invalid", source);
    assert.match(
        invalid.declarations.at(-1).error,
        /Universe|未确定的占位符|unresolved placeholders/,
        source
    );
}
assert.deepEqual(
    typeFormation.bridge().axioms.map(([name]) => name),
    ["A", "base", "endo", "family", "resolved"],
    "non-types and unresolved metavariables must never cross the trusted bridge"
);
assert.equal(
    JSON.stringify(typeFormation.bridge().axioms.at(-1)[1]).includes("?"),
    false,
    "resolved declaration holes must be elaborated before crossing the bridge"
);

const checked = sandbox.check("base = base");
assert.equal(checked.ok, true);

result = sandbox.add("bad : Missing");
assert.equal(result.ok, false);
assert.match(result.declarations.at(-1).error, /未知的沙盒名称/);

const forward = new SandboxEnvironment();
result = forward.add("base : A");
assert.equal(result.ok, false);
assert.match(result.declarations[0].error, /未知的沙盒名称/);
forward.add("A : U");
assert.match(forward.declarations[0].error, /禁止前向引用/);
assert.equal(forward.declarations[0].status, "invalid");

const numericName = new SandboxEnvironment();
assert.equal(numericName.add("tri : U").ok, true);
assert.equal(numericName.add("0t : tri").ok, true);
assert.equal(numericName.declarations[1].name, "0t");

const duplicate = new SandboxEnvironment();
duplicate.add("A : U");
result = duplicate.add("A : U");
assert.equal(result.ok, false);
assert.match(result.declarations[1].error, /名称冲突/);

const disabled = new SandboxEnvironment();
disabled.add("A : U");
disabled.add("base : A");
result = disabled.setEnabled("sandbox-1", false);
assert.equal(result.declarations[0].status, "disabled");
assert.equal(result.declarations[1].status, "invalid");

const foldered = new SandboxEnvironment();
const folder = foldered.addFolder("Basics");
foldered.add("A : U");
foldered.setFolder("sandbox-1", folder.id);
assert.equal(foldered.declarations[0].folderId, folder.id);
foldered.setFolderOpen(folder.id, false);
assert.equal(foldered.folders[0].open, false);
foldered.setFolderDisabled(folder.id, true);
assert.equal(foldered.declarations[0].status, "disabled");

const roundTrip = new SandboxEnvironment();
roundTrip.load(sandbox.serialize());
assert.deepEqual(roundTrip.getDeclarations().map(item => [item.name, item.status]),
    sandbox.getDeclarations().map(item => [item.name, item.status]));

// The browser worker reuses one environment and calls load for every change.
// A declaration must be reusable after disable/enable without stale-core
// duplicate-name errors.
const reloadable = new SandboxEnvironment();
reloadable.add("A : U");
reloadable.setEnabled("sandbox-1", false);
const reloaded = reloadable.toJSON();
reloaded.declarations[0].enabled = true;
const reenabled = reloadable.load(reloaded);
assert.equal(reenabled.ok, true);
assert.equal(reenabled.declarations[0].status, "valid");

const ordinary = new TTCoreEngine();
ordinary.configure({ unlockedTypes: ["True", "False"] });
assert.equal(ordinary.core.hasConst("A"), false);
assert.equal(ordinary.core.hasConst("base"), false);

// Creative mode is the only bridge into the type layer. Trusted declarations
// remain body-less system constants and are not copied into user definitions.
const bridgeParser = new ASTParser();
const bridged = new TTCoreEngine();
bridged.configure({
    unlockedTypes: ["True", "False"],
    trustedAxioms: [
        ["tri", bridgeParser.parse("U")],
        ["0t", bridgeParser.parse("tri")],
        ["loop", bridgeParser.parse("0t = 0t")]
    ]
});
assert.equal(bridged.core.hasConst("tri"), true);
assert.equal(bridged.core.hasConst("0t"), true);
assert.equal(bridged.core.hasConst("loop"), true);
assert.equal(bridged.check("loop").ok, true);
assert.equal(Object.keys(bridged.core.state.userDefs ?? {}).includes("tri"), false);

// Transparent sandbox definitions use `:=` and are checked as ordinary
// terms before entering the creative type-layer bridge.  An optional type
// ascription is accepted, while the bridge keeps the body separate from
// trusted body-less axioms.
const parsedDefinition = parseSandboxDeclaration("id := (Lx:A.x) : A->A");
assert.equal(parsedDefinition.name, "id");
assert.ok(parsedDefinition.definitionAst);
assert.ok(parsedDefinition.typeAst);

// Declarations copied from rendered rows may carry NBSP/zero-width spacing
// around the assignment operator.  Sandbox normalization should accept the
// same transparent definition and persist a clean, deterministic source.
const clipboardDefinition = parseSandboxDeclaration(
    "\uFEFFaddn\u00A0\u200B:=\u00A0Lx:nat.succ x"
);
assert.equal(clipboardDefinition.name, "addn");
assert.ok(clipboardDefinition.definitionAst);
const clipboardSandbox = new SandboxEnvironment({
    systemRuleIds: ["True", "False", "nat", "nat.ind"]
});
const clipboardResult = clipboardSandbox.add(
    "\uFEFFaddn\u00A0\u200B:=\u00A0Lx:nat.succ x"
);
assert.equal(clipboardResult.ok, true, clipboardResult.error);
assert.equal(clipboardResult.declarations.at(-1).source, "addn := Lx:nat.succ x");
assert.equal(clipboardSandbox.check("addn 0 === succ 0").ok, true);

const definitionSandbox = new SandboxEnvironment();
assert.equal(definitionSandbox.add("A : U").ok, true);
assert.equal(definitionSandbox.add("a : A").ok, true);
let definitionResult = definitionSandbox.add("id := Lx:A.x");
assert.equal(definitionResult.ok, true, definitionResult.error);
assert.equal(definitionSandbox.check("id a === a").ok, true);
assert.equal(definitionSandbox.bridge().definitions.length, 1);
assert.equal(definitionSandbox.bridge().axioms.some(([name]) => name === "id"), false);

const typedDefinitionSandbox = new SandboxEnvironment();
typedDefinitionSandbox.add("A : U");
typedDefinitionSandbox.add("a : A");
definitionResult = typedDefinitionSandbox.add("id := (Lx:A.x) : A->A");
assert.equal(definitionResult.ok, true, definitionResult.error);

// A failed definition must not leave a stale system definition that can leak
// into a later bridge or make the same name appear defined unexpectedly.
const failedDefinitionSandbox = new SandboxEnvironment();
failedDefinitionSandbox.add("A : U");
definitionResult = failedDefinitionSandbox.add("bad := (Lx:A.x) : A");
assert.equal(definitionResult.ok, false);
assert.equal(failedDefinitionSandbox.bridge().definitions.length, 0);
failedDefinitionSandbox.remove("sandbox-2");
assert.equal(failedDefinitionSandbox.add("bad : U").ok, true);

// The type-layer engine installs transparent bridge definitions in order and
// can use them in subsequent checks without copying them into userDefs.
const definitionBridge = definitionSandbox.bridge();
const definitionEngine = new TTCoreEngine();
definitionEngine.configure({
    unlockedTypes: ["True", "False"],
    trustedAxioms: definitionBridge.axioms,
    trustedInductives: definitionBridge.inductives,
    trustedDefinitions: definitionBridge.definitions
});
assert.equal(definitionEngine.core.hasConst("id"), true);
assert.equal(definitionEngine.check("id a === a").ok, true);
assert.equal(Object.keys(definitionEngine.core.state.userDefs ?? {}).includes("id"), false);

// The creative UI supplies the current system prelude to the sandbox. A
// transparent definition can therefore use ordinary built-ins directly,
// while the standalone default remains isolated for small experiments.
const builtinSandbox = new SandboxEnvironment({
    systemRuleIds: ["True", "False", "nat", "nat.ind"]
});
const builtinDefinition = builtinSandbox.add("inc := Lx:nat.succ x");
assert.equal(builtinDefinition.ok, true, builtinDefinition.error);
assert.equal(builtinSandbox.check("inc 0 === succ 0").ok, true);
assert.equal(builtinSandbox.bridge().definitions.some(([name]) => name === "inc"), true);

// A transparent definition may use the built-in natural-number eliminator
// directly.  Keep the scrutinee argument in the source: an under-applied
// `ind_nat` term is a function, not a natural number, and must not be treated
// as a failed reduction.  Check both the sandbox engine and its type-layer
// bridge so the explicit @ind_nat elaboration survives the hand-off.
const builtinRecursiveDefinition = builtinSandbox.add(
    "addn := Ly:nat.ind_nat (Lx:nat.nat) 0 (Lx:nat.Lz:nat.succ z) y"
);
assert.equal(builtinRecursiveDefinition.ok, true, builtinRecursiveDefinition.error);
assert.equal(builtinSandbox.check("addn 0 === 0").ok, true);
assert.equal(builtinSandbox.check("addn (succ 0) === succ 0").ok, true);
const builtinBridge = builtinSandbox.bridge();
const builtinBridgeEngine = new TTCoreEngine();
builtinBridgeEngine.configure({
    unlockedTypes: creativeSandboxSystemRuleIds,
    trustedAxioms: builtinBridge.axioms,
    trustedInductives: builtinBridge.inductives,
    trustedDefinitions: builtinBridge.definitions
});
assert.equal(builtinBridgeEngine.check("addn 0 === 0").ok, true);
assert.equal(builtinBridgeEngine.check("addn (succ 0) === succ 0").ok, true);

// The exported creative prelude mirrors the type-layer rule table and is
// available to non-DOM callers that want the same built-in visibility.
assert.equal(creativeSandboxSystemRuleIds.includes("nat"), true);
assert.equal(creativeSandboxSystemRuleIds.includes("nat.ind"), true);

// Self-reference is rejected explicitly before registration.  The parser's
// hole handling remains covered by the ordinary type-layer tests; a bare
// lambda domain is intentionally not accepted by the current kernel.
const recursiveSandbox = new SandboxEnvironment();
const recursiveDefinition = recursiveSandbox.add("loop := loop");
assert.equal(recursiveDefinition.ok, false);
assert.match(recursiveDefinition.declarations.at(-1).error, /递归|未知/);

console.log("type-theory sandbox stage-1 regression passed");
