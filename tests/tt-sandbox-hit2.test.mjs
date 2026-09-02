import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import {
    SandboxEnvironment,
    creativeSandboxSystemRuleIds,
    lowerSandboxHit,
    parseSandboxHit
} from "../js/tt/sandbox.js";

const parser = new ASTParser();
const surfaceSource = "hit SurfaceX : U "
    + "| baseX : SurfaceX "
    + "| loopAX : baseX = baseX "
    + "| loopBX : baseX = baseX "
    + "| path2 squareX : loopAX = loopBX";

// Parsing must retain the distinction between point, first-path, and
// second-path constructors, including the path endpoints used by metadata.
const parsed = parseSandboxHit(surfaceSource);
assert.equal(parsed.name, "SurfaceX");
assert.deepEqual(parsed.pointConstructors.map(constructor => constructor.name), ["baseX"]);
assert.deepEqual(parsed.pathConstructors.map(path => path.name), ["loopAX", "loopBX"]);
assert.deepEqual(parsed.twoPathConstructors.map(path => path.name), ["squareX"]);
assert.equal(parsed.twoPathConstructors[0].left.name, "loopAX");
assert.equal(parsed.twoPathConstructors[0].right.name, "loopBX");
assert.equal(parsed.twoPathConstructors[0].leftPoint.name, "baseX");
assert.equal(parsed.twoPathConstructors[0].rightPoint.name, "baseX");

assert.throws(
    () => parseSandboxHit(
        "hit BadSquare : U | baseB : BadSquare "
            + "| loopB : baseB = baseB | path2 squareB : loopB"
    ),
    /二阶路径构造子.*必须以等式为结论/
);
assert.throws(
    () => parseSandboxHit(
        "hit BadSquare : U | path2 squareB : loopB = loopB "
            + "| loopB : BadSquare = BadSquare"
    ),
    /二阶路径构造子必须写在一阶路径构造子之后/
);
assert.throws(
    () => parseSandboxHit(
        "hit BadSquare : U | baseB : BadSquare "
            + "| loopB : baseB = baseB | path2 squareB : loopB = missingB"
    ),
    /端点必须由 BadSquare 的一阶路径构造子形成/
);
assert.throws(
    () => parseSandboxHit(
        "hit FutureHigher : U | baseF : FutureHigher "
            + "| loopF : baseF = baseF "
            + "| path2 faceF : loopF = loopF "
            + "| path3 cubeF : faceF = faceF "
            + "| path4 hyperF : cubeF = cubeF"
    ),
    /最高只解析三维 HIT.*path4/
);

const bundle = lowerSandboxHit(parsed);
assert.equal(bundle.metadata.version, 4);
assert.equal(bundle.metadata.kind, "hit2");
assert.equal(bundle.metadata.dimension, 2);
assert.equal(bundle.metadata.typeName, "SurfaceX");
assert.deepEqual(bundle.metadata.twoPathConstructors.map(path => ({
    name: path.name,
    leftPath: path.leftPath,
    rightPath: path.rightPath,
    computationName: path.computationName
})), [{
    name: "squareX",
    leftPath: "loopAX",
    rightPath: "loopBX",
    computationName: "apd_squareX"
}]);
assert.deepEqual(bundle.metadata.twoPathConstructors[0].argumentTypes, []);
assert.equal(bundle.metadata.twoPathConstructors[0].left.name, "loopAX");
assert.equal(bundle.metadata.twoPathConstructors[0].right.name, "loopBX");

// The second path is propositional. It must expose computation theorem
// slots, but must not be installed as an ordinary definitional rewrite head.
assert.equal(bundle.computeRules.squareX, undefined);
assert.equal(bundle.computeRules.apd_squareX, undefined);
assert.equal(bundle.computeRules.ap_squareX, undefined);
assert.equal(bundle.computeRules["@apd_squareX"], undefined);
assert.equal(bundle.computeRules["@ap_squareX"], undefined);
for (const name of [
    "squareX",
    "apd_squareX",
    "@apd_squareX",
    "ap_squareX",
    "@ap_squareX"
]) {
    assert.ok(bundle.auxiliaryTypes.some(([entryName]) => entryName === name),
        `二维 HIT must export ${name}`);
}

// Registration is the end-to-end acceptance check: it validates all generated
// slots through the same Core path used by the creative sandbox.
const sandbox = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const folder = sandbox.addFolder("surface");
const added = sandbox.addInFolder(surfaceSource, folder.id);
assert.equal(added.ok, true, added.error);
const declaration = added.declarations.find(item => item.name === "SurfaceX");
assert.ok(declaration);
assert.equal(declaration.status, "valid");
assert.equal(declaration.folderId, folder.id);
assert.ok(declaration.generatedNames.includes("squareX"));
assert.ok(sandbox.check("squareX : loopAX = loopBX").ok);
assert.ok(sandbox.check("apd_squareX").ok);
assert.ok(sandbox.check("@apd_squareX").ok);
assert.ok(sandbox.check("ap_squareX").ok);
assert.ok(sandbox.check("@ap_squareX").ok);

const bridge = sandbox.bridge();
assert.deepEqual(bridge.order, [{ kind: "inductive", name: "SurfaceX" }]);
assert.equal(bridge.inductives.length, 1);
assert.equal(bridge.inductives[0].metadata.kind, "hit2");
assert.equal(bridge.inductives[0].metadata.dimension, 2);
assert.equal(bridge.inductives[0].metadata.twoPathConstructors[0].name, "squareX");

// Save/load must preserve the declaration source, folder placement, and the
// regenerated two-dimensional metadata rather than silently downgrading it.
const encoded = JSON.parse(sandbox.serialize());
assert.equal(encoded.version, 1);
assert.deepEqual(encoded.order, [folder.id, declaration.id]);
assert.equal(encoded.folders[0].open, true);
assert.equal(encoded.declarations[0].folderId, folder.id);

const restored = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
restored.load(encoded);
const restoredDeclaration = restored.getDeclarations().find(item => item.name === "SurfaceX");
assert.ok(restoredDeclaration);
assert.equal(restoredDeclaration.status, "valid");
assert.equal(restoredDeclaration.folderId, folder.id);
assert.ok(restored.check("squareX : loopAX = loopBX").ok);
assert.equal(restored.bridge().inductives[0].metadata.kind, "hit2");
assert.equal(restored.bridge().inductives[0].metadata.dimension, 2);

// Uniform parameters must be threaded through generated path-computation
// theorems.  Before the regression fix, `C` was supplied where `A` was
// expected in `apd_loopAP`/`apd_loopBP`, so this otherwise valid parameterized
// HIT failed during registration at its `apd_squareP` type.
const parameterizedSource = "hit SurfaceP (A : U) : U "
    + "| baseP : SurfaceP A "
    + "| loopAP : Pz:A,baseP=baseP "
    + "| loopBP : Pz:A,baseP=baseP "
    + "| path2 squareP : Pz:A,loopAP z=loopBP z";
const parameterized = lowerSandboxHit(parseSandboxHit(parameterizedSource));
assert.equal(parameterized.metadata.parameterCount, 1);
assert.equal(parameterized.metadata.twoPathConstructors[0].name, "squareP");
const parameterizedSandbox = new SandboxEnvironment({
    systemRuleIds: creativeSandboxSystemRuleIds
});
const parameterizedAdded = parameterizedSandbox.add(parameterizedSource);
assert.equal(parameterizedAdded.ok, true, parameterizedAdded.error);
assert.ok(parameterizedSandbox.check("apd_squareP").ok);
assert.ok(parameterizedSandbox.check("@apd_squareP").ok);
assert.ok(parameterizedSandbox.check("ap_squareP").ok);
assert.ok(parameterizedSandbox.check("@ap_squareP").ok);

// A modern transparent declaration may consume the generated 2-path
// computation theorem.  This exercises application elaboration after the
// declaration has crossed the strict surface-input boundary, rather than
// checking only the bare theorem type.
const applicationSandbox = new SandboxEnvironment({
    systemRuleIds: creativeSandboxSystemRuleIds
});
assert.equal(applicationSandbox.add(surfaceSource).ok, true);
const application = applicationSandbox.add(
    "useApd2 := λC:SurfaceX→U."
    + "λc:(C baseX)."
    + "λp0:((trans C loopAX c)=c)."
    + "λp1:((trans C loopBX c)=c)."
    + "λp2:(p0=((trans2 C squareX c)▪p1))."
    + "apd_squareX C c p0 p1 p2"
);
assert.equal(application.ok, true, application.error);
assert.equal(application.declarations.at(-1).kind, "definition");
assert.equal(applicationSandbox.check("useApd2").ok, true);
assert.equal(applicationSandbox.check("Πx:SurfaceX,x=x").ok, true);
assert.equal(applicationSandbox.check("Px:SurfaceX,x=x").ok, true,
    "legacy replay syntax should still parse generated sandbox names");
const nondependentApplication = applicationSandbox.add(
    "useAp2 := λC:U."
    + "λr:C."
    + "λq0:(r=r)."
    + "λq1:(r=r)."
    + "λq2:(q0=q1)."
    + "ap_squareX C r q0 q1 q2"
);
assert.equal(nondependentApplication.ok, true, nondependentApplication.error);
assert.equal(applicationSandbox.check("useAp2").ok, true);

// The same generated theorem must retain uniform parameters when a HIT path
// has a local telescope.  This catches accidental argument reordering that a
// bare type check can miss.
const parameterizedApplication = parameterizedSandbox.add(
    "useApdP := λA:U."
    + "λC:(SurfaceP A→U)."
    + "λc:(C (baseP A))."
    + "λp0:(Πz:A,(trans C (loopAP A z) c)=c)."
    + "λp1:(Πz:A,(trans C (loopBP A z) c)=c)."
    + "λp2:(Πz:A,p0 z=((trans2 C (squareP A z) c)▪p1 z))."
    + "λz:A.apd_squareP A C c p0 p1 p2 z"
);
assert.equal(parameterizedApplication.ok, true, parameterizedApplication.error);
assert.equal(parameterizedSandbox.check("useApdP").ok, true);

console.log("sandbox second-order HIT regression passed");
