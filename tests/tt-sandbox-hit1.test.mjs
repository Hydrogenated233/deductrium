import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { initTypeSystem } from "../js/tt/initial.js";
import {
    SandboxEnvironment,
    creativeSandboxSystemRuleIds,
    lowerSandboxHit,
    parseSandboxDeclaration,
    parseSandboxHit
} from "../js/tt/sandbox.js";

const parser = new ASTParser();
const circleSource = "hit Circle2 : U | baseC : Circle2 | loopC : baseC = baseC";
const circle = parseSandboxHit(circleSource);
assert.equal(circle.name, "Circle2");
assert.deepEqual(circle.pointConstructors.map(ctor => ctor.name), ["baseC"]);
assert.deepEqual(circle.pathConstructors.map(ctor => ctor.name), ["loopC"]);
assert.equal(circle.pointConstructors[0].typeSource, "Circle2",
    "the parser's internal self placeholder must not leak into HIT display source");
assert.equal(parseSandboxDeclaration(circleSource).hit?.name, "Circle2");

assert.throws(
    () => parseSandboxHit("hit NoPath : U | pointN : NoPath"),
    /至少需要一个一阶路径构造子/
);
assert.throws(
    () => parseSandboxHit(
        "hit BadEndpoint : U | pointB : BadEndpoint | badPath : true = true"
    ),
    /路径端点.*点构造子|端点.*BadEndpoint/
);
assert.throws(
    () => parseSandboxHit(
        "hit BadOrder : U | pathFirst : pointLater = pointLater | pointLater : BadOrder"
    ),
    /点构造子必须写在路径构造子之前/
);
assert.throws(
    () => parseSandboxHit(
        "hit ShadowPoint : U | cShadow : ShadowPoint | loopShadow : PcShadow:True,cShadow=cShadow"
    ),
    /端点.*被局部参数遮蔽/
);

const internalPlaceholderSource = "hit _SandboxHitSelf : U "
    + "| pointSelf : _SandboxHitSelf | pathSelf : pointSelf = pointSelf";
const internalPlaceholder = parseSandboxHit(internalPlaceholderSource);
assert.equal(internalPlaceholder.name, "_SandboxHitSelf");
assert.equal(internalPlaceholder.pointConstructors[0].typeSource, "_SandboxHitSelf");
const internalPlaceholderSandbox = new SandboxEnvironment({
    systemRuleIds: creativeSandboxSystemRuleIds
});
const internalPlaceholderResult = internalPlaceholderSandbox.add(internalPlaceholderSource);
assert.equal(internalPlaceholderResult.ok, true, internalPlaceholderResult.error);

const reservedPrefixSource = "hit PrefixPoints : U "
    + "| Point : PrefixPoints | Left : PrefixPoints "
    + "| Xpoint : PrefixPoints | Spoint : PrefixPoints "
    + "| pathPL : Point = Left | pathXS : Xpoint = Spoint";
const reservedPrefix = parseSandboxHit(reservedPrefixSource);
assert.deepEqual(
    reservedPrefix.pointConstructors.map(constructor => constructor.name),
    ["Point", "Left", "Xpoint", "Spoint"]
);
const reservedPrefixSandbox = new SandboxEnvironment({
    systemRuleIds: creativeSandboxSystemRuleIds
});
const reservedPrefixResult = reservedPrefixSandbox.add(reservedPrefixSource);
assert.equal(reservedPrefixResult.ok, true, reservedPrefixResult.error);

const arrowCapture = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const arrowCaptureResult = arrowCapture.add(
    "hit ArrowCapture : U | pointArrow : True -> ArrowCapture "
    + "| loopArrow : True -> pointArrow x0 = pointArrow x0"
);
assert.equal(arrowCaptureResult.ok, false,
    "an anonymous arrow binder must not capture a free x0 in the path endpoint");
assert.match(arrowCaptureResult.error ?? "", /未知的沙盒名称：x0/);

const sandbox = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const result = sandbox.add(circleSource);
assert.equal(result.ok, true, result.error);
assert.equal(result.declarations[0].kind, "hit");
assert.equal(sandbox.check("baseC : Circle2").ok, true);
assert.equal(sandbox.check("loopC : baseC = baseC").ok, true);
assert.equal(sandbox.check(
    "ind_Circle2 (Lx:Circle2.True) true (transconst loopC true) baseC === true"
).ok, true, "point constructors must retain definitional iota computation");
assert.equal(sandbox.check(
    "apd_loopC (Lx:Circle2.True) true (transconst loopC true)"
).ok, true, "the path computation theorem must be available propositionally");
assert.equal(sandbox.check(
    "rec_Circle2 True true rfl baseC === true"
).ok, true, "the non-dependent recursor must compute on point constructors");
assert.equal(sandbox.check("ap_loopC True true rfl").ok, true);

const circleBundle = lowerSandboxHit(circle);
assert.equal(circleBundle.metadata.version, 3);
assert.equal(circleBundle.metadata.kind, "hit1");
assert.deepEqual(circleBundle.metadata.constructors.map(ctor => ctor.name), ["baseC"]);
assert.deepEqual(circleBundle.metadata.pathConstructors.map(ctor => ctor.name), ["loopC"]);
assert.equal(circleBundle.computeRules.loopC, undefined,
    "path constructors must never become definitional compute-rule heads");
assert.equal(circleBundle.computeRules.apd_loopC, undefined,
    "path computation must remain a proposition, not definitional equality");

const intervalSource = "hit Interval2 : U "
    + "| leftI : Interval2 "
    + "| rightI : Interval2 "
    + "| segI2 : leftI = rightI";
const intervalSandbox = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const intervalResult = intervalSandbox.add(intervalSource);
assert.equal(intervalResult.ok, true, intervalResult.error);
assert.equal(intervalSandbox.check("segI2 : leftI = rightI").ok, true);
assert.equal(intervalSandbox.check(
    "ind_Interval2 (Lx:Interval2.True) true true (transconst segI2 true) leftI === true"
).ok, true);
assert.equal(intervalSandbox.check(
    "ind_Interval2 (Lx:Interval2.True) true true (transconst segI2 true) rightI === true"
).ok, true);

const parameterizedSource = "hit Span2 (A : U) (B : U) (C : U) "
    + "(f : C -> A) (g : C -> B) : U "
    + "| inl2 : A -> Span2 A B C f g "
    + "| inr2 : B -> Span2 A B C f g "
    + "| glue2 : Px:C,inl2 (f x) = inr2 (g x)";
const parameterized = parseSandboxHit(parameterizedSource);
assert.equal(parameterized.pathConstructors[0].arguments[0].name, "x");
const parameterizedSandbox = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const parameterizedResult = parameterizedSandbox.add(parameterizedSource);
assert.equal(parameterizedResult.ok, true, parameterizedResult.error);
const parameterizedBundle = lowerSandboxHit(parameterized);
const glueType = parameterizedBundle.auxiliaryTypes
    .find(([name]) => name === "glue2")?.[1];
assert.ok(glueType, "the path constructor type must be exported by the HIT bundle");
assert.equal(
    parser.stringify(glueType),
    parser.stringify(parser.parse(
        "PA:U,PB:U,PC:U,Pf:C->A,Pg:C->B,Px:C,"
        + "inl2 A B C f g (f x) = inr2 A B C f g (g x)"
    )),
    "path endpoints must retain parameters and point-constructor arguments"
);
assert.equal(parameterizedSandbox.check(
    "PA:U,PB:U,PC:U,Pf:C->A,Pg:C->B,Px:C,"
    + "glue2 A B C f g x = glue2 A B C f g x"
).ok, true, "parameterized path constructors must be available to later declarations");
for (const rules of Object.values(parameterizedBundle.computeRules)) {
    for (const rule of rules) {
        const argumentOffset = rule.pattern[0].name.startsWith("@") ? 2 : 1;
        const parameterMetas = rule.pattern
            .slice(argumentOffset, argumentOffset + parameterized.parameters.length)
            .map(term => term.name);
        const coherenceMeta = rule.pattern[
            argumentOffset
            + parameterized.parameters.length
            + 1
            + parameterized.pointConstructors.length
        ]?.name;
        assert.equal(parameterMetas.includes(coherenceMeta), false,
            "HIT coherence holes must not alias uniform-parameter pattern variables");
    }
}

const captureSource = "hit Capture2 (A : U) : U "
    + "| pointCapture2 : A -> Capture2 A "
    + "| pathCapture2 : PC:A,Pp0:A,Pq0:A,Pc0:A,Pr0:A,Pu:A,"
    + "pointCapture2 C = pointCapture2 C";
const captureSandbox = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const captureResult = captureSandbox.add(captureSource);
assert.equal(captureResult.ok, true, captureResult.error);
assert.equal(captureSandbox.check(
    "PA:U,PC:A,Pp0:A,Pq0:A,Pc0:A,Pr0:A,Pu:A,"
    + "pathCapture2 A C p0 q0 c0 r0 u = pathCapture2 A C p0 q0 c0 r0 u"
).ok, true, "path-local names must not capture generated motive or branch binders");

const nestedCaptureSource = "hit NestedCapture (A : U) : U "
    + "| pointNested : U -> NestedCapture A "
    + "| pathNested : PC:U,Pz:(Ppath_C:U,C),pointNested C = pointNested C";
const nestedCapture = parseSandboxHit(nestedCaptureSource);
const nestedCaptureBundle = lowerSandboxHit(nestedCapture);
const nestedPathType = nestedCaptureBundle.auxiliaryTypes
    .find(([name]) => name === "pathNested")?.[1];
assert.ok(nestedPathType);
const nestedPathArgument = nestedPathType.nodes[1];
const nestedLaterArgument = nestedPathArgument.nodes[1];
assert.equal(nestedPathArgument.name, "path_C1",
    "a renamed path parameter must avoid binders already present in later argument types");
assert.equal(nestedLaterArgument.nodes[0].name, "path_C");
assert.equal(nestedLaterArgument.nodes[0].nodes[1].name, "path_C1",
    "later argument types must keep referring to the renamed outer path parameter");

const generatedNameCapture = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const generatedNameCaptureResult = generatedNameCapture.add(
    "hit GeneratedNameCapture : U | pointGenerated : True -> GeneratedNameCapture "
    + "| pathGenerated : Ptrans:True,pointGenerated trans = pointGenerated trans"
);
assert.equal(generatedNameCaptureResult.ok, true, generatedNameCaptureResult.error);

const uniformPathCollision = new SandboxEnvironment({
    systemRuleIds: creativeSandboxSystemRuleIds
});
const uniformPathCollisionResult = uniformPathCollision.add(
    "hit UniformPathCollision (pathUniform : U) : U "
    + "| pointUniform : UniformPathCollision pathUniform "
    + "| pathUniform : pointUniform = pointUniform"
);
assert.equal(uniformPathCollisionResult.ok, true, uniformPathCollisionResult.error);
assert.equal(uniformPathCollision.check(
    "PA:U,(pathUniform A = pathUniform A)"
).ok, true, "a uniform parameter may share the path constructor's global name");

const uniformGeneratedCollision = new SandboxEnvironment({
    systemRuleIds: creativeSandboxSystemRuleIds
});
const uniformGeneratedCollisionResult = uniformGeneratedCollision.add(
    "hit UniformGeneratedCollision "
    + "(ind_UniformGeneratedCollision : U) (rec_UniformGeneratedCollision : U) : U "
    + "| pointGeneratedCollision : UniformGeneratedCollision "
    + "ind_UniformGeneratedCollision rec_UniformGeneratedCollision "
    + "| loopGeneratedCollision : pointGeneratedCollision = pointGeneratedCollision"
);
assert.equal(
    uniformGeneratedCollisionResult.ok,
    true,
    uniformGeneratedCollisionResult.error
);

const assist = new TTAssistEngine();
assist.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    trustedInductives: [circleBundle],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});
const options = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};
let snapshot = assist.start("Circle2", options);
assert.equal(snapshot.tactics.includes("exact baseC"), true);
assert.equal(snapshot.tactics.some(tactic => tactic.includes("loopC")), false,
    "path constructors are not data constructors and must not be recommended by constructor");
snapshot = assist.apply("constructor");
assert.equal(snapshot.goals.length, 0);

snapshot = assist.start("Px:Circle2,x=x", options);
snapshot = assist.apply("intro x");
assert.equal(snapshot.tactics.includes("induction x"), true);
snapshot = assist.apply("induction x");
assert.equal(snapshot.goals.length, 2,
    "HIT induction must expose one point branch and one path-coherence branch");
assert.equal(snapshot.goals.some(goal => JSON.stringify(goal.type).includes("loopC")), true);

const restored = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
restored.load(sandbox.serialize());
assert.equal(restored.declarations[0].kind, "hit");
assert.equal(restored.check("loopC : baseC = baseC").ok, true);

const lifecycle = new SandboxEnvironment({ systemRuleIds: creativeSandboxSystemRuleIds });
const hitDeclaration = lifecycle.add(circleSource).declarations[0];
const dependentDeclaration = lifecycle.add("circlePoint : Circle2").declarations[1];
assert.equal(dependentDeclaration.status, "valid");
let lifecycleResult = lifecycle.setEnabled(hitDeclaration.id, false);
assert.equal(lifecycleResult.declarations[0].status, "disabled");
assert.equal(lifecycleResult.declarations[1].status, "invalid");
assert.equal(lifecycle.check("loopC").ok, false,
    "disabling a HIT must revoke its path constructor and generated rules");
lifecycleResult = lifecycle.setEnabled(hitDeclaration.id, true);
assert.equal(lifecycleResult.ok, true, lifecycleResult.error);
assert.equal(lifecycleResult.declarations[1].status, "valid");
assert.equal(lifecycle.check("apd_loopC").ok, true,
    "re-enabling a HIT must rebuild its propositional computation theorem");

console.log("sandbox first-order HIT regression passed");
