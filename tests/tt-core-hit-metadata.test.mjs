import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import {
    creativeSandboxSystemRuleIds,
    lowerSandboxHit,
    parseSandboxHit
} from "../js/tt/sandbox.js";

const parser = new ASTParser();
const parse = source => parser.parse(source);
const createEngine = () => {
    const instance = new TTCoreEngine();
    instance.configure({ unlockedTypes: ["True", "False", "eq"] });
    return instance;
};
const createHitEngine = () => {
    const instance = new TTCoreEngine();
    instance.configure({ unlockedTypes: creativeSandboxSystemRuleIds });
    return instance;
};

const engine = createEngine();

const bundle = {
    type: ["CircleCore", parse("U")],
    // A path constructor is still a constant, but it is not a point/data
    // constructor and therefore travels through the auxiliary type channel.
    auxiliaryTypes: [
        ["loopCore", parse("Px:True,baseCore = baseCore")],
        ["@ind_CircleCore", parse("True")],
        ["@rec_CircleCore", parse("True")],
        ["apd_loopCore", parse("baseCore = baseCore")],
        ["@apd_loopCore", parse("baseCore = baseCore")],
        ["ap_loopCore", parse("baseCore = baseCore")],
        ["@ap_loopCore", parse("baseCore = baseCore")]
    ],
    constructors: [["baseCore", parse("CircleCore")]],
    eliminator: ["ind_CircleCore", parse("True -> CircleCore -> True")],
    recursor: ["rec_CircleCore", parse("True -> CircleCore -> True")],
    computeRules: {
        rec_CircleCore: [{
            pattern: [parse("rec_CircleCore"), parse("?base"), parse("baseCore")],
            result: parse("?base")
        }]
    },
    metadata: {
        version: 3,
        kind: "hit1",
        dimension: 1,
        typeName: "CircleCore",
        eliminatorName: "ind_CircleCore",
        fullEliminatorName: "@ind_CircleCore",
        recursorName: "rec_CircleCore",
        fullRecursorName: "@rec_CircleCore",
        constructors: [{ name: "baseCore", argumentTypes: [] }],
        pathConstructors: [{
            name: "loopCore",
            argumentTypes: [parse("True")],
            left: parse("baseCore"),
            right: parse("baseCore"),
            computationName: "apd_loopCore"
        }]
    }
};
const pristineBundle = structuredClone(bundle);
const cloneBundle = () => structuredClone(pristineBundle);

const registration = engine.core.registerSystemInductive(bundle);
assert.deepEqual(registration.names, [
    "CircleCore",
    "loopCore",
    "@ind_CircleCore",
    "@rec_CircleCore",
    "apd_loopCore",
    "@apd_loopCore",
    "ap_loopCore",
    "@ap_loopCore",
    "baseCore",
    "ind_CircleCore",
    "rec_CircleCore"
]);
assert.equal(registration.computeRuleCount, 1);
assert.equal(engine.check("loopCore true : baseCore = baseCore").ok, true);
assert.equal(engine.check("rec_CircleCore true baseCore === true").ok, true);

const metadata = engine.core.getInductiveMetadata("CircleCore");
assert.equal(metadata.kind, "hit1");
assert.equal(metadata.dimension, 1);
assert.deepEqual(metadata.constructors.map(ctor => ctor.name), ["baseCore"]);
assert.deepEqual(metadata.pathConstructors.map(ctor => ctor.name), ["loopCore"]);
assert.equal(metadata.pathConstructors[0].computationName, "apd_loopCore");
assert.equal(engine.core.state.computeRules.loopCore, undefined);
assert.equal(engine.core.state.computeRules.apd_loopCore, undefined);
assert.equal(engine.core.state.computeRules["@apd_loopCore"], undefined);
assert.equal(engine.core.state.computeRules.ap_loopCore, undefined);
assert.equal(engine.core.state.computeRules["@ap_loopCore"], undefined);
assert.equal(engine.core.semanticKernel.hasComputeRules("loopCore"), false);
assert.equal(engine.core.semanticKernel.hasComputeRules("apd_loopCore"), false);
assert.equal(engine.core.semanticKernel.hasComputeRules("@apd_loopCore"), false);
assert.equal(engine.core.semanticKernel.hasComputeRules("ap_loopCore"), false);
assert.equal(engine.core.semanticKernel.hasComputeRules("@ap_loopCore"), false);

// Registration and retrieval must both isolate mutable AST payloads.
bundle.metadata.pathConstructors[0].left.name = "mutatedInput";
bundle.metadata.pathConstructors[0].argumentTypes[0].name = "mutatedArgument";
metadata.pathConstructors[0].right.name = "mutatedOutput";
const freshMetadata = engine.core.getInductiveMetadata("CircleCore");
assert.equal(freshMetadata.pathConstructors[0].left.name, "baseCore");
assert.equal(freshMetadata.pathConstructors[0].right.name, "baseCore");
assert.equal(freshMetadata.pathConstructors[0].argumentTypes[0].name, "True");
assert.notEqual(freshMetadata.pathConstructors[0].left, bundle.metadata.pathConstructors[0].left);
assert.notEqual(freshMetadata.pathConstructors[0].right, metadata.pathConstructors[0].right);
assert.notEqual(
    freshMetadata.pathConstructors[0].argumentTypes[0],
    bundle.metadata.pathConstructors[0].argumentTypes[0]
);

assert.throws(() => new TTCoreEngine().core.registerSystemInductive({
    type: ["BadHit", parse("U")],
    constructors: [["badLoop", parse("BadHit")]],
    metadata: {
        kind: "hit1",
        dimension: 1,
        typeName: "BadHit",
        eliminatorName: "ind_BadHit",
        constructors: [],
        pathConstructors: [{
            name: "badLoop",
            argumentTypes: [],
            left: parse("badLoop"),
            right: parse("badLoop")
        }]
    }
}), /路径构造子不能作为点构造子/);

assert.throws(() => new TTCoreEngine().core.registerSystemInductive({
    type: ["BadRuleHit", parse("U")],
    auxiliaryTypes: [["badRuleLoop", parse("BadRuleHit")]],
    constructors: [["badRuleBase", parse("BadRuleHit")]],
    eliminator: ["ind_BadRuleHit", parse("BadRuleHit -> BadRuleHit")],
    computeRules: {
        badRuleLoop: [{ pattern: [parse("badRuleLoop")], result: parse("badRuleBase") }]
    },
    metadata: {
        kind: "hit1",
        dimension: 1,
        typeName: "BadRuleHit",
        eliminatorName: "ind_BadRuleHit",
        constructors: [{ name: "badRuleBase", argumentTypes: [] }],
        pathConstructors: [{
            name: "badRuleLoop",
            argumentTypes: [],
            left: parse("badRuleBase"),
            right: parse("badRuleBase")
        }]
    }
}), /路径构造子不能注册为定义计算规则/);

for (const forbiddenHead of [
    "apd_badRuleLoop",
    "@apd_badRuleLoop",
    "ap_badRuleLoop",
    "@ap_badRuleLoop"
]) {
    assert.throws(() => createEngine().core.registerSystemInductive({
        type: ["BadRuleHit", parse("U")],
        auxiliaryTypes: [
            ["badRuleLoop", parse("badRuleBase = badRuleBase")],
            ["@ind_BadRuleHit", parse("True")],
            ["@rec_BadRuleHit", parse("True")],
            ["apd_badRuleLoop", parse("badRuleBase = badRuleBase")],
            ["@apd_badRuleLoop", parse("badRuleBase = badRuleBase")],
            ["ap_badRuleLoop", parse("badRuleBase = badRuleBase")],
            ["@ap_badRuleLoop", parse("badRuleBase = badRuleBase")]
        ],
        constructors: [["badRuleBase", parse("BadRuleHit")]],
        eliminator: ["ind_BadRuleHit", parse("BadRuleHit -> BadRuleHit")],
        recursor: ["rec_BadRuleHit", parse("BadRuleHit -> BadRuleHit")],
        computeRules: {
            [forbiddenHead]: [{ pattern: [parse(forbiddenHead)], result: parse("true") }]
        },
        metadata: {
            kind: "hit1",
            dimension: 1,
            typeName: "BadRuleHit",
            eliminatorName: "ind_BadRuleHit",
            fullEliminatorName: "@ind_BadRuleHit",
            recursorName: "rec_BadRuleHit",
            fullRecursorName: "@rec_BadRuleHit",
            constructors: [{ name: "badRuleBase", argumentTypes: [] }],
            pathConstructors: [{
                name: "badRuleLoop",
                argumentTypes: [],
                left: parse("badRuleBase"),
                right: parse("badRuleBase"),
                computationName: "apd_badRuleLoop"
            }]
        }
    }), /路径构造子不能注册为定义计算规则/);
}

for (const [field, wrongName, expectedMessage] of [
    ["eliminatorName", "loopCore", /公开消去器槽位/],
    ["fullEliminatorName", "@rec_CircleCore", /完整消去器槽位/],
    ["recursorName", "ind_CircleCore", /公开递归器槽位/],
    ["fullRecursorName", "@ind_CircleCore", /完整递归器槽位/]
]) {
    const mismatched = cloneBundle();
    mismatched.metadata[field] = wrongName;
    assert.throws(
        () => createEngine().core.registerSystemInductive(mismatched),
        expectedMessage
    );
}

const badPointTelescope = cloneBundle();
badPointTelescope.metadata.constructors[0].argumentTypes.push(parse("True"));
assert.throws(
    () => createEngine().core.registerSystemInductive(badPointTelescope),
    /点构造子.*telescope.*不一致/
);

const badPathTelescope = cloneBundle();
badPathTelescope.metadata.pathConstructors[0].argumentTypes[0] = parse("False");
assert.throws(
    () => createEngine().core.registerSystemInductive(badPathTelescope),
    /路径构造子.*telescope.*不一致/
);

const badPathEndpoint = cloneBundle();
badPathEndpoint.auxiliaryTypes.unshift(["otherCore", parse("CircleCore")]);
badPathEndpoint.auxiliaryTypes.find(([name]) => name === "loopCore")[1]
    = parse("Px:True,baseCore = otherCore");
assert.throws(
    () => createEngine().core.registerSystemInductive(badPathEndpoint),
    /路径构造子.*端点.*不一致/
);

const pathInDefinitionSlot = cloneBundle();
pathInDefinitionSlot.auxiliaryTypes = pathInDefinitionSlot.auxiliaryTypes
    .filter(([name]) => name !== "loopCore");
pathInDefinitionSlot.definitions = [["loopCore", parse("baseCore")]];
assert.throws(
    () => createEngine().core.registerSystemInductive(pathInDefinitionSlot),
    /路径构造子不存在/
);

const computationInDefinitionSlot = cloneBundle();
computationInDefinitionSlot.auxiliaryTypes = computationInDefinitionSlot.auxiliaryTypes
    .filter(([name]) => name !== "apd_loopCore");
computationInDefinitionSlot.definitions = [["apd_loopCore", parse("baseCore")]];
assert.throws(
    () => createEngine().core.registerSystemInductive(computationInDefinitionSlot),
    /计算定理不存在/
);

const nonPropositionalComputation = cloneBundle();
nonPropositionalComputation.auxiliaryTypes
    .find(([name]) => name === "ap_loopCore")[1] = parse("True");
assert.throws(
    () => createEngine().core.registerSystemInductive(nonPropositionalComputation),
    /路径计算项.*不是等式命题/
);

for (const missingName of [
    "loopCore",
    "@ind_CircleCore",
    "@rec_CircleCore",
    "apd_loopCore",
    "@apd_loopCore",
    "ap_loopCore",
    "@ap_loopCore"
]) {
    const missing = cloneBundle();
    missing.auxiliaryTypes = missing.auxiliaryTypes.filter(([name]) => name !== missingName);
    assert.throws(
        () => createEngine().core.registerSystemInductive(missing),
        /路径构造子不存在|完整消去器槽位|完整递归器槽位|计算定理不存在|路径计算项槽位/
    );
}

assert.throws(() => new TTCoreEngine().core.registerSystemInductive({
    type: ["MissingPathHit", parse("U")],
    constructors: [["missingPathBase", parse("MissingPathHit")]],
    eliminator: ["ind_MissingPathHit", parse("MissingPathHit -> MissingPathHit")],
    metadata: {
        kind: "hit1",
        dimension: 1,
        typeName: "MissingPathHit",
        eliminatorName: "ind_MissingPathHit",
        constructors: [{ name: "missingPathBase", argumentTypes: [] }],
        pathConstructors: [{
            name: "missingPathLoop",
            argumentTypes: [],
            left: parse("missingPathBase"),
            right: parse("missingPathBase")
        }]
    }
}), /路径构造子不存在/);

assert.throws(() => new TTCoreEngine().core.registerSystemInductive({
    type: ["MissingComputationHit", parse("U")],
    auxiliaryTypes: [["missingComputationLoop", parse("missingComputationBase = missingComputationBase")]],
    constructors: [["missingComputationBase", parse("MissingComputationHit")]],
    eliminator: ["ind_MissingComputationHit", parse("MissingComputationHit -> MissingComputationHit")],
    metadata: {
        kind: "hit1",
        dimension: 1,
        typeName: "MissingComputationHit",
        eliminatorName: "ind_MissingComputationHit",
        constructors: [{ name: "missingComputationBase", argumentTypes: [] }],
        pathConstructors: [{
            name: "missingComputationLoop",
            argumentTypes: [],
            left: parse("missingComputationBase"),
            right: parse("missingComputationBase"),
            computationName: "apd_missingComputationLoop"
        }]
    }
}), /计算定理不存在/);

assert.throws(() => new TTCoreEngine().core.registerSystemInductive({
    type: ["BadDimensionHit", parse("U")],
    auxiliaryTypes: [["badDimensionLoop", parse("badDimensionBase = badDimensionBase")]],
    constructors: [["badDimensionBase", parse("BadDimensionHit")]],
    eliminator: ["ind_BadDimensionHit", parse("BadDimensionHit -> BadDimensionHit")],
    metadata: {
        kind: "hit1",
        dimension: 2,
        typeName: "BadDimensionHit",
        eliminatorName: "ind_BadDimensionHit",
        constructors: [{ name: "badDimensionBase", argumentTypes: [] }],
        pathConstructors: [{
            name: "badDimensionLoop",
            argumentTypes: [],
            left: parse("badDimensionBase"),
            right: parse("badDimensionBase")
        }]
    }
}), /维度必须为 1/);

const parameterizedHit2 = lowerSandboxHit(parseSandboxHit(
    "hit SurfaceMetadata (A : U) : U "
    + "| baseMetadata : SurfaceMetadata A "
    + "| loopLeftMetadata : Πz:A,baseMetadata=baseMetadata "
    + "| loopRightMetadata : Πz:A,baseMetadata=baseMetadata "
    + "| path2 squareMetadata : Πz:A,loopLeftMetadata z=loopRightMetadata z"
));
const cloneHit2 = () => structuredClone(parameterizedHit2);

assert.doesNotThrow(() => createHitEngine().core.registerSystemInductive(cloneHit2()));

for (const [field, wrongPath] of [
    ["leftPath", "loopRightMetadata"],
    ["rightPath", "loopLeftMetadata"]
]) {
    const mismatchedHead = cloneHit2();
    mismatchedHead.metadata.twoPathConstructors[0][field] = wrongPath;
    assert.throws(
        () => createHitEngine().core.registerSystemInductive(mismatchedHead),
        /端点头常量与 [左右]Path metadata 不一致/
    );
}

const missingPathArgument = cloneHit2();
missingPathArgument.metadata.twoPathConstructors[0].left = parse("loopLeftMetadata A");
missingPathArgument.auxiliaryTypes.find(([name]) => name === "squareMetadata")[1]
    = parse("ΠA:U,Πz:A,(loopLeftMetadata A)=(loopRightMetadata A z)");
assert.throws(
    () => createHitEngine().core.registerSystemInductive(missingPathArgument),
    /左端点参数数量与一阶路径 loopLeftMetadata telescope 不一致/
);

const extraPathArgument = cloneHit2();
extraPathArgument.metadata.twoPathConstructors[0].right
    = parse("loopRightMetadata A z z");
extraPathArgument.auxiliaryTypes.find(([name]) => name === "squareMetadata")[1]
    = parse("ΠA:U,Πz:A,(loopLeftMetadata A z)=(loopRightMetadata A z z)");
assert.throws(
    () => createHitEngine().core.registerSystemInductive(extraPathArgument),
    /右端点参数数量与一阶路径 loopRightMetadata telescope 不一致/
);

const mismatchedUniformParameter = cloneHit2();
mismatchedUniformParameter.metadata.twoPathConstructors[0].left
    = parse("loopLeftMetadata True z");
mismatchedUniformParameter.auxiliaryTypes.find(([name]) => name === "squareMetadata")[1]
    = parse("ΠA:U,Πz:A,(loopLeftMetadata True z)=(loopRightMetadata A z)");
assert.throws(
    () => createHitEngine().core.registerSystemInductive(mismatchedUniformParameter),
    /左端点未保持统一参数：A/
);

console.log("Core HIT path-metadata regression passed");
