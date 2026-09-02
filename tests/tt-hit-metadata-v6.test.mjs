import assert from "node:assert/strict";

import { TTCoreEngine } from "../js/tt/engine.js";
import {
    creativeSandboxSystemRuleIds,
    lowerSandboxHit,
    parseSandboxHit
} from "../js/tt/sandbox.js";

const sources = [
    "hit Wire1 : U | pointW1 : Wire1 | loopW1 : pointW1=pointW1",
    "hit Wire2 : U | pointW2 : Wire2 "
        + "| loopW2A : pointW2=pointW2 | loopW2B : pointW2=pointW2 "
        + "| path2 faceW2 : loopW2A=loopW2B",
    "hit Wire3 : U | pointW3 : Wire3 "
        + "| loopW3A : pointW3=pointW3 | loopW3B : pointW3=pointW3 "
        + "| path2 faceW3A : loopW3A=loopW3B "
        + "| path2 faceW3B : loopW3A=loopW3B "
        + "| path3 cellW3 : faceW3A=faceW3B"
];
const bundles = sources.map(source => lowerSandboxHit(parseSandboxHit(source)));

for (let index = 0; index < bundles.length; index++) {
    const metadata = bundles[index].metadata;
    assert.equal(metadata.version, 7);
    assert.equal(metadata.dimension, index + 1);
    assert.ok(metadata.pathLevels);
    assert.equal(metadata.pathConstructors, undefined);
    assert.equal(metadata.twoPathConstructors, undefined);
    assert.equal(metadata.threePathConstructors, undefined);
}

const createEngine = () => {
    const engine = new TTCoreEngine();
    engine.configure({ unlockedTypes: creativeSandboxSystemRuleIds });
    return engine;
};

const jsonBundle = JSON.parse(JSON.stringify(bundles[2]));
const clonedBundle = structuredClone(jsonBundle);
const configured = new TTCoreEngine();
configured.configure({
    unlockedTypes: creativeSandboxSystemRuleIds,
    trustedInductives: [clonedBundle]
});
assert.equal(configured.check("cellW3 : faceW3A=faceW3B").ok, true);

const toLegacy = (bundle, version) => {
    const legacy = structuredClone(bundle);
    const levels = legacy.metadata.pathLevels;
    for (const path of levels[2].constructors) {
        const conclusion = bundle.auxiliaryTypes.find(([name]) => name === path.name)[1];
        const left = path.leftExpression;
        const right = path.rightExpression;
        assert.equal(left.kind, "atom");
        assert.equal(right.kind, "atom");
        const leftPath = levels[1].constructors.find(candidate => candidate.name === left.name);
        const rightPath = levels[1].constructors.find(candidate => candidate.name === right.name);
        path.left = structuredClone(conclusion.nodes[0]);
        path.right = structuredClone(conclusion.nodes[1]);
        path.leftTwoPath = left.name;
        path.rightTwoPath = right.name;
        path.sourcePath = structuredClone(leftPath.left);
        path.targetPath = structuredClone(leftPath.right);
        delete path.leftExpression;
        delete path.rightExpression;
        assert.deepEqual(leftPath.left, rightPath.left);
        assert.deepEqual(leftPath.right, rightPath.right);
    }
    delete legacy.metadata.pathLevels;
    legacy.metadata.version = version;
    legacy.metadata.pathConstructors = levels[0].constructors;
    legacy.metadata.twoPathConstructors = levels[1].constructors;
    legacy.metadata.threePathConstructors = levels[2].constructors;
    return legacy;
};

for (let index = 0; index < bundles.length; index++) {
    const engine = createEngine();
    const legacy = toLegacy(bundles[index], index + 3);
    engine.core.registerSystemInductive(legacy);
    const metadata = engine.core.getInductiveMetadata(`Wire${index + 1}`);
    assert.equal(metadata.version, 7);
    assert.equal(metadata.dimension, index + 1);
    assert.ok(metadata.pathLevels);
    assert.equal(metadata.pathConstructors, undefined);
    assert.equal(metadata.twoPathConstructors, undefined);
    assert.equal(metadata.threePathConstructors, undefined);
}

for (const bundle of bundles) {
    const v6 = structuredClone(bundle);
    v6.metadata.version = 6;
    for (const path of v6.metadata.pathLevels[2].constructors) {
        const conclusion = bundle.auxiliaryTypes.find(([name]) => name === path.name)[1];
        const left = path.leftExpression;
        const right = path.rightExpression;
        assert.equal(left.kind, "atom");
        assert.equal(right.kind, "atom");
        const twoPaths = v6.metadata.pathLevels[1].constructors;
        const leftPath = twoPaths.find(candidate => candidate.name === left.name);
        const rightPath = twoPaths.find(candidate => candidate.name === right.name);
        path.left = structuredClone(conclusion.nodes[0]);
        path.right = structuredClone(conclusion.nodes[1]);
        path.leftTwoPath = left.name;
        path.rightTwoPath = right.name;
        path.sourcePath = structuredClone(leftPath.left);
        path.targetPath = structuredClone(leftPath.right);
        delete path.leftExpression;
        delete path.rightExpression;
        assert.deepEqual(leftPath.left, rightPath.left);
        assert.deepEqual(leftPath.right, rightPath.right);
    }
    const engine = createEngine();
    engine.core.registerSystemInductive(v6);
    assert.equal(engine.core.getInductiveMetadata(bundle.metadata.typeName).version, 7);
}

const isolationEngine = createEngine();
isolationEngine.core.registerSystemInductive(structuredClone(bundles[2]));
const firstRead = isolationEngine.core.getInductiveMetadata("Wire3");
const firstPath = firstRead.pathLevels[0].constructors[0];
const originalLeftName = firstPath.left.name;
firstPath.left.name = "mutatedWireEndpoint";
firstRead.pathLevels[2].constructors[0].leftExpression.name = "mutatedWireSource";
const secondRead = isolationEngine.core.getInductiveMetadata("Wire3");
assert.equal(secondRead.pathLevels[0].constructors[0].left.name, originalLeftName);
assert.notEqual(
    secondRead.pathLevels[2].constructors[0].leftExpression.name,
    "mutatedWireSource"
);

const v7WithLegacy = structuredClone(bundles[0]);
v7WithLegacy.metadata.pathConstructors = [];
assert.throws(
    () => createEngine().core.registerSystemInductive(v7WithLegacy),
    /v7 不能同时携带 legacy 路径字段/
);

const legacyWithPathLevels = structuredClone(bundles[0]);
legacyWithPathLevels.metadata.version = 3;
legacyWithPathLevels.metadata.pathConstructors
    = legacyWithPathLevels.metadata.pathLevels[0].constructors;
assert.throws(
    () => createEngine().core.registerSystemInductive(legacyWithPathLevels),
    /legacy HIT metadata v3 不能携带 pathLevels/
);

const v7WithoutPathLevels = structuredClone(bundles[0]);
delete v7WithoutPathLevels.metadata.pathLevels;
assert.throws(
    () => createEngine().core.registerSystemInductive(v7WithoutPathLevels),
    /v7 缺少 canonical pathLevels/
);

const v7PathWithLegacyField = structuredClone(bundles[2]);
v7PathWithLegacyField.metadata.pathLevels[2].constructors[0].sourcePath
    = structuredClone(v7PathWithLegacyField.metadata.pathLevels[0].constructors[0].left);
assert.throws(
    () => createEngine().core.registerSystemInductive(v7PathWithLegacyField),
    /v7 三阶路径构造子.*不能携带 legacy 冗余字段/,
    "v7 path entries must not carry a second, forgeable boundary representation"
);

const unknownAtom = structuredClone(bundles[2]);
unknownAtom.metadata.pathLevels[2].constructors[0].leftExpression = {
    kind: "atom",
    name: "missingWireTwoPath",
    arguments: []
};
assert.throws(
    () => createEngine().core.registerSystemInductive(unknownAtom),
    /三阶路径构造子.*引用不存在/,
    "Core must resolve every expression atom from the certified two-path table"
);

const cyclicExpression = structuredClone(bundles[2]);
const cycle = { kind: "inverse" };
cycle.value = cycle;
cyclicExpression.metadata.pathLevels[2].constructors[0].leftExpression = cycle;
assert.throws(
    () => createEngine().core.registerSystemInductive(cyclicExpression),
    /不能循环引用自身/,
    "cyclic programmatic metadata must be rejected before recursive reconstruction"
);

const tooDeepExpression = structuredClone(bundles[2]);
let deep = structuredClone(tooDeepExpression.metadata.pathLevels[2].constructors[0].leftExpression);
for (let index = 0; index < 130; index++) deep = { kind: "inverse", value: deep };
tooDeepExpression.metadata.pathLevels[2].constructors[0].leftExpression = deep;
assert.throws(
    () => createEngine().core.registerSystemInductive(tooDeepExpression),
    /表达式嵌套过深/,
    "expression reconstruction must have an independent recursion-depth boundary"
);

const tooManyExpressionNodes = structuredClone(bundles[2]);
const atom = structuredClone(tooManyExpressionNodes.metadata.pathLevels[2].constructors[0].leftExpression);
const makeBalancedExpression = depth => depth === 0
    ? structuredClone(atom)
    : {
        kind: "compose",
        left: makeBalancedExpression(depth - 1),
        right: makeBalancedExpression(depth - 1)
    };
tooManyExpressionNodes.metadata.pathLevels[2].constructors[0].leftExpression
    = makeBalancedExpression(12);
assert.throws(
    () => createEngine().core.registerSystemInductive(tooManyExpressionNodes),
    /表达式节点过多/,
    "a shallow but exponentially large expression tree must be bounded"
);

const compositeSource = "hit LegacyComposite : U | legacyPoint : LegacyComposite "
    + "| legacyLoop0 : legacyPoint=legacyPoint | legacyLoop1 : legacyPoint=legacyPoint "
    + "| legacyLoop2 : legacyPoint=legacyPoint "
    + "| path2 legacyFace01 : legacyLoop0=legacyLoop1 "
    + "| path2 legacyFace12 : legacyLoop1=legacyLoop2 "
    + "| path2 legacyFace02 : legacyLoop0=legacyLoop2 "
    + "| path3 legacyCell : (legacyFace01▪legacyFace12)=legacyFace02";
const v6Composite = lowerSandboxHit(parseSandboxHit(compositeSource));
v6Composite.metadata.version = 6;
assert.throws(
    () => createEngine().core.registerSystemInductive(v6Composite),
    /legacy 三阶路径端点 metadata 不完整/,
    "v6 migration must remain direct-atom-only instead of interpreting v7 expression fields"
);

console.log("HIT metadata v7 wire and v3-v6 migration regression passed");
