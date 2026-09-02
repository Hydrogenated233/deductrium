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
    assert.equal(metadata.version, 6);
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
    assert.equal(metadata.version, 6);
    assert.equal(metadata.dimension, index + 1);
    assert.ok(metadata.pathLevels);
    assert.equal(metadata.pathConstructors, undefined);
    assert.equal(metadata.twoPathConstructors, undefined);
    assert.equal(metadata.threePathConstructors, undefined);
}

const isolationEngine = createEngine();
isolationEngine.core.registerSystemInductive(structuredClone(bundles[2]));
const firstRead = isolationEngine.core.getInductiveMetadata("Wire3");
const firstPath = firstRead.pathLevels[0].constructors[0];
const originalLeftName = firstPath.left.name;
firstPath.left.name = "mutatedWireEndpoint";
firstRead.pathLevels[2].constructors[0].sourcePath.name = "mutatedWireSource";
const secondRead = isolationEngine.core.getInductiveMetadata("Wire3");
assert.equal(secondRead.pathLevels[0].constructors[0].left.name, originalLeftName);
assert.notEqual(
    secondRead.pathLevels[2].constructors[0].sourcePath.name,
    "mutatedWireSource"
);

const v6WithLegacy = structuredClone(bundles[0]);
v6WithLegacy.metadata.pathConstructors = [];
assert.throws(
    () => createEngine().core.registerSystemInductive(v6WithLegacy),
    /v6 不能同时携带 legacy 路径字段/
);

const legacyWithPathLevels = structuredClone(bundles[0]);
legacyWithPathLevels.metadata.version = 3;
legacyWithPathLevels.metadata.pathConstructors
    = legacyWithPathLevels.metadata.pathLevels[0].constructors;
assert.throws(
    () => createEngine().core.registerSystemInductive(legacyWithPathLevels),
    /legacy HIT metadata v3 不能携带 pathLevels/
);

const v6WithoutPathLevels = structuredClone(bundles[0]);
delete v6WithoutPathLevels.metadata.pathLevels;
assert.throws(
    () => createEngine().core.registerSystemInductive(v6WithoutPathLevels),
    /v6 缺少 canonical pathLevels/
);

console.log("HIT metadata v6 wire and legacy migration regression passed");
