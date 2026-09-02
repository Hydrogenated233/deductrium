import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { TTCoreEngine } from "../js/tt/engine.js";
import {
    SandboxEnvironment,
    creativeSandboxSystemRuleIds,
    lowerSandboxHit,
    parseSandboxHit
} from "../js/tt/sandbox.js";
import { SandboxWorkerSession } from "../js/tt/sandbox-worker.js";

const fixture = readFileSync(
    new URL("./fixtures/hit4-boundary.txt", import.meta.url),
    "utf8"
).trim();

assert.match(fixture, /path4\s+hyper4/);
assert.throws(
    () => parseSandboxHit(fixture),
    /最高只解析三维 HIT.*path4/,
    "dimension 4 must be recognized and rejected before lowering"
);

const cube3 = parseSandboxHit(
    "hit Cube3Boundary : U "
        + "| base3Boundary : Cube3Boundary "
        + "| loopA3Boundary : base3Boundary=base3Boundary "
        + "| loopB3Boundary : base3Boundary=base3Boundary "
        + "| path2 faceA3Boundary : loopA3Boundary=loopB3Boundary "
        + "| path2 faceB3Boundary : loopA3Boundary=loopB3Boundary "
        + "| path3 cell3Boundary : faceA3Boundary=faceB3Boundary"
);
const bundle = lowerSandboxHit(cube3);
const register = candidate => {
    const engine = new TTCoreEngine();
    engine.configure({ unlockedTypes: creativeSandboxSystemRuleIds });
    return engine.core.registerSystemInductive(candidate);
};

const forgedKind = structuredClone(bundle);
forgedKind.metadata.kind = "hit4";
forgedKind.metadata.dimension = 4;
assert.throws(
    () => register(forgedKind),
    /Core 最高只支持三维 HIT/,
    "a hand-built dimension-4 bundle must not bypass the parser boundary"
);

const forgedDimension = structuredClone(bundle);
forgedDimension.metadata.dimension = 4;
assert.throws(
    () => register(forgedDimension),
    /Core 最高只支持三维 HIT/,
    "a dimension field above the supported ceiling must be rejected"
);

const seed = new SandboxEnvironment();
seed.add("A4Fixture : U");
const save = seed.toJSON();
save.declarations[0] = {
    ...save.declarations[0],
    name: "Hyper4",
    kind: "hit",
    source: fixture,
    typeSource: "",
    status: "unchecked",
    dependencies: []
};
delete save.validationCache;

const bounded = new SandboxWorkerSession().handle({
    id: 1,
    kind: "load",
    save,
    options: { validationMaxNodes: 1 }
});
assert.equal(bounded.status, "budget-exhausted");
assert.match(bounded.error ?? "", /语法节点|资源上限/);
assert.equal(bounded.bridge, undefined,
    "a dimension-4 fixture beyond its request budget must not publish a bridge");

const validated = new SandboxWorkerSession().handle({
    id: 2,
    kind: "load",
    save,
    options: { validationMaxNodes: 100_000 }
});
assert.equal(validated.status, "invalid");
assert.match(validated.error ?? "", /最高只解析三维 HIT.*path4/);
assert.equal(validated.bridge?.inductives.length ?? 0, 0);

console.log("sandbox dimension-4 fixture and resource-boundary regression passed");
