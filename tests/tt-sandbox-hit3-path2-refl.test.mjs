import assert from "node:assert/strict";

import { TTCoreEngine } from "../js/tt/engine.js";
import {
    SandboxEnvironment,
    creativeSandboxSystemRuleIds,
    lowerSandboxHit,
    parseSandboxHit
} from "../js/tt/sandbox.js";
import { SandboxWorkerSession } from "../js/tt/sandbox-worker.js";

const register = bundle => {
    const engine = new TTCoreEngine();
    engine.configure({ unlockedTypes: creativeSandboxSystemRuleIds });
    return engine.core.registerSystemInductive(structuredClone(bundle));
};

// The two-dimensional laws deliberately use refl(point) as their endpoints.
// The three-dimensional laws then refer to those path2 constructors through
// composition and inverse, which exercises Core's canonical reconstruction of
// the nested endpoint expressions and its explicit hit_dep2 primitives.
const source =
    "hit Path3OverPath2Refl [n:nat] : U "
    + "| pointP3R:Πn:nat,Path3OverPath2Refl n "
    + "| loopP3R:Πn:nat,pointP3R n=pointP3R n "
    + "| path2 forwardP3R:Πn:nat,refl (pointP3R n)=loopP3R n "
    + "| path2 backwardP3R:Πn:nat,loopP3R n=refl (pointP3R n) "
    + "| path2 u:Πn:nat,refl (pointP3R n)=refl (pointP3R n) "
    + "| path3 composeP3R:Πn:nat,(forwardP3R n▪backwardP3R n)=u n "
    + "| path3 inverseP3R:Πn:nat,inveq (forwardP3R n)=backwardP3R n";

const parsed = parseSandboxHit(source);
const twoPaths = new Map(parsed.pathLevels[1].constructors.map(path => [path.name, path]));
assert.equal(twoPaths.get("forwardP3R")?.leftExpression.kind, "refl");
assert.equal(twoPaths.get("backwardP3R")?.rightExpression.kind, "refl");
assert.equal(twoPaths.get("u")?.leftExpression.kind, "refl");
assert.equal(twoPaths.get("u")?.rightExpression.kind, "refl");
const threePaths = new Map(parsed.pathLevels[2].constructors.map(path => [path.name, path]));
assert.equal(threePaths.get("composeP3R")?.leftExpression.kind, "compose");
assert.equal(threePaths.get("inverseP3R")?.leftExpression.kind, "inverse");

const bundle = lowerSandboxHit(parsed);
const forwardMetadata = bundle.metadata.pathLevels[1].constructors
    .find(path => path.name === "forwardP3R");
const composeMetadata = bundle.metadata.pathLevels[2].constructors
    .find(path => path.name === "composeP3R");
const inverseMetadata = bundle.metadata.pathLevels[2].constructors
    .find(path => path.name === "inverseP3R");
assert.equal(forwardMetadata?.leftExpression.kind, "refl");
assert.equal(composeMetadata?.leftExpression.kind, "compose");
assert.equal(inverseMetadata?.leftExpression.kind, "inverse");
const hasConstant = (ast, name) => {
    const stack = [ast];
    while (stack.length) {
        const current = stack.pop();
        if (!current) continue;
        if (current.type === "var" && current.name === name) return true;
        stack.push(...(current.nodes ?? []));
    }
    return false;
};
const generatedTypes = [
    bundle.eliminator?.[1],
    ...(bundle.auxiliaryTypes ?? []).map(([, type]) => type)
].filter(Boolean);
assert.equal(generatedTypes.some(type => hasConstant(type, "@hit_dep2_comp")), true);
assert.equal(generatedTypes.some(type => hasConstant(type, "@hit_dep2_inv")), true);
for (const name of [
    "apd3_composeP3R", "@apd3_composeP3R",
    "ap3_composeP3R", "@ap3_composeP3R",
    "apd3_inverseP3R", "@apd3_inverseP3R",
    "ap3_inverseP3R", "@ap3_inverseP3R"
]) {
    assert.ok(bundle.generatedNames.includes(name),
        `path3 lowering must expose ${name}`);
}

const save = new SandboxEnvironment().toJSON();
save.declarations = [{
    id: "path3-over-path2-refl",
    name: "Path3OverPath2Refl",
    kind: "hit",
    source,
    typeSource: "U",
    enabled: true,
    trusted: true,
    status: "unchecked",
    dependencies: [],
    folderId: null
}];
save.order = ["path3-over-path2-refl"];
delete save.validationCache;
const worker = new SandboxWorkerSession();
const restored = worker.handle({
    id: 1,
    kind: "load",
    save,
    options: {
        systemRuleIds: creativeSandboxSystemRuleIds,
        validationTimeoutMs: 60_000
    }
});
assert.equal(restored.ok, true, restored.error);
assert.equal(restored.bridge.inductives[0].metadata.kind, "hit3");
assert.equal(
    worker.handle({
        id: 2,
        kind: "check",
        source: "apd3_composeP3R",
        options: {
            systemRuleIds: creativeSandboxSystemRuleIds,
            validationTimeoutMs: 60_000
        }
    }).ok,
    true,
    "source-only Worker restore must rebuild nested path2 refl laws"
);

const forged = structuredClone(bundle);
const forgedForward = forged.metadata.pathLevels[1].constructors
    .find(path => path.name === "forwardP3R");
assert.ok(forgedForward);
if (forgedForward.leftExpression.kind === "refl") {
    forgedForward.leftExpression.pointName = "loopP3R";
}
assert.throws(
    () => register(forged),
    /未知点端点|点构造子不存在|refl|metadata|不一致/,
    "Core must reject forged path2 refl metadata before rebuilding path3 laws"
);

console.log("sandbox path3 over path2 refl regression passed");
