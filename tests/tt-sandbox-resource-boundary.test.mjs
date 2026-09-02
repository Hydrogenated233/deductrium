import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import {
    SandboxEnvironment,
    creativeSandboxSystemRuleIds,
    inspectSandboxHitSource,
    lowerSandboxHit,
    parseSandboxHit
} from "../js/tt/sandbox.js";
import { SandboxWorkerSession } from "../js/tt/sandbox-worker.js";
import { sandboxBrowserEnvironmentOptions } from "../js/tt/sandbox-gui.js";

const path4Fixture = readFileSync(
    new URL("./fixtures/hit4-boundary.txt", import.meta.url),
    "utf8"
).trim();

const cube3Source = "hit ResourceCube3 : U "
    + "| resourceBase3 : ResourceCube3 "
    + "| resourceLoopA3 : resourceBase3=resourceBase3 "
    + "| resourceLoopB3 : resourceBase3=resourceBase3 "
    + "| path2 resourceFaceA3 : resourceLoopA3=resourceLoopB3 "
    + "| path2 resourceFaceB3 : resourceLoopA3=resourceLoopB3 "
    + "| path3 resourceCell3 : resourceFaceA3=resourceFaceB3";

{
    const inspection = inspectSandboxHitSource(path4Fixture);
    assert.equal(inspection.maxPathLevel, 4);
    assert.equal(inspection.firstUnsupportedPath?.level, 4);
    assert.equal(inspection.firstUnsupportedPath?.offset, path4Fixture.indexOf("path4"));
}

{
    const defaults = sandboxBrowserEnvironmentOptions();
    for (const key of [
        "validationMaxDeclarations",
        "validationMaxSourceChars",
        "validationMaxNodes",
        "validationMaxSteps",
        "validationTimeoutMs"
    ]) {
        assert.equal(Number.isFinite(defaults[key]) && defaults[key] > 0, true,
            `browser sandbox default ${key} must be a positive finite bound`);
    }
    assert.equal(
        sandboxBrowserEnvironmentOptions({ validationMaxSourceChars: 256 }).validationMaxSourceChars,
        256,
        "explicit browser sandbox limits must override production defaults"
    );
}

function uncheckedSave(source, id = "sandbox-resource-boundary") {
    const save = new SandboxEnvironment().toJSON();
    save.declarations = [{
        id,
        name: "Hyper4",
        kind: "hit",
        source,
        typeSource: "U",
        enabled: true,
        trusted: true,
        status: "unchecked",
        dependencies: [],
        folderId: null
    }];
    save.order = [id];
    delete save.validationCache;
    return save;
}

{
    const canonical = parseSandboxHit(cube3Source);
    const legacyOnly = {
        ...canonical,
        pathConstructors: structuredClone(canonical.pathLevels[0].constructors),
        twoPathConstructors: structuredClone(canonical.pathLevels[1].constructors),
        threePathConstructors: structuredClone(canonical.pathLevels[2].constructors)
    };
    delete legacyOnly.pathLevels;

    assert.throws(
        () => lowerSandboxHit(legacyOnly),
        /pathLevels/,
        "the public sandbox lowerer must reject legacy-only path arrays instead of rebuilding them"
    );
}

{
    const oversizedSource = `${path4Fixture}\n${" ".repeat(4_096)}`;
    const result = new SandboxWorkerSession().handle({
        id: 1,
        kind: "load",
        save: uncheckedSave(oversizedSource),
        options: {
            validationMaxSourceChars: 256,
            validationMaxNodes: 100_000,
            validationMaxSteps: 100_000
        }
    });

    assert.equal(result.status, "budget-exhausted",
        "raw source size must be bounded before the full HIT parser runs");
    assert.match(result.error ?? "", /源文本|字符|source/i);
    assert.doesNotMatch(result.error ?? "", /path4/,
        "the source-character preflight must win over the later path4 parser diagnostic");
    assert.equal(result.validationStats?.checkedDeclarations ?? 0, 0);
    assert.equal(result.bridge, undefined,
        "a source rejected by preflight must not publish a bridge");
}

{
    const cached = new SandboxEnvironment({
        systemRuleIds: creativeSandboxSystemRuleIds
    });
    const added = cached.add(cube3Source);
    assert.equal(added.ok, true, added.error);
    const forgedSave = cached.toJSON();
    assert.ok(forgedSave.validationCache?.entries?.length,
        "the fixture must start with a valid cached HIT artifact");

    forgedSave.declarations[0] = {
        ...forgedSave.declarations[0],
        name: "Hyper4",
        source: path4Fixture,
        typeSource: "U",
        kind: "hit",
        status: "valid",
        error: undefined,
        dependencies: []
    };
    forgedSave.validationCache.entries[0].status = "valid";
    forgedSave.validationCache.entries[0].kind = "hit";
    forgedSave.validationCache.entries[0].artifact = { kind: "hit" };

    const result = new SandboxWorkerSession().handle({
        id: 2,
        kind: "load",
        save: forgedSave,
        options: {
            systemRuleIds: creativeSandboxSystemRuleIds,
            validationMaxSourceChars: 100_000,
            validationMaxNodes: 100_000,
            validationMaxSteps: 100_000
        }
    });

    assert.equal(result.ok, false,
        "a forged valid cache marker must not make a path4 source valid");
    assert.equal(result.status, "invalid");
    assert.match(result.error ?? "", /最高只解析三维 HIT.*path4/);
    assert.equal(result.declarations[0].status, "invalid");
    assert.equal(result.bridge?.inductives.length ?? 0, 0,
        "a forged path4 cache must never publish an inductive bundle");
}

console.log("sandbox source and dimension resource-boundary regressions passed");
