import assert from "node:assert/strict";

import { SandboxEnvironment } from "../js/tt/sandbox.js";

// Folder presentation changes must retain the public validation-result shape
// without re-running Core or changing the trusted bridge.
const sandbox = new SandboxEnvironment();
assert.equal(sandbox.add("A : U").ok, true);
const folder = sandbox.addFolder("Basics");
assert.equal(sandbox.addInFolder("a : A", folder.id).ok, true);

const baselineStats = { ...sandbox.lastValidationStats };
const baselineBridge = sandbox.bridge();
let validations = 0;
const validate = sandbox.validate.bind(sandbox);
sandbox.validate = (...args) => {
    validations++;
    return validate(...args);
};

const folded = sandbox.setFolderOpen(folder.id, false);
assert.equal(validations, 0,
    "folding a sandbox folder must not re-run declaration validation");
assert.equal(folded.ok, true);
assert.equal(folded.status, "ok");
assert.equal(sandbox.folders.find(item => item.id === folder.id)?.open, false);
assert.deepEqual(sandbox.lastValidationStats, baselineStats,
    "presentation-only mutations must not change validation counters");
assert.deepEqual(sandbox.bridge(), baselineBridge,
    "folding must leave the trusted bridge unchanged");

const renamed = sandbox.renameFolder(folder.id, "Renamed");
assert.equal(validations, 0,
    "renaming a sandbox folder must not re-run declaration validation");
assert.equal(renamed.ok, true);
assert.equal(sandbox.folders.find(item => item.id === folder.id)?.name, "Renamed");
assert.deepEqual(sandbox.bridge(), baselineBridge,
    "renaming must leave the trusted bridge unchanged");

const removed = sandbox.removeFolder(folder.id);
assert.equal(validations, 0,
    "removing an enabled empty/scope-only folder must not re-run validation");
assert.equal(removed.ok, true);
assert.equal(sandbox.declarations[1].folderId, null,
    "removing a folder must preserve its declarations at the root scope");
assert.deepEqual(sandbox.bridge(), baselineBridge,
    "removing an enabled folder must leave the bridge unchanged");

// A disabled folder changes the effective declaration availability when it is
// removed, so that semantic transition still validates the affected suffix.
const disabledFolder = sandbox.addFolder("Disabled");
assert.equal(sandbox.addInFolder("b : A", disabledFolder.id).ok, true);
assert.equal(sandbox.setFolderDisabled(disabledFolder.id, true).ok, true);
validations = 0;
const reopened = sandbox.removeFolder(disabledFolder.id);
assert.equal(validations, 1,
    "removing a disabled folder must revalidate declarations it re-enables");
assert.equal(reopened.ok, true);
assert.equal(
    sandbox.declarations.find(declaration => declaration.name === "b")?.status,
    "valid"
);

console.log("sandbox presentation-only mutation regression passed");
