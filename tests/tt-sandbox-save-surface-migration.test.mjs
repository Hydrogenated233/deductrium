import assert from "node:assert/strict";

import {
    migrateLegacySandboxDeclarationSource,
    migrateLegacySandboxSave,
    parseSandboxDeclaration,
    parseSandboxDeclarationSurface,
    createSandboxDeclaration
} from "../js/tt/sandbox.js";

// The low-level parser remains a compatibility API for fixtures and migrated
// saves, while the editor-facing entry rejects old ASCII notation.
assert.doesNotThrow(() => parseSandboxDeclaration("A : Lx:U.x"));
assert.doesNotThrow(() => parseSandboxDeclarationSurface("A : λx:U.x"));
assert.doesNotThrow(
    () => parseSandboxDeclarationSurface("compose := rfl \\* rfl"),
    "sandbox surface input should expand \\* to the composition operator"
);
const composed = createSandboxDeclaration("compose := rfl \\* rfl", "sandbox-compose");
assert.equal(composed.source, "compose := rfl ▪ rfl");
assert.deepEqual(composed.dependencies, ["rfl"]);
assert.throws(
    () => parseSandboxDeclarationSurface("A : Lx:U.x"),
    /不再支持旧语法/u
);

assert.equal(
    migrateLegacySandboxDeclarationSource("A : Lx:U.x"),
    "A : λx:U.x"
);
assert.equal(
    migrateLegacySandboxDeclarationSource(
        "inductive List (P : U) : U | nil : List P | mk : Lx:P.x"
    ),
    "inductive List (P : U) : U | nil : List P | mk : λx:P.x"
);
assert.equal(
    migrateLegacySandboxDeclarationSource(
        "hit Lfoo (S : U) : U | p : Lfoo S | path2 Pfoo : Lx:Lfoo S.x"
    ),
    "hit Lfoo (S : U) : U | p : Lfoo S | path2 Pfoo : λx:Lfoo S.x"
);

const legacy = {
    version: 1,
    declarations: [{
        id: "sandbox-17",
        name: "Lfoo",
        source: "inductive List (P : U) : U | nil : List P | mk : Lx:P.x",
        typeSource: "P U",
        enabled: false,
        status: "invalid",
        error: "保留",
        dependencies: ["Pfoo"],
        folderId: "folder-2",
        customMetadata: { keep: true }
    }],
    folders: [{
        kind: "folder",
        id: "folder-2",
        name: "L/P/S/X folder",
        length: 1,
        open: false,
        disabled: true
    }],
    order: ["folder-2", "sandbox-17"]
};

const migrated = migrateLegacySandboxSave(legacy);
assert.notEqual(migrated, legacy, "migration must return a cloned save envelope");
assert.equal(migrated.declarations[0].source,
    "inductive List (P : U) : U | nil : List P | mk : λx:P.x");
assert.equal(migrated.declarations[0].typeSource, "P U");
assert.equal(migrated.declarations[0].name, "Lfoo");
assert.equal(migrated.declarations[0].enabled, false);
assert.equal(migrated.declarations[0].folderId, "folder-2");
assert.deepEqual(migrated.declarations[0].customMetadata, { keep: true });
assert.deepEqual(migrated.folders, legacy.folders);
assert.deepEqual(migrated.order, legacy.order);

assert.deepEqual(
    migrateLegacySandboxSave(migrated),
    migrated,
    "loading an already migrated save must be idempotent"
);

console.log("sandbox save surface migration regression passed");
