import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
};

const session = new TTCoreSession();
assert.equal(session.dispatch({ kind: "configure", config: {
    ...config,
    userDefinitions: [["embeddedOnly", parser.parse("true")]],
    userDefinitionCaches: []
} }), undefined);
const persistentCore = session.engine.core;
assert.equal(session.dispatch({ kind: "check", input: "embeddedOnly:True" })?.ok, true,
    "configure must retain definitions embedded in the legacy TTCoreConfig payload");

const base = session.dispatch({
    kind: "validate",
    index: 0,
    ast: parser.parse("base:=true:True")
});
assert.equal(base?.ok, true, base?.error);
assert.equal(session.engine.core, persistentCore,
    "dispatch validation rebuilt the persistent Core");

const checkedInput = session.dispatch({ kind: "check", input: "base" });
assert.equal(checkedInput?.ok, true, checkedInput?.error);
const checkedAst = session.dispatch({ kind: "check", ast: parser.parse("base") });
assert.equal(checkedAst?.ok, true, checkedAst?.error);

const snapshot = session.snapshot();
assert.equal(snapshot.definitions.length, 1);
assert.equal("userDefinitions" in snapshot.config, false,
    "session snapshots must keep definitions out of the configuration payload");
assert.equal("userDefinitionCaches" in snapshot.config, false,
    "session snapshots must keep definition caches out of the configuration payload");
const independentSnapshot = session.snapshot();
snapshot.definitions[0][0] = "corruptedSnapshot";
assert.equal(independentSnapshot.definitions[0][0], "base",
    "session snapshots must not share definition slot arrays");
assert.equal(session.dispatch({ kind: "check", input: "base" })?.ok, true,
    "mutating a snapshot changed the live session");
assert.equal(session.snapshot(0).definitions.length, 0);
const restored = new TTCoreSession();
const serializedSnapshot = JSON.parse(JSON.stringify(independentSnapshot));
restored.restore(serializedSnapshot);
const restoredCheck = restored.dispatch({ kind: "check", input: "base" });
assert.equal(restoredCheck?.ok, true, restoredCheck?.error);

const mirrored = new TTCoreSession();
mirrored.dispatch({ kind: "configure", config });
assert.equal(mirrored.dispatch({
    kind: "set-definition",
    index: 0,
    definition: independentSnapshot.definitions[0]
}), undefined);
assert.equal(mirrored.dispatch({ kind: "check", input: "base" })?.ok, true);

const rewound = new TTCoreSession();
rewound.configure(config, [
    null,
    ["later", parser.parse("true")]
]);
assert.equal(rewound.check("later:True")?.ok, true);
assert.equal(rewound.validate(0, parser.parse("true"))?.ok, true);
assert.equal(rewound.check("later:True")?.ok, false,
    "rewinding a validation prefix must hide the retained suffix definition");
const rewoundSnapshot = rewound.snapshot();
assert.equal(rewoundSnapshot.loadedThrough, 1);
const restoredRewound = new TTCoreSession();
restoredRewound.restore(JSON.parse(JSON.stringify(rewoundSnapshot)));
assert.equal(restoredRewound.check("later:True")?.ok, false,
    "restoring a rewound session exposed a retained suffix definition");
assert.equal(restoredRewound.validate(2, parser.parse("later:True"))?.ok, true,
    "a restored session must still reload the retained suffix when validation reaches it");

const shadows = new TTCoreSession();
shadows.dispatch({ kind: "configure", config });
assert.equal(shadows.dispatch({
    kind: "validate",
    index: 0,
    ast: parser.parse("shadow:=true:True")
})?.ok, true);
assert.equal(shadows.dispatch({
    kind: "validate",
    index: 1,
    ast: parser.parse("shadow:=0:nat")
})?.ok, true);
const shadowSnapshot = shadows.snapshot();
assert.equal(shadows.dispatch({ kind: "check", input: "shadow:nat" })?.ok, true);
assert.equal(shadows.dispatch({ kind: "truncate", startIndex: 1 }), undefined);
assert.equal(shadows.dispatch({ kind: "check", input: "shadow:True" })?.ok, true,
    "truncating a shadow definition did not restore the retained definition");
assert.equal(shadows.dispatch({ kind: "check", input: "shadow:nat" })?.ok, false);
assert.equal(shadows.dispatch({
    kind: "set-definition",
    index: 1,
    definition: shadowSnapshot.definitions[1]
}), undefined);
assert.equal(shadows.dispatch({ kind: "check", input: "shadow:nat" })?.ok, true);

assert.throws(
    () => session.dispatch({ kind: "unknown" }),
    /Unknown core request/
);

console.log("persistent core-session dispatch regression passed");
