import assert from "node:assert/strict";

import {
    SandboxEnvironment,
    creativeSandboxSystemRuleIds
} from "../js/tt/sandbox.js";
import { SandboxWorkerSession } from "../js/tt/sandbox-worker.js";

const checked = result => result.validationStats?.checkedDeclarations ?? -1;
const replayed = result => result.validationStats?.replayedDeclarations ?? -1;

function loadFresh(save, options) {
    const session = new SandboxWorkerSession();
    const request = { id: 1, kind: "load", save };
    if (options !== undefined) request.options = options;
    const result = session.handle(request);
    return { result, session };
}

function cacheEntries(save) {
    assert.ok(save.validationCache, "the source environment must persist a validation cache");
    assert.ok(Array.isArray(save.validationCache.entries),
        "the validation cache must expose one ordered entry list");
    return save.validationCache.entries;
}

function assertNormalFallback(save, label, options) {
    const { result, session } = loadFresh(save, options);
    assert.equal(result.ok, true, `${label}: cache rejection must fall back to normal validation`);
    assert.ok(checked(result) > 0, `${label}: stale cache must not be reported as a cache hit`);
    assert.equal(checked(result) + replayed(result), save.declarations.length,
        `${label}: every declaration must be checked or replayed exactly once`);
    assert.ok(result.validationCache,
        `${label}: successful fallback validation must replace the rejected cache`);
    return { result, session };
}

function mutatePrefixKey(entry) {
    const field = Object.keys(entry).find(key =>
        /prefix|hash|fingerprint/i.test(key) && typeof entry[key] === "string"
    );
    assert.ok(field, "each cache entry must bind itself to its validated source prefix");
    entry[field] = `${entry[field]}-tampered`;
}

function replaceCachedTypeWithFalse(value) {
    const falseType = { type: "var", name: "False", nodes: [] };
    const seen = new WeakSet();
    let replacements = 0;
    const visit = current => {
        if (!current || typeof current !== "object" || seen.has(current)) return;
        seen.add(current);
        if (Array.isArray(current)) {
            for (const item of current) visit(item);
            return;
        }
        for (const [key, child] of Object.entries(current)) {
            if (/type$/i.test(key)
                && child && typeof child === "object" && !Array.isArray(child)
                && typeof child.type === "string") {
                current[key] = structuredClone(falseType);
                replacements++;
                continue;
            }
            if (/typeSource$/i.test(key) && typeof child === "string") {
                current[key] = "False";
                replacements++;
                continue;
            }
            visit(child);
        }
    };
    visit(value);
    if (!replacements) {
        // A cache implementation may initially omit definition hints. Inject a
        // plausible native snapshot so later support cannot accidentally start
        // trusting this user-editable field.
        value.definitionHint = {
            kind: "nbe",
            type: falseType,
            metas: [],
            bondVarId: 0
        };
    }
}

const environment = new SandboxEnvironment();
environment.add("A : U");
environment.add("a : A");
environment.add("tail : A");
const cachedSave = environment.toJSON();
const entries = cacheEntries(cachedSave);
assert.equal(typeof cachedSave.validationCache.version, "number",
    "sandbox validation caches must carry an explicit format version");
assert.ok(cachedSave.validationCache.version > 0);
assert.equal(entries.length, cachedSave.declarations.length,
    "a complete valid environment caches each ordered declaration");

{
    const { result, session } = loadFresh(cachedSave);
    assert.equal(result.ok, true);
    assert.equal(checked(result), 0,
        "a restarted Worker must reuse an untampered persisted cache");
    assert.equal(replayed(result), cachedSave.declarations.length);
    assert.ok(result.validationCache);
    assert.equal(session.handle({ id: 2, kind: "check", source: "tail" }).ok, true,
        "the environment rebuilt from cached entries must remain usable");
}

{
    const options = { systemRuleIds: creativeSandboxSystemRuleIds };
    const structured = new SandboxEnvironment(options);
    structured.add("truth := true");
    structured.add("inductive CacheTri : U | cacheNt : CacheTri | cachePt : CacheTri");
    structured.add("hit CacheCircle : U | cacheBase : CacheCircle | cacheLoop : cacheBase = cacheBase");
    const save = structured.toJSON();
    assert.equal(cacheEntries(save).length, save.declarations.length);
    const { result, session } = loadFresh(save, options);
    assert.equal(result.ok, true, result.error);
    assert.equal(checked(result), 0,
        "closed definitions and regenerated inductive/HIT bundles use the certified replay path");
    assert.equal(replayed(result), save.declarations.length);
    assert.equal(session.handle({ id: 2, kind: "check", source: "truth:True", options }).ok, true);
    assert.equal(session.handle({ id: 3, kind: "check", source: "cacheNt:CacheTri", options }).ok, true);
    assert.equal(session.handle({ id: 4, kind: "check", source: "cacheLoop", options }).ok, true);
}

{
    const oldSave = structuredClone(cachedSave);
    delete oldSave.validationCache;
    const { result, session } = loadFresh(oldSave);
    assert.equal(result.ok, true, "old cacheless saves remain supported");
    assert.equal(checked(result), oldSave.declarations.length,
        "an old save without validation metadata is checked from source");
    assert.equal(replayed(result), 0);
    assert.equal(session.handle({ id: 2, kind: "check", source: "tail" }).ok, true);
}

{
    const changed = structuredClone(cachedSave);
    changed.declarations[0].source = "A : U0";
    const { session } = assertNormalFallback(changed, "source change");
    assert.equal(session.handle({ id: 2, kind: "check", source: "tail" }).ok, true);
}

{
    const changed = structuredClone(cachedSave);
    [changed.order[1], changed.order[2]] = [changed.order[2], changed.order[1]];
    const { session } = assertNormalFallback(changed, "declaration order change");
    assert.equal(session.handle({ id: 2, kind: "check", source: "a" }).ok, true);
    assert.equal(session.handle({ id: 3, kind: "check", source: "tail" }).ok, true);
}

{
    const changed = structuredClone(cachedSave);
    changed.declarations[1].enabled = false;
    const { session } = assertNormalFallback(changed, "enabled-state change");
    assert.equal(session.handle({ id: 2, kind: "check", source: "A" }).ok, true);
    assert.equal(session.handle({ id: 3, kind: "check", source: "a" }).ok, false,
        "a stale cache must not restore a declaration that is now disabled");
}

{
    const nested = new SandboxEnvironment();
    const outer = nested.addFolder("outer");
    const inner = nested.addFolder("inner");
    nested.moveItem(inner.id, `after:${outer.id}`);
    nested.addInFolder("NestedA : U", inner.id);
    const nestedSave = nested.toJSON();
    cacheEntries(nestedSave);
    const changed = structuredClone(nestedSave);
    changed.folders.find(folder => folder.id === outer.id).disabled = true;
    const { result, session } = assertNormalFallback(changed, "recursive folder disable");
    assert.equal(result.declarations[0].status, "disabled");
    assert.equal(session.handle({ id: 2, kind: "check", source: "NestedA" }).ok, false,
        "a disabled parent folder must keep cached nested declarations unavailable");
}

{
    const changedPrelude = {
        systemRuleIds: ["True", "False", "eq", "eq.=", "nat"]
    };
    const { session } = assertNormalFallback(cachedSave, "prelude change", changedPrelude);
    assert.equal(session.handle({
        id: 2,
        kind: "check",
        source: "nat",
        options: changedPrelude
    }).ok, true,
        "validation after a prelude-key mismatch must use the requested prelude");
}

{
    const changed = structuredClone(cachedSave);
    changed.validationCache.version = Number.MAX_SAFE_INTEGER;
    assertNormalFallback(changed, "unknown cache version");
}

{
    const changed = structuredClone(cachedSave);
    cacheEntries(changed)[0].id = "tampered-cache-entry";
    assertNormalFallback(changed, "tampered cache entry");
}

{
    const changed = structuredClone(cachedSave);
    mutatePrefixKey(cacheEntries(changed)[0]);
    assertNormalFallback(changed, "tampered prefix fingerprint");
}

{
    const changed = structuredClone(cachedSave);
    const changedEntries = cacheEntries(changed);
    while (changedEntries.length <= 4_096) {
        changedEntries.push(structuredClone(changedEntries[0]));
    }
    assertNormalFallback(changed, "oversized cache entry list");
}

{
    const forged = structuredClone(cachedSave);
    forged.declarations[0].source = "A : Missing";
    forged.declarations[0].status = "valid";
    forged.declarations[0].error = undefined;
    const session = new SandboxWorkerSession();
    const result = session.handle({ id: 1, kind: "load", save: forged });
    assert.equal(result.ok, false,
        "a persisted valid status must not turn an invalid source into a declaration");
    assert.equal(result.status, "invalid");
    assert.ok(checked(result) > 0);
    assert.equal(session.handle({ id: 2, kind: "check", source: "A" }).ok, false);
}

{
    const transparent = new SandboxEnvironment();
    transparent.add("truth := true");
    const forged = transparent.toJSON();
    const entry = cacheEntries(forged)[0];
    forged.declarations[0].status = "valid";
    forged.declarations[0].kind = "definition";
    forged.declarations[0].typeSource = "False";
    replaceCachedTypeWithFalse(entry);

    const { result, session } = loadFresh(forged);
    assert.equal(result.ok, true,
        "a forged definition cache must be discarded or verified against its source");
    assert.equal(result.declarations[0].typeSource, "True",
        "the transparent definition type must come from checking `truth := true`");
    assert.equal(session.handle({ id: 2, kind: "check", source: "truth:True" }).ok, true);
    assert.equal(session.handle({ id: 3, kind: "check", source: "truth:False" }).ok, false,
        "a forged cache type must not make true inhabit False");
    assert.equal(session.handle({ id: 4, kind: "check", source: "true:False" }).ok, false);
}

console.log("sandbox persisted validation-cache safety regression passed");
