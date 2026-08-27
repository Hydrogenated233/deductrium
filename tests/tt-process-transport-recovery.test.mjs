import assert from "node:assert/strict";

import { TTProcessTransport } from "../js/tt/process-transport.js";

const originalFetch = globalThis.fetch;

const jsonResponse = (body, status = 200) => new Response(JSON.stringify(body), {
    status,
    headers: { "Content-Type": "application/json" }
});

async function sessionLossRestoresBothChannels() {
    let sessionCount = 0;
    let failedCheck = false;
    const calls = [];
    globalThis.fetch = async (url, init = {}) => {
        if (url === "/api/tt/session") {
            sessionCount++;
            const sessionId = `session-${sessionCount}`;
            calls.push({ kind: "session", sessionId });
            return jsonResponse({ ok: true, sessionId, generation: 1, protocolVersion: 1 }, 201);
        }
        assert.equal(url, "/api/tt/rpc");
        const body = JSON.parse(init.body);
        const call = {
            kind: body.request.kind,
            channel: body.channel,
            sessionId: body.sessionId,
            generation: body.generation,
            marker: body.request.config?.marker
        };
        if (body.request.kind === "start") call.history = body.request.history;
        calls.push(call);
        if (body.request.kind === "check" && !failedCheck) {
            failedCheck = true;
            return jsonResponse({
                ok: false,
                error: "Type-theory session was not found",
                code: "TT_PROCESS_SESSION_NOT_FOUND"
            }, 404);
        }
        if (body.request.kind === "check") {
            return jsonResponse({ ok: true, result: { ok: true, marker: "restored" }, generation: 1 });
        }
        if (body.request.kind === "start") {
            return jsonResponse({ ok: true, result: { history: body.request.history ?? [] }, generation: 1 });
        }
        if (body.request.kind === "apply") {
            return jsonResponse({ ok: true, result: { history: ["exact true"] }, generation: 1 });
        }
        return jsonResponse({ ok: true, generation: 1 });
    };

    const transport = new TTProcessTransport();
    await transport.request("core", {
        kind: "configure",
        config: { marker: "core-config" },
        definitions: []
    });
    await transport.request("assist", {
        kind: "configure",
        config: { marker: "assist-config" },
        definitions: []
    });
    await transport.request("assist", {
        kind: "start",
        target: "True",
        options: {},
        history: []
    });
    await transport.request("assist", { kind: "apply", command: "exact true" });
    const result = await transport.request("core", { kind: "check", input: "true" });

    assert.deepEqual(result, { ok: true, marker: "restored" });
    assert.deepEqual(calls, [
        { kind: "session", sessionId: "session-1" },
        {
            kind: "configure",
            channel: "core",
            sessionId: "session-1",
            generation: 1,
            marker: "core-config"
        },
        {
            kind: "configure",
            channel: "assist",
            sessionId: "session-1",
            generation: 1,
            marker: "assist-config"
        },
        {
            kind: "start",
            channel: "assist",
            sessionId: "session-1",
            generation: 1,
            marker: undefined,
            history: []
        },
        {
            kind: "apply",
            channel: "assist",
            sessionId: "session-1",
            generation: 1,
            marker: undefined
        },
        {
            kind: "check",
            channel: "core",
            sessionId: "session-1",
            generation: 1,
            marker: undefined
        },
        { kind: "session", sessionId: "session-2" },
        {
            kind: "configure",
            channel: "core",
            sessionId: "session-2",
            generation: 1,
            marker: "core-config"
        },
        {
            kind: "configure",
            channel: "assist",
            sessionId: "session-2",
            generation: 1,
            marker: "assist-config"
        },
        {
            kind: "start",
            channel: "assist",
            sessionId: "session-2",
            generation: 1,
            marker: undefined,
            history: ["exact true"]
        },
        {
            kind: "check",
            channel: "core",
            sessionId: "session-2",
            generation: 1,
            marker: undefined
        }
    ]);
}

async function generationChangeReusesSessionAndRetriesOnce() {
    let checkAttempts = 0;
    const calls = [];
    globalThis.fetch = async (url, init = {}) => {
        if (url === "/api/tt/session") {
            calls.push({ kind: "session" });
            return jsonResponse({
                ok: true,
                sessionId: "stable-session",
                generation: 1,
                protocolVersion: 1
            }, 201);
        }
        assert.equal(url, "/api/tt/rpc");
        const body = JSON.parse(init.body);
        calls.push({
            kind: body.request.kind,
            generation: body.generation,
            definitionNames: body.request.kind === "configure"
                ? body.request.definitions.map(definition => definition?.[0] ?? null)
                : undefined
        });
        if (body.request.kind === "check" && checkAttempts++ === 0) {
            return jsonResponse({
                ok: false,
                error: "Type-theory process generation changed",
                code: "TT_PROCESS_GENERATION_CHANGED",
                generation: 2
            }, 409);
        }
        return jsonResponse({
            ok: true,
            result: body.request.kind === "check" ? { ok: true } : undefined,
            generation: body.generation
        });
    };

    const transport = new TTProcessTransport();
    await transport.request("core", {
        kind: "configure",
        config: { marker: "core-config" },
        definitions: []
    });
    const firstDefinition = ["first", { type: "var", name: "true" }];
    await transport.request("core", {
        kind: "validate",
        index: 0,
        ast: { type: ":=", nodes: [{ type: "var", name: "first" }, firstDefinition[1]] }
    });
    transport.rememberDefinition("core", 0, firstDefinition);
    const result = await transport.request("core", { kind: "check", input: "true" });

    assert.deepEqual(result, { ok: true });
    assert.deepEqual(calls, [
        { kind: "session" },
        { kind: "configure", generation: 1, definitionNames: [] },
        { kind: "validate", generation: 1, definitionNames: undefined },
        { kind: "check", generation: 1, definitionNames: undefined },
        { kind: "configure", generation: 2, definitionNames: ["first"] },
        { kind: "check", generation: 2, definitionNames: undefined }
    ], "a generation change should restore the committed prefix and retry exactly once");
}

async function ordinaryRecheckPreservesRetainedSuffix() {
    let checkAttempts = 0;
    const restoredDefinitions = [];
    const restoredLoadedThrough = [];
    globalThis.fetch = async (url, init = {}) => {
        if (url === "/api/tt/session") {
            return jsonResponse({
                ok: true,
                sessionId: "retained-suffix-session",
                generation: 1,
                protocolVersion: 1
            }, 201);
        }
        assert.equal(url, "/api/tt/rpc");
        const body = JSON.parse(init.body);
        if (body.request.kind === "configure") {
            restoredDefinitions.push(body.request.definitions.map(definition => definition?.[0] ?? null));
            restoredLoadedThrough.push(body.request.loadedThrough);
        }
        if (body.request.kind === "check" && checkAttempts++ === 0) {
            return jsonResponse({
                ok: false,
                error: "Type-theory process generation changed",
                code: "TT_PROCESS_GENERATION_CHANGED",
                generation: 2
            }, 409);
        }
        return jsonResponse({
            ok: true,
            result: body.request.kind === "check" || body.request.kind === "validate"
                ? { ok: true }
                : undefined,
            generation: body.generation
        });
    };

    const laterDefinition = ["later", { type: "var", name: "true" }];
    const transport = new TTProcessTransport();
    await transport.request("core", {
        kind: "configure",
        config: {},
        definitions: [null, laterDefinition]
    });
    await transport.request("core", {
        kind: "validate",
        index: 0,
        ast: { type: "var", name: "true" }
    });
    await transport.request("core", { kind: "check", input: "later" });

    assert.deepEqual(restoredDefinitions, [
        [null, "later"],
        [null, "later"]
    ], "rechecking a non-definition row discarded a retained suffix definition");
    assert.deepEqual(restoredLoadedThrough, [undefined, 1],
        "process recovery loaded a retained suffix instead of preserving its session cursor");
}

async function recoveryUsesOwnedCoreSessionSnapshot() {
    let checkAttempts = 0;
    const configurations = [];
    globalThis.fetch = async (url, init = {}) => {
        if (url === "/api/tt/session") {
            return jsonResponse({
                ok: true,
                sessionId: "snapshot-session",
                generation: 1,
                protocolVersion: 1
            }, 201);
        }
        assert.equal(url, "/api/tt/rpc");
        const body = JSON.parse(init.body);
        if (body.request.kind === "configure") configurations.push(body.request);
        if (body.request.kind === "check" && checkAttempts++ === 0) {
            return jsonResponse({
                ok: false,
                error: "Type-theory process generation changed",
                code: "TT_PROCESS_GENERATION_CHANGED",
                generation: 2
            }, 409);
        }
        return jsonResponse({
            ok: true,
            result: body.request.kind === "check" ? { ok: true } : undefined,
            generation: body.generation
        });
    };

    const definition = ["snapshotBase", { type: "var", name: "true" }];
    const config = {
        marker: "snapshot-config",
        // These legacy fields are redundant with the ordered slots and must
        // never be retained in the recovery configuration.
        userDefinitions: [["staleEmbedded", { type: "var", name: "false" }]],
        userDefinitionCaches: [["staleEmbedded", { kind: "nbe" }]]
    };
    const transport = new TTProcessTransport();
    await transport.request("core", {
        kind: "configure",
        config,
        definitions: [definition]
    });
    definition[0] = "mutatedAfterConfigure";
    definition[1].name = "false";
    config.marker = "mutated-after-configure";
    await transport.request("core", { kind: "check", input: "true" });

    assert.equal(configurations.length, 2);
    assert.deepEqual(configurations[0].config.userDefinitions, [
        ["staleEmbedded", { type: "var", name: "false" }]
    ], "the initial wire request must remain backwards compatible");
    assert.equal(configurations[1].config.marker, "snapshot-config");
    assert.equal("userDefinitions" in configurations[1].config, false);
    assert.equal("userDefinitionCaches" in configurations[1].config, false);
    assert.deepEqual(configurations[1].definitions, [
        ["snapshotBase", { type: "var", name: "true", checked: null }, null]
    ], "recovery must replay the owned cloned definition slots");
}

async function recoveryLiftsLegacyEmbeddedDefinitions() {
    let checkAttempts = 0;
    const configurations = [];
    globalThis.fetch = async (url, init = {}) => {
        if (url === "/api/tt/session") {
            return jsonResponse({
                ok: true,
                sessionId: "legacy-prefix-session",
                generation: 1,
                protocolVersion: 1
            }, 201);
        }
        assert.equal(url, "/api/tt/rpc");
        const body = JSON.parse(init.body);
        if (body.request.kind === "configure") configurations.push(body.request);
        if (body.request.kind === "check" && checkAttempts++ === 0) {
            return jsonResponse({
                ok: false,
                error: "Type-theory process generation changed",
                code: "TT_PROCESS_GENERATION_CHANGED",
                generation: 2
            }, 409);
        }
        return jsonResponse({
            ok: true,
            result: body.request.kind === "check" ? { ok: true } : undefined,
            generation: body.generation
        });
    };

    const transport = new TTProcessTransport();
    await transport.request("core", {
        kind: "configure",
        config: {
            marker: "legacy-prefix-config",
            userDefinitions: [["embeddedBase", { type: "var", name: "true" }]],
            userDefinitionCaches: []
        }
    });
    await transport.request("core", { kind: "check", input: "embeddedBase" });

    assert.equal(configurations.length, 2);
    assert.deepEqual(configurations[0].config.userDefinitions, [
        ["embeddedBase", { type: "var", name: "true" }]
    ], "the initial legacy wire request must be accepted unchanged");
    assert.equal("userDefinitions" in configurations[1].config, false);
    assert.equal("userDefinitionCaches" in configurations[1].config, false);
    assert.deepEqual(configurations[1].definitions, [
        ["embeddedBase", { type: "var", name: "true", checked: null }, null]
    ], "recovery must lift legacy embedded definitions into the ordered session prefix");
}

try {
    await sessionLossRestoresBothChannels();
    await generationChangeReusesSessionAndRetriesOnce();
    await ordinaryRecheckPreservesRetainedSuffix();
    await recoveryUsesOwnedCoreSessionSnapshot();
    await recoveryLiftsLegacyEmbeddedDefinitions();
} finally {
    globalThis.fetch = originalFetch;
}

console.log("type-theory process session recovery regression passed");
