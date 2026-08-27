import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";

import { ASTParser } from "../js/tt/astparser.js";
import { initTypeSystem } from "../js/tt/initial.js";
import {
    jsonRequest,
    minimalTTConfig,
    startTTServer,
    stopTTServer
} from "./tt-process-test-utils.mjs";

const projectRoot = fileURLToPath(new URL("..", import.meta.url));
const parser = new ASTParser();
const server = await startTTServer(projectRoot, { DEDUCTRIUM_TT_MAX_SESSIONS: "2" });
const activeSessions = new Set();

async function createSession() {
    const { response, body } = await jsonRequest(server.baseUrl, "/api/tt/session", { body: {} });
    assert.equal(response.status, 201, server.output());
    assert.equal(body?.ok, true, server.output());
    assert.equal(typeof body?.sessionId, "string");
    assert.equal(body?.generation, 1);
    assert.equal(body?.protocolVersion, 1);
    activeSessions.add(body.sessionId);
    return { sessionId: body.sessionId, generation: body.generation };
}

async function rpc(session, channel, request, generation = session.generation) {
    return jsonRequest(server.baseUrl, "/api/tt/rpc", {
        body: {
            sessionId: session.sessionId,
            generation,
            channel,
            request
        }
    });
}

try {
    {
        const { response, body } = await jsonRequest(server.baseUrl, "/api/tt/health");
        assert.equal(response.status, 200, server.output());
        assert.deepEqual(
            { ok: body?.ok, available: body?.available, protocolVersion: body?.protocolVersion },
            { ok: true, available: true, protocolVersion: 1 }
        );
        assert.equal(body?.sessions, 0);
    }

    {
        const port = new URL(server.baseUrl).port;
        const forged = await jsonRequest(server.baseUrl, "/api/tt/session", {
            headers: {
                Host: `evil.test:${port}`,
                Origin: `http://evil.test:${port}`
            },
            body: {}
        });
        assert.ok(
            forged.response.status === 403 || forged.response.status === 404,
            server.output()
        );
        assert.ok(
            forged.body?.code === "TT_PROCESS_FORBIDDEN"
                || forged.body?.code === "TT_PROCESS_LOCAL_ONLY"
        );

        const privateFile = await jsonRequest(server.baseUrl, "/.git/config");
        assert.equal(privateFile.response.status, 404, "the static server exposed repository metadata");
        const sourceFile = await jsonRequest(server.baseUrl, "/src/tt/core.ts");
        assert.equal(sourceFile.response.status, 404, "the static server exposed TypeScript sources");
        for (const traversal of [
            "/js/%2e%2e%2f.git/config",
            "/js/%2e%2e%5csrc/tt/core.ts",
            "/js/%2e%2e%2fserver.mjs"
        ]) {
            const escaped = await jsonRequest(server.baseUrl, traversal);
            assert.equal(escaped.response.status, 404,
                `the static server accepted encoded traversal: ${traversal}`);
        }
    }

    const first = await createSession();
    const second = await createSession();

    {
        const limited = await jsonRequest(server.baseUrl, "/api/tt/session", { body: {} });
        assert.equal(limited.response.status, 429, server.output());
        assert.equal(limited.body?.code, "TT_PROCESS_SESSION_LIMIT");
        const health = await jsonRequest(server.baseUrl, "/api/tt/health");
        assert.equal(health.body?.sessions, 2);
    }

    for (const session of [first, second]) {
        const configured = await rpc(session, "core", {
            kind: "configure",
            config: minimalTTConfig,
            definitions: []
        });
        assert.equal(configured.response.status, 200, server.output());
        assert.equal(configured.body?.ok, true, server.output());
    }

    {
        const checked = await rpc(first, "core", { kind: "check", input: "true" });
        assert.equal(checked.response.status, 200, server.output());
        assert.equal(checked.body?.ok, true, server.output());
        assert.equal(checked.body?.result?.ok, true, checked.body?.result?.error);
        assert.equal(checked.body?.result?.type?.name, "True");
    }

    {
        const declaration = parser.parse("onlyInFirst:=true:True");
        const validated = await rpc(first, "core", {
            kind: "validate",
            index: 0,
            ast: declaration
        });
        assert.equal(validated.body?.ok, true, server.output());
        assert.equal(validated.body?.result?.ok, true, validated.body?.result?.error);

        const visible = await rpc(first, "core", { kind: "check", input: "onlyInFirst" });
        const isolated = await rpc(second, "core", { kind: "check", input: "onlyInFirst" });
        assert.equal(visible.body?.result?.ok, true, visible.body?.result?.error);
        assert.equal(isolated.body?.result?.ok, false,
            "a definition from one process session leaked into another session");
    }

    {
        const configured = await rpc(first, "assist", {
            kind: "configure",
            config: minimalTTConfig,
            definitions: []
        });
        assert.equal(configured.body?.ok, true, server.output());

        const options = {
            disableMultipleApply: false,
            disableDestructConds: false,
            disableDestructEq: false
        };
        const started = await rpc(first, "assist", { kind: "start", target: "True", options });
        assert.equal(started.body?.ok, true, server.output());
        assert.equal(started.body?.result?.goals?.length, 1);

        const applied = await rpc(first, "assist", { kind: "apply", command: "exact true" });
        assert.equal(applied.body?.ok, true, applied.body?.error);
        assert.equal(applied.body?.result?.goals?.length, 0);

        const qed = await rpc(first, "assist", { kind: "qed" });
        assert.equal(qed.body?.ok, true, qed.body?.error);
        assert.equal(qed.body?.result?.theorem, "True");
        assert.match(qed.body?.result?.proof ?? "", /true/);
    }

    {
        const options = {
            disableMultipleApply: false,
            disableDestructConds: false,
            disableDestructEq: false
        };
        const retainedSuffix = [
            null,
            ["later", parser.parse("True")]
        ];
        const rewound = await rpc(first, "assist", {
            kind: "configure",
            config: minimalTTConfig,
            definitions: retainedSuffix,
            loadedThrough: 1
        });
        assert.equal(rewound.body?.ok, true, server.output());
        const hidden = await rpc(first, "assist", { kind: "start", target: "later", options });
        assert.equal(hidden.body?.ok, false,
            "the assistant process exposed a definition retained beyond loadedThrough");

        const reloaded = await rpc(first, "assist", {
            kind: "configure",
            config: minimalTTConfig,
            definitions: retainedSuffix,
            loadedThrough: 2
        });
        assert.equal(reloaded.body?.ok, true, server.output());
        const visible = await rpc(first, "assist", { kind: "start", target: "later", options });
        assert.equal(visible.body?.ok, true, visible.body?.error ?? server.output());
    }

    {
        const config = {
            ...minimalTTConfig,
            unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))]
        };
        const options = {
            disableMultipleApply: false,
            disableDestructConds: false,
            disableDestructEq: false
        };
        const target = "Πa:U0,Πb:U0,Πc:U0,(a ≃ b)→(b ≃ c)→((a ≃ c))";
        const prefix = [
            "intro a",
            "intro b",
            "intro c",
            "expand eqv",
            "intro ab",
            "intro bc"
        ];
        const configured = await rpc(first, "assist", {
            kind: "configure",
            config,
            definitions: []
        });
        assert.equal(configured.body?.ok, true, server.output());

        let result = await rpc(first, "assist", { kind: "start", target, options });
        assert.equal(result.body?.ok, true, result.body?.error ?? server.output());
        for (const command of prefix) {
            result = await rpc(first, "assist", { kind: "apply", command });
            assert.equal(
                result.body?.ok,
                true,
                command + ": " + (result.body?.error ?? server.output())
            );
        }
        assert.equal(result.body?.result?.goals?.length, 1);
        assert.equal(result.body?.result?.history?.at(-1), "intro bc");

        // The reported stale-binder failure can surface after further work and
        // undo. Exercise that exact path through the isolated process.
        for (const command of [
            "ex",
            "intro f",
            "exact (pr0 bc) ((pr0 ab) f)",
            "case",
            "ex"
        ]) {
            result = await rpc(first, "assist", { kind: "apply", command });
            assert.equal(
                result.body?.ok,
                true,
                command + ": " + (result.body?.error ?? server.output())
            );
        }
        result = await rpc(first, "assist", { kind: "undo" });
        assert.equal(result.body?.ok, true, result.body?.error ?? server.output());
        result = await rpc(first, "assist", { kind: "undo" });
        assert.equal(result.body?.ok, true, result.body?.error ?? server.output());
        result = await rpc(first, "assist", { kind: "apply", command: "case" });
        assert.equal(result.body?.ok, true, result.body?.error ?? server.output());

        const replayed = await rpc(first, "assist", {
            kind: "start",
            target,
            options,
            history: prefix
        });
        assert.equal(replayed.body?.ok, true, replayed.body?.error ?? server.output());
        assert.equal(replayed.body?.result?.goals?.length, 1);
        assert.equal(replayed.body?.result?.history?.at(-1), "intro bc");
    }

    {
        const previousGeneration = first.generation;
        const reset = await jsonRequest(server.baseUrl, "/api/tt/reset", {
            body: { sessionId: first.sessionId, generation: previousGeneration }
        });
        assert.equal(reset.response.status, 200, server.output());
        assert.equal(reset.body?.ok, true);
        assert.equal(reset.body?.restarted, true);
        assert.equal(reset.body?.generation, previousGeneration + 1);
        first.generation = reset.body.generation;

        const stale = await rpc(first, "core", { kind: "check", input: "true" }, previousGeneration);
        assert.equal(stale.response.status, 409);
        assert.equal(stale.body?.code, "TT_PROCESS_GENERATION_CHANGED");
        assert.equal(stale.body?.generation, first.generation);

        const staleReset = await jsonRequest(server.baseUrl, "/api/tt/reset", {
            body: { sessionId: first.sessionId, generation: previousGeneration }
        });
        assert.equal(staleReset.body?.ok, true);
        assert.equal(staleReset.body?.restarted, false);
        assert.equal(staleReset.body?.generation, first.generation);

        const configured = await rpc(first, "core", {
            kind: "configure",
            config: minimalTTConfig,
            definitions: []
        });
        assert.equal(configured.body?.ok, true, server.output());
        const checked = await rpc(first, "core", { kind: "check", input: "true" });
        assert.equal(checked.body?.result?.ok, true, checked.body?.result?.error);
    }

    {
        const disposed = await jsonRequest(server.baseUrl, "/api/tt/dispose", {
            body: { sessionId: first.sessionId }
        });
        assert.equal(disposed.response.status, 200, server.output());
        assert.equal(disposed.body?.ok, true);
        activeSessions.delete(first.sessionId);

        const missing = await rpc(first, "core", { kind: "check", input: "true" });
        assert.equal(missing.response.status, 404);
        assert.equal(missing.body?.code, "TT_PROCESS_SESSION_NOT_FOUND");

        const secondStillWorks = await rpc(second, "core", { kind: "check", input: "true" });
        assert.equal(secondStillWorks.body?.result?.ok, true, secondStillWorks.body?.result?.error);
    }

    await jsonRequest(server.baseUrl, "/api/tt/dispose", { body: { sessionId: second.sessionId } });
    activeSessions.delete(second.sessionId);
    const health = await jsonRequest(server.baseUrl, "/api/tt/health");
    assert.equal(health.body?.sessions, 0);
} finally {
    await stopTTServer(server, activeSessions);
}

console.log("isolated type-theory process HTTP regression passed");
