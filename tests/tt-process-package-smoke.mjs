import assert from "node:assert/strict";
import { readFile, stat } from "node:fs/promises";
import { resolve } from "node:path";

import {
    jsonRequest,
    minimalTTConfig,
    startTTServer,
    stopTTServer
} from "./tt-process-test-utils.mjs";

const packageDirectory = resolve(process.argv[2] ?? process.cwd());
for (const relativePath of ["package.json", "server.mjs", "tt-process.mjs", "js/tt/core-session.js"]) {
    const info = await stat(resolve(packageDirectory, relativePath));
    assert.equal(info.isFile(), true, `packaged runtime is missing ${relativePath}`);
}
const packageJson = JSON.parse(await readFile(resolve(packageDirectory, "package.json"), "utf8"));
assert.equal(packageJson.type, "module", "packaged JavaScript must retain ESM package metadata");

const server = await startTTServer(packageDirectory);
const sessions = new Set();
try {
    const health = await jsonRequest(server.baseUrl, "/api/tt/health");
    assert.equal(health.response.status, 200, server.output());
    assert.equal(health.body?.available, true, server.output());

    const created = await jsonRequest(server.baseUrl, "/api/tt/session", { body: {} });
    assert.equal(created.response.status, 201, server.output());
    assert.equal(created.body?.ok, true, server.output());
    sessions.add(created.body.sessionId);

    const rpcBody = request => ({
        sessionId: created.body.sessionId,
        generation: created.body.generation,
        channel: "core",
        request
    });
    const configured = await jsonRequest(server.baseUrl, "/api/tt/rpc", {
        body: rpcBody({ kind: "configure", config: minimalTTConfig, definitions: [] })
    });
    assert.equal(configured.body?.ok, true, server.output());

    const checked = await jsonRequest(server.baseUrl, "/api/tt/rpc", {
        body: rpcBody({ kind: "check", input: "true" })
    });
    assert.equal(checked.body?.ok, true, server.output());
    assert.equal(checked.body?.result?.ok, true, checked.body?.result?.error);
    assert.equal(checked.body?.result?.type?.name, "True");
} finally {
    await stopTTServer(server, sessions);
}

console.log(`packaged type-theory process smoke test passed: ${packageDirectory}`);
