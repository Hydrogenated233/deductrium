import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { initTypeSystem } from "../js/tt/initial.js";
import { jsonRequest, startTTServer, stopTTServer } from "./tt-process-test-utils.mjs";

const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_", timeout: 30_000, language: "zh"
};
const options = {
    disableMultipleApply: false, disableDestructConds: false, disableDestructEq: false
};
const local = new TTAssistEngine();
local.configure(config);
const server = await startTTServer(fileURLToPath(new URL("..", import.meta.url)));
let session;
try {
    const created = await jsonRequest(server.baseUrl, "/api/tt/session", { body: {} });
    assert.equal(created.body?.ok, true, server.output());
    session = created.body;
    const rpc = async request => (await jsonRequest(server.baseUrl, "/api/tt/rpc", {
        body: {
            sessionId: session.sessionId, generation: session.generation,
            channel: "assist", request
        }
    })).body;
    const success = async request => {
        const body = await rpc(request);
        assert.equal(body?.ok, true, body?.error ?? server.output());
        return body.result;
    };
    await success({ kind: "configure", config, definitions: [] });
    const target = "Σn:nat,n=n";
    await success({ kind: "start", target, options });
    local.start(target, options);
    const before = await success({ kind: "apply", command: "constructor" });
    local.apply("constructor");
    const failed = await rpc({
        kind: "apply", command: "· have n : nat := by exact 0\n  exact n\n  rfl"
    });
    assert.equal(failed?.ok, false);
    assert.match(failed.error, /第 3 行.*无证明目标/s);
    const command = "· have n : nat := by exact 0\n  exact n";
    const after = await success({ kind: "apply", command });
    const localAfter = local.apply(command);
    // RPC uses JSON while the local snapshot retains undefined properties.
    assert.deepEqual(after, JSON.parse(JSON.stringify(localAfter)));
    assert.deepEqual(await success({ kind: "undo" }), before);
    assert.deepEqual(await success({
        kind: "start", target, options, history: after.history
    }), after);
    await success({ kind: "apply", command: "· rfl" });
    local.apply("· rfl");
    assert.deepEqual(await success({ kind: "qed" }), local.qed());
} finally {
    await stopTTServer(server, session ? [session.sessionId] : []);
}
console.log("type-theory structured scripts isolated-process parity passed");
