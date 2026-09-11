import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { initTypeSystem } from "../js/tt/initial.js";
import { jsonRequest, startTTServer, stopTTServer } from "./tt-process-test-utils.mjs";

const server = await startTTServer(fileURLToPath(new URL("..", import.meta.url)));
let session;
try {
    const created = await jsonRequest(server.baseUrl, "/api/tt/session", { body: {} });
    assert.equal(created.body?.ok, true, server.output());
    session = created.body;
    const rpc = async request => {
        const { body } = await jsonRequest(server.baseUrl, "/api/tt/rpc", {
            body: {
                sessionId: session.sessionId, generation: session.generation,
                channel: "assist", request
            }
        });
        return body;
    };
    const success = async request => {
        const body = await rpc(request);
        assert.equal(body?.ok, true, body?.error ?? server.output());
        return body.result;
    };
    await success({
        kind: "configure",
        config: {
            unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
            inferDisplayMode: "_", timeout: 30_000, language: "zh"
        },
        definitions: []
    });
    const target = "Πp:(Σn:nat,n=n),Σm:nat,m=m";
    const options = {
        disableMultipleApply: false, disableDestructConds: false, disableDestructEq: false
    };
    await success({ kind: "start", target, options });
    const before = await success({ kind: "apply", command: "intro p" });
    const failed = await rpc({ kind: "apply", command: "obtain ⟨p, h⟩ := p" });
    assert.equal(failed?.ok, false);
    const obtained = await success({ kind: "apply", command: "obtain ⟨n, hn⟩ := p" });
    assert.deepEqual(obtained.history, ["intro p", "obtain ⟨n, hn⟩ := p"]);
    assert.deepEqual(obtained.goals[0].context.map(entry => entry[0]), ["n", "hn", "p"]);
    assert.deepEqual(await success({ kind: "undo" }), before);
    assert.deepEqual(await success({
        kind: "start", target, options, history: obtained.history
    }), obtained);
    await success({ kind: "apply", command: "use n" });
    const completed = await success({ kind: "apply", command: "exact hn" });
    assert.equal(completed.goals.length, 0);
    const proof = await success({ kind: "qed" });
    assert.equal(proof.theorem, "(Πp:(Σn:nat,(n=n)),(Σm:nat,(m=m)))");

    const nestedTarget = "Πp:(Σn:nat,Σm:nat,n=m),Σa:nat,Σb:nat,a=b";
    for (const command of [
        "rcases p with ⟨n, ⟨m, h⟩⟩",
        "obtain ⟨n, ⟨m, h⟩⟩ := p",
        "rintro ⟨n, ⟨m, h⟩⟩"
    ]) {
        let before = await success({ kind: "start", target: nestedTarget, options });
        if (!command.startsWith("rintro")) {
            before = await success({ kind: "apply", command: "intro p" });
            const failed = await rpc({
                kind: "apply", command: "rcases p with ⟨⟨x, y⟩, h⟩"
            });
            assert.equal(failed?.ok, false, "a failed nested elimination must not commit");
        }
        const nested = await success({ kind: "apply", command });
        assert.deepEqual(nested.history, [...before.history, command]);
        assert.deepEqual(await success({ kind: "undo" }), before);
        assert.deepEqual(await success({
            kind: "start", target: nestedTarget, options, history: nested.history
        }), nested);
        for (const command of ["use n", "use m", "exact h"]) {
            await success({ kind: "apply", command });
        }
        const qed = await success({ kind: "qed" });
        assert.equal(qed.theorem,
            "(Πp:(Σn:nat,(Σm:nat,(n=m))),(Σa:nat,(Σb:nat,(a=b))))");
    }
} finally {
    await stopTTServer(server, session ? [session.sessionId] : []);
}

console.log("type-theory obtain isolated-process regression passed");
