import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { initTypeSystem } from "../js/tt/initial.js";
import { ASTParser } from "../js/tt/astparser.js";
import { jsonRequest, startTTServer, stopTTServer } from "./tt-process-test-utils.mjs";

const parser = new ASTParser();
const server = await startTTServer(fileURLToPath(new URL("..", import.meta.url)));
let session;
try {
    const created = await jsonRequest(server.baseUrl, "/api/tt/session", { body: {} });
    assert.equal(created.body?.ok, true, server.output());
    session = created.body;
    const rpc = async (channel, request) => (await jsonRequest(server.baseUrl, "/api/tt/rpc", {
        body: {
            sessionId: session.sessionId, generation: session.generation, channel, request
        }
    })).body;
    const success = async (channel, request) => {
        const body = await rpc(channel, request);
        assert.equal(body?.ok, true, body?.error ?? server.output());
        return body.result;
    };
    const config = {
        unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
        inferDisplayMode: "_", timeout: 30_000, language: "zh"
    };
    for (const channel of ["assist", "core"]) {
        await success(channel, { kind: "configure", config, definitions: [] });
    }
    const options = { disableMultipleApply: true, disableDestructConds: true, disableDestructEq: true };
    for (const [name, target, steps] of [
        ["what", "Πb:Bool,ind_Bool (λb:Bool.U1) U (U→U) b",
            ["intro b", "cases b", "simpl", "exact True", "simpl", "intro A", "exact A"]],
        ["sumAssoc", "ΠA:U,ΠB:U,ΠC:U,((A+B)+C)→(A+(B+C))",
            ["intros A B C s", "cases s", "cases sl", "left", "assumption", "right", "left",
                "assumption", "right", "right", "assumption"]]
    ]) {
        await success("assist", { kind: "start", target, options });
        for (const command of steps) await success("assist", { kind: "apply", command });
        const qed = await success("assist", { kind: "qed" });
        const reloaded = await success("core", {
            kind: "validate", index: 0,
            ast: parser.parseSurface(`${name} := ${qed.proof} : ${qed.theorem}`)
        });
        assert.equal(reloaded.ok, true, reloaded.error);
        assert.equal(reloaded.inferenceComplete, true);
    }
} finally {
    await stopTTServer(server, session ? [session.sessionId] : []);
}
console.log("issues #47/#48 isolated-process proof export and independent validation passed");
