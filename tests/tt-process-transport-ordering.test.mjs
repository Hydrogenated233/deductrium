import assert from "node:assert/strict";

import {
    TTProcessExecutionError,
    TTProcessTransport
} from "../js/tt/process-transport.js";

const originalFetch = globalThis.fetch;

const jsonResponse = (body, status = 200) => new Response(JSON.stringify(body), {
    status,
    headers: { "Content-Type": "application/json" }
});

async function preservesPerChannelCallOrder() {
    let releaseFirst;
    let firstStarted;
    const firstGate = new Promise(resolve => { releaseFirst = resolve; });
    const firstDispatch = new Promise(resolve => { firstStarted = resolve; });
    const dispatches = [];

    globalThis.fetch = async (url, init = {}) => {
        if (url === "/api/tt/session") {
            return jsonResponse({
                ok: true,
                sessionId: "ordered-session",
                generation: 1,
                protocolVersion: 1
            }, 201);
        }

        assert.equal(url, "/api/tt/rpc");
        const body = JSON.parse(init.body);
        const label = body.request.label ?? body.request.kind;
        dispatches.push(`${body.channel}:${label}`);
        if (body.channel === "core" && label === "first") {
            firstStarted();
            await firstGate;
        }
        return jsonResponse({ ok: true, result: { ok: true }, generation: 1 });
    };

    const transport = new TTProcessTransport();
    await transport.request("core", { kind: "configure", config: {}, definitions: [] });
    await transport.request("assist", { kind: "configure", config: {}, definitions: [] });
    dispatches.length = 0;

    const first = transport.request("core", { kind: "validate", label: "first" });
    await firstDispatch;
    const second = transport.request("core", { kind: "validate", label: "second" });

    await transport.request("assist", { kind: "clear" });
    await new Promise(resolve => setTimeout(resolve, 0));
    assert.deepEqual(dispatches, ["core:first", "assist:clear"],
        "a later core mutation overtook an in-flight validation");

    releaseFirst();
    await Promise.all([first, second]);
    assert.deepEqual(dispatches, ["core:first", "assist:clear", "core:second"],
        "same-channel process requests were not dispatched in call order");
}

async function resetCancelsQueuedMutations() {
    let releaseFirst;
    let firstStarted;
    let generation = 1;
    const firstGate = new Promise(resolve => { releaseFirst = resolve; });
    const firstDispatch = new Promise(resolve => { firstStarted = resolve; });
    const dispatches = [];

    globalThis.fetch = async (url, init = {}) => {
        if (url === "/api/tt/session") {
            return jsonResponse({
                ok: true,
                sessionId: "reset-session",
                generation,
                protocolVersion: 1
            }, 201);
        }
        if (url === "/api/tt/reset") {
            dispatches.push("reset");
            generation++;
            return jsonResponse({ ok: true, generation, restarted: true });
        }

        assert.equal(url, "/api/tt/rpc");
        const body = JSON.parse(init.body);
        const label = body.request.label ?? body.request.kind;
        dispatches.push(`${body.channel}:${label}`);
        if (label === "first") {
            firstStarted();
            await firstGate;
        }
        return jsonResponse({ ok: true, result: { ok: true }, generation });
    };

    const transport = new TTProcessTransport();
    await transport.request("core", { kind: "configure", config: {}, definitions: [] });
    dispatches.length = 0;

    const first = transport.request("core", { kind: "validate", label: "first" });
    await firstDispatch;
    const stale = transport.request("core", { kind: "validate", label: "stale" })
        .then(() => null, error => error);

    transport.reset(new Error("the theorem list changed"));
    releaseFirst();
    await first;
    const staleError = await stale;
    assert.ok(staleError instanceof TTProcessExecutionError);
    assert.equal(staleError.code, "TT_PROCESS_QUEUE_CANCELLED");

    await transport.request("core", { kind: "check", label: "fresh" });
    assert.equal(dispatches.includes("core:stale"), false,
        "a queued validation from before reset reached the new process generation");
    assert.ok(dispatches.includes("reset"));
    assert.ok(dispatches.includes("core:fresh"));
}

async function pageHideCancelsQueuedMutations() {
    let releaseFirst;
    let firstStarted;
    let sessionCount = 0;
    const firstGate = new Promise(resolve => { releaseFirst = resolve; });
    const firstDispatch = new Promise(resolve => { firstStarted = resolve; });
    const dispatches = [];

    globalThis.fetch = async (url, init = {}) => {
        if (url === "/api/tt/session") {
            sessionCount++;
            return jsonResponse({
                ok: true,
                sessionId: `page-session-${sessionCount}`,
                generation: 1,
                protocolVersion: 1
            }, 201);
        }

        assert.equal(url, "/api/tt/rpc");
        const body = JSON.parse(init.body);
        const label = body.request.label ?? body.request.kind;
        dispatches.push(`${body.channel}:${label}`);
        if (label === "first") {
            firstStarted();
            await firstGate;
        }
        return jsonResponse({ ok: true, result: { ok: true }, generation: 1 });
    };

    const transport = new TTProcessTransport();
    await transport.request("core", { kind: "configure", config: {}, definitions: [] });
    dispatches.length = 0;

    const first = transport.request("core", { kind: "validate", label: "first" });
    await firstDispatch;
    const stale = transport.request("core", { kind: "validate", label: "stale" })
        .then(() => null, error => error);

    transport.disposePageSession();
    releaseFirst();
    await first;
    const staleError = await stale;
    assert.ok(staleError instanceof TTProcessExecutionError);
    assert.equal(staleError.code, "TT_PROCESS_QUEUE_CANCELLED");
    assert.equal(dispatches.includes("core:stale"), false);
    assert.equal(sessionCount, 1,
        "a hidden page recreated a process session for a stale queued request");
}

try {
    await preservesPerChannelCallOrder();
    await resetCancelsQueuedMutations();
    await pageHideCancelsQueuedMutations();
} finally {
    globalThis.fetch = originalFetch;
}

console.log("type-theory process per-channel ordering regression passed");
