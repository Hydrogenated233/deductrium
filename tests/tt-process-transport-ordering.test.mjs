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

    const first = transport.request("core", { kind: "validate", label: "first" })
        .then(() => null, error => error);
    await firstDispatch;
    const stale = transport.request("core", { kind: "validate", label: "stale" })
        .then(() => null, error => error);

    transport.reset(new Error("the theorem list changed"));
    releaseFirst();
    const firstError = await first;
    assert.ok(firstError instanceof TTProcessExecutionError);
    assert.equal(firstError.code, "TT_PROCESS_QUEUE_CANCELLED");
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

    const first = transport.request("core", { kind: "validate", label: "first" })
        .then(() => null, error => error);
    await firstDispatch;
    const stale = transport.request("core", { kind: "validate", label: "stale" })
        .then(() => null, error => error);

    transport.disposePageSession();
    releaseFirst();
    const firstError = await first;
    assert.ok(firstError instanceof TTProcessExecutionError);
    assert.equal(firstError.code, "TT_PROCESS_QUEUE_CANCELLED");
    const staleError = await stale;
    assert.ok(staleError instanceof TTProcessExecutionError);
    assert.equal(staleError.code, "TT_PROCESS_QUEUE_CANCELLED");
    assert.equal(dispatches.includes("core:stale"), false);
    assert.equal(sessionCount, 1,
        "a hidden page recreated a process session for a stale queued request");
}

async function resetCancelsMutationAlreadyWaitingForReset() {
    let releaseFirstReset;
    let firstResetStarted;
    let generation = 1;
    let resetCount = 0;
    const firstResetGate = new Promise(resolve => { releaseFirstReset = resolve; });
    const firstResetDispatch = new Promise(resolve => { firstResetStarted = resolve; });
    const dispatches = [];

    globalThis.fetch = async (url, init = {}) => {
        if (url === "/api/tt/session") {
            return jsonResponse({
                ok: true,
                sessionId: "waiting-reset-session",
                generation,
                protocolVersion: 1
            }, 201);
        }
        if (url === "/api/tt/reset") {
            resetCount++;
            dispatches.push(`reset:${resetCount}`);
            if (resetCount === 1) {
                firstResetStarted();
                await firstResetGate;
            }
            generation++;
            return jsonResponse({ ok: true, generation, restarted: true });
        }

        assert.equal(url, "/api/tt/rpc");
        const body = JSON.parse(init.body);
        dispatches.push(`${body.channel}:${body.request.label ?? body.request.kind}`);
        return jsonResponse({ ok: true, result: { ok: true }, generation });
    };

    const transport = new TTProcessTransport();
    await transport.request("core", { kind: "configure", config: {}, definitions: [] });
    dispatches.length = 0;

    transport.reset(new Error("first reset"));
    await firstResetDispatch;
    const stale = transport.request("core", { kind: "validate", label: "stale-after-await" })
        .then(() => null, error => error);
    await new Promise(resolve => setTimeout(resolve, 0));

    transport.reset(new Error("second reset"));
    releaseFirstReset();
    const staleError = await stale;
    assert.ok(staleError instanceof TTProcessExecutionError);
    assert.equal(staleError.code, "TT_PROCESS_QUEUE_CANCELLED");

    await transport.request("core", { kind: "check", label: "fresh-after-resets" });
    assert.equal(dispatches.includes("core:stale-after-await"), false,
        "a request already awaiting the first reset crossed the second reset epoch");
    assert.deepEqual(dispatches.filter(value => value.startsWith("reset:")), ["reset:1", "reset:2"]);
}

async function pageHideCancelsSessionCreationInFlight() {
    let releaseSession;
    let sessionStarted;
    const sessionGate = new Promise(resolve => { releaseSession = resolve; });
    const sessionDispatch = new Promise(resolve => { sessionStarted = resolve; });
    const rpcDispatches = [];
    const disposedSessions = [];

    globalThis.fetch = async (url, init = {}) => {
        if (url === "/api/tt/session") {
            sessionStarted();
            await sessionGate;
            return jsonResponse({
                ok: true,
                sessionId: "pagehide-creating-session",
                generation: 1,
                protocolVersion: 1
            }, 201);
        }
        if (url === "/api/tt/dispose") {
            disposedSessions.push(JSON.parse(init.body).sessionId);
            return jsonResponse({ ok: true });
        }

        assert.equal(url, "/api/tt/rpc");
        const body = JSON.parse(init.body);
        rpcDispatches.push(body.request.kind);
        return jsonResponse({ ok: true, result: { ok: true }, generation: 1 });
    };

    const transport = new TTProcessTransport();
    const stale = transport.request("core", { kind: "configure", config: {}, definitions: [] })
        .then(() => null, error => error);
    await sessionDispatch;

    transport.disposePageSession();
    releaseSession();
    const staleError = await stale;
    assert.ok(staleError instanceof TTProcessExecutionError);
    assert.equal(staleError.code, "TT_PROCESS_QUEUE_CANCELLED");
    assert.deepEqual(rpcDispatches, [], "a hidden page continued into RPC after session creation");
    assert.deepEqual(disposedSessions, ["pagehide-creating-session"],
        "a session created after pagehide was not disposed");
}

async function timeoutPreservesTheInitiatingError() {
    let resetStarted;
    const resetSeen = new Promise(resolve => { resetStarted = resolve; });
    globalThis.fetch = async (url, init = {}) => {
        if (url === "/api/tt/session") {
            return jsonResponse({
                ok: true,
                sessionId: "timeout-session",
                generation: 1,
                protocolVersion: 1
            }, 201);
        }
        if (url === "/api/tt/reset") {
            resetStarted();
            return jsonResponse({ ok: true, generation: 2, restarted: true });
        }

        assert.equal(url, "/api/tt/rpc");
        const body = JSON.parse(init.body);
        if (body.request.kind === "configure") {
            return jsonResponse({ ok: true, generation: 1 });
        }
        return new Promise((resolve, reject) => {
            const signal = init.signal;
            if (signal?.aborted) {
                reject(signal.reason);
                return;
            }
            signal?.addEventListener("abort", () => reject(signal.reason), { once: true });
        });
    };

    const transport = new TTProcessTransport();
    await transport.request("core", { kind: "configure", config: {}, definitions: [] });
    const error = await transport.request("core", { kind: "check", input: "slow" }, 1)
        .then(() => null, reason => reason);
    assert.ok(error instanceof TTProcessExecutionError);
    assert.equal(error.code, "TT_PROCESS_TIMEOUT",
        "the request which timed out was overwritten by queue-cancelled");
    await resetSeen;
}

try {
    await preservesPerChannelCallOrder();
    await resetCancelsQueuedMutations();
    await pageHideCancelsQueuedMutations();
    await resetCancelsMutationAlreadyWaitingForReset();
    await pageHideCancelsSessionCreationInFlight();
    await timeoutPreservesTheInitiatingError();
} finally {
    globalThis.fetch = originalFetch;
}

console.log("type-theory process per-channel ordering regression passed");
