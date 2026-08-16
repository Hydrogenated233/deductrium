import assert from "node:assert/strict";

import {
    TTProcessExecutionError,
    TTProcessTransport,
    TTProcessUnavailableError
} from "../js/tt/process-transport.js";

const originalFetch = globalThis.fetch;

async function expectWorkerFallback(mockFetch) {
    let calls = 0;
    globalThis.fetch = async (...args) => {
        calls++;
        return mockFetch(...args);
    };
    const transport = new TTProcessTransport();
    await assert.rejects(
        () => transport.request("core", { kind: "check", input: "true" }),
        error => error instanceof TTProcessUnavailableError
    );
    assert.equal(transport.workerFallbackSelected, true);
    assert.equal(transport.processSelected, false);
    await assert.rejects(
        () => transport.request("core", { kind: "check", input: "true" }),
        error => error instanceof TTProcessUnavailableError
    );
    assert.equal(calls, 1, "the unavailable API should be probed only once");
}

try {
    await expectWorkerFallback(async () => new Response(
        JSON.stringify({ error: "Not found" }),
        { status: 404, headers: { "Content-Type": "application/json" } }
    ));

    await expectWorkerFallback(async () => {
        throw new TypeError("connection refused");
    });

    let processErrorCalls = 0;
    globalThis.fetch = async () => {
        processErrorCalls++;
        return new Response(JSON.stringify({
            ok: false,
            error: "Unable to start type-theory process",
            code: "TT_PROCESS_START_FAILED",
            protocolVersion: 1
        }), {
            status: 503,
            headers: { "Content-Type": "application/json" }
        });
    };
    const transport = new TTProcessTransport();
    for (let attempt = 0; attempt < 2; attempt++) {
        await assert.rejects(
            () => transport.request("core", { kind: "check", input: "true" }),
            error => {
                assert.ok(error instanceof TTProcessExecutionError);
                assert.equal(error.code, "TT_PROCESS_START_FAILED");
                assert.equal(error.preventSynchronousFallback, true);
                return true;
            }
        );
    }
    assert.equal(processErrorCalls, 2, "a recognized process API error should remain retryable");
    assert.equal(transport.processSelected, true);
    assert.equal(transport.workerFallbackSelected, false,
        "a TT_PROCESS_* startup error must not silently fall back to a Web Worker");
} finally {
    globalThis.fetch = originalFetch;
}

console.log("type-theory process fallback selection regression passed");
