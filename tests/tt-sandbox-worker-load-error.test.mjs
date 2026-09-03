import assert from "node:assert/strict";

import { SandboxEnvironment } from "../js/tt/sandbox.js";
import { SandboxWorkerSession } from "../js/tt/sandbox-worker.js";
import { SandboxWorkerClient } from "../js/tt/sandbox-worker-client.js";

const sourceEnvironment = new SandboxEnvironment();
sourceEnvironment.add("A : U");
const save = sourceEnvironment.toJSON();

// A rejected replacement save must invalidate the stateful session.  Otherwise
// a caller that omits the save on its next check can observe declarations from
// the previous creative workspace.
const session = new SandboxWorkerSession();
assert.equal(session.handle({ id: 1, kind: "load", save }).status, "ok");
assert.throws(
    () => session.handle({ id: 2, kind: "load", save: { version: 999, declarations: [] } }),
    /不支持的沙盒存档版本/
);
assert.throws(
    () => session.handle({ id: 3, kind: "check", source: "A" }),
    /尚未加载|先加载|先校验/,
    "a failed load must not expose the previous environment"
);
assert.equal(
    session.handle({ id: 4, kind: "load", save }).status,
    "ok",
    "the same worker session must recover after a failed load"
);
assert.equal(session.handle({ id: 5, kind: "check", source: "A" }).ok, true);

// Cancellation and resource exhaustion can happen after a prefix has already
// been installed.  The session must discard that partial environment too.
const interruptedSession = new SandboxWorkerSession();
const originalEnvironment = interruptedSession.environment;
let interruptedCalls = 0;
interruptedSession.environment = {
    load(saveValue, validationOptions) {
        interruptedCalls++;
        if (interruptedCalls === 1) {
            return {
                ok: false,
                status: "cancelled",
                declarations: [],
                error: "沙盒验证已取消"
            };
        }
        return originalEnvironment.load(saveValue, validationOptions);
    }
};
assert.equal(
    interruptedSession.handle({ id: 6, kind: "load", save }).status,
    "cancelled"
);
assert.throws(
    () => interruptedSession.handle({ id: 7, kind: "check", source: "A" }),
    /尚未加载|先加载|先校验/,
    "an interrupted load must revoke the partial environment"
);
assert.equal(
    interruptedSession.handle({ id: 8, kind: "load", save }).status,
    "ok",
    "a cancelled session must recover with a fresh valid load"
);

// The same reset rule applies to an explicit validation budget result.
const budgetSession = new SandboxWorkerSession();
budgetSession.environment = {
    load() {
        return {
            ok: false,
            status: "budget-exhausted",
            declarations: [],
            error: "沙盒验证资源上限"
        };
    }
};
assert.equal(
    budgetSession.handle({ id: 9, kind: "load", save }).status,
    "budget-exhausted"
);
assert.throws(
    () => budgetSession.handle({ id: 10, kind: "check", source: "A" }),
    /尚未加载|先加载|先校验/
);
assert.equal(
    budgetSession.handle({ id: 11, kind: "load", save }).status,
    "ok",
    "a budget-limited session must recover after replacing its environment"
);

// The browser client mirrors the worker's invalidation so it does not believe
// that a rejected load left a usable session behind.
class SynchronousSandboxWorker {
    constructor() {
        this.session = new SandboxWorkerSession();
        this.listeners = new Map();
    }

    addEventListener(type, listener) {
        const listeners = this.listeners.get(type) ?? [];
        listeners.push(listener);
        this.listeners.set(type, listeners);
    }

    postMessage(request) {
        try {
            const result = this.session.handle(request);
            this.emit("message", { data: { id: request.id, ok: true, result } });
        } catch (error) {
            this.emit("message", {
                data: { id: request.id, ok: false, error: String(error) }
            });
        }
    }

    terminate() {}

    emit(type, event) {
        for (const listener of this.listeners.get(type) ?? []) listener(event);
    }
}

const previousWorker = globalThis.Worker;
globalThis.Worker = SynchronousSandboxWorker;
try {
    const client = new SandboxWorkerClient();
    assert.equal((await client.load(save)).status, "ok");
    await assert.rejects(
        client.load({ version: 999, declarations: [] }),
        /不支持的沙盒存档版本/
    );
    await assert.rejects(
        client.check("A"),
        /尚未加载|先加载|先校验/,
        "the client must invalidate its ready flag after a rejected load"
    );
    assert.equal((await client.check(save, "A")).ok, true,
        "a check with the current save must rebuild after a rejected load");
    await assert.rejects(
        client.validate({ version: 999, declarations: [] }),
        /不支持的沙盒存档版本/
    );
    await assert.rejects(
        client.check("A"),
        /尚未加载|先加载|先校验/,
        "a rejected validate request must invalidate the client session too"
    );
    assert.equal((await client.load(save)).status, "ok");
    const rejectedRequest = client.validateRequest({ version: 999, declarations: [] });
    await assert.rejects(
        rejectedRequest.promise,
        /不支持的沙盒存档版本/
    );
    await assert.rejects(
        client.check("A"),
        /尚未加载|先加载|先校验/,
        "a rejected validateRequest must invalidate the client session too"
    );
} finally {
    if (previousWorker === undefined) delete globalThis.Worker;
    else globalThis.Worker = previousWorker;
}

console.log("sandbox worker load-error/session invalidation regression passed");
