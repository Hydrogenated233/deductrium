import assert from "node:assert/strict";

import { Core } from "../js/tt/core.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { SandboxEnvironment } from "../js/tt/sandbox.js";
import { SandboxWorkerSession } from "../js/tt/sandbox-worker.js";
import {
    SandboxWorkerCancelledError,
    SandboxWorkerClient
} from "../js/tt/sandbox-worker-client.js";

const sourceEnvironment = new SandboxEnvironment();
sourceEnvironment.add("A : U");
sourceEnvironment.add("a : A");
const save = sourceEnvironment.toJSON();

const budgetSession = new SandboxWorkerSession();
const budgetResult = budgetSession.handle({
    id: 1,
    kind: "load",
    save,
    options: { validationMaxDeclarations: 1 }
});
assert.equal(budgetResult.ok, false);
assert.equal(budgetResult.status, "budget-exhausted");
assert.match(budgetResult.error, /声明数量/);
assert.equal(budgetResult.bridge, undefined,
    "a budget failure must never publish a partial trusted bridge");
assert.throws(
    () => budgetSession.handle({ id: 2, kind: "check", source: "A" }),
    /尚未加载|先加载|先校验/,
    "a worker must require a fresh load after a bounded validation"
);

const nodeBudgetSession = new SandboxWorkerSession();
const nodeBudgetResult = nodeBudgetSession.handle({
    id: 3,
    kind: "load",
    save,
    options: { validationMaxNodes: 1 }
});
assert.equal(nodeBudgetResult.status, "budget-exhausted");
assert.match(nodeBudgetResult.error, /语法节点|资源上限/);

const timeBudgetSession = new SandboxWorkerSession();
const timeBudgetResult = timeBudgetSession.handle({
    id: 31,
    kind: "load",
    save,
    options: { validationTimeoutMs: 0 }
});
assert.equal(timeBudgetResult.status, "budget-exhausted");
assert.match(timeBudgetResult.error, /时间预算|资源上限/);

// A sandbox Worker owns a separate Core instance. Its validation timeout must
// override a short game-wide Core timeout without mutating that global value.
const previousCoreTimeout = Core.timeout;
try {
    Core.timeout = 0;
    const isolatedTimeoutEnvironment = new SandboxEnvironment({
        validationTimeoutMs: 5_000
    });
    const isolatedTimeoutResult = isolatedTimeoutEnvironment.add("ScopedTimeoutA : U");
    assert.equal(isolatedTimeoutResult.ok, true, isolatedTimeoutResult.error);
    assert.equal(Core.timeout, 0,
        "sandbox validation must not leak its local timeout into the game Core");
} finally {
    Core.timeout = previousCoreTimeout;
}

const deadlineEngine = new TTCoreEngine();
deadlineEngine.configure({ unlockedTypes: ["True"] });
const expired = deadlineEngine.core.withTimeoutBudget(
    5_000,
    Date.now() - 1,
    () => deadlineEngine.check("true : True")
);
assert.equal(expired.ok, false);
assert.equal(expired.timeout, true,
    "an absolute sandbox deadline must stop nested Core checks without restarting the budget");
assert.equal(deadlineEngine.check("true : True").ok, true,
    "the request deadline must be restored after the bounded operation finishes");

const cancelledSession = new SandboxWorkerSession();
cancelledSession.cancel(4);
assert.throws(
    () => cancelledSession.handle({ id: 4, kind: "load", save }),
    /沙盒验证已取消/,
    "a request cancelled before it starts must not mutate the session"
);

class DelayedSandboxWorker {
    static instances = [];
    listeners = new Map();
    session = new SandboxWorkerSession();
    terminated = false;

    constructor() {
        DelayedSandboxWorker.instances.push(this);
    }

    addEventListener(type, listener) {
        const listeners = this.listeners.get(type) ?? [];
        listeners.push(listener);
        this.listeners.set(type, listeners);
    }

    postMessage(request) {
        if (this.terminated) return;
        // Hold the first validation request to model a long-running worker;
        // cancellation must reject it and discard this worker instance.
        if (request.kind === "validate" && DelayedSandboxWorker.instances.length === 1) {
            this.pending = request;
            return;
        }
        try {
            const result = this.session.handle(request);
            this.emit("message", { data: { id: request.id, ok: true, result } });
        } catch (error) {
            this.emit("message", { data: { id: request.id, ok: false, error: String(error) } });
        }
    }

    terminate() {
        this.terminated = true;
    }

    emit(type, event) {
        for (const listener of this.listeners.get(type) ?? []) listener(event);
    }
}

const previousWorker = globalThis.Worker;
globalThis.Worker = DelayedSandboxWorker;
try {
    const client = new SandboxWorkerClient();
    const task = client.validateRequest(save);
    assert.equal(task.requestId, 1);
    assert.equal(task.cancel(), true);
    await assert.rejects(task.promise, error => error instanceof SandboxWorkerCancelledError);
    assert.equal(DelayedSandboxWorker.instances[0].terminated, true,
        "cancelling an in-flight validation must terminate the synchronous worker");

    const recovered = await client.check(save, "A");
    assert.equal(recovered.ok, true,
        "the client must rebuild the sandbox from the supplied save after cancellation");
} finally {
    if (previousWorker === undefined) delete globalThis.Worker;
    else globalThis.Worker = previousWorker;
}

console.log("sandbox worker cancellation/resource-budget regression passed");
