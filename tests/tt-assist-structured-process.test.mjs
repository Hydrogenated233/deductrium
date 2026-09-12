import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { ASTParser } from "../js/tt/astparser.js";
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
const parser = new ASTParser();
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

    const contextTarget = "Πn:nat,Πh:n=n,True→True";
    await success({ kind: "start", target: contextTarget, options });
    local.start(contextTarget, options);
    const introduced = await success({ kind: "apply", command: "intro n h keep" });
    local.apply("intro n h keep");
    const clearFailure = await rpc({ kind: "apply", command: "clear n" });
    assert.equal(clearFailure?.ok, false);
    assert.match(clearFailure.error, /依赖/);
    const reverted = await success({ kind: "apply", command: "revert n" });
    assert.deepEqual(reverted, JSON.parse(JSON.stringify(local.apply("revert n"))));
    assert.deepEqual(await success({ kind: "undo" }), introduced);
    assert.deepEqual(await success({
        kind: "start", target: contextTarget, options, history: reverted.history
    }), reverted);
    const closing = "by\n  intros\n  clear n h\n  exact keep";
    await success({ kind: "apply", command: closing });
    local.apply(closing);
    assert.deepEqual(await success({ kind: "qed" }), local.qed());

    const refineTarget = "Πf:nat→nat,Σn:nat,n=n";
    await success({ kind: "start", target: refineTarget, options });
    local.start(refineTarget, options);
    const refined = await success({ kind: "apply", command: "intro f\nrefine (succ _, _)" });
    const localRefined = local.apply("intro f\nrefine (succ _, _)");
    assert.deepEqual(refined, JSON.parse(JSON.stringify(localRefined)));
    assert.deepEqual(refined.goals.map(goal => goal.context.map(([name]) => name)),
        [["f"], ["f"]], "remaining refine holes retain their local scope");
    assert.equal(refined.goals.length, 2);
    assert.equal(parser.stringify(refined.goals[0].type), "nat");
    const invalidRefine = "refine ?named";
    const rejectedRefine = await rpc({ kind: "apply", command: invalidRefine });
    assert.equal(rejectedRefine?.ok, false);
    assert.match(rejectedRefine.error, /不支持命名孔位/);
    assert.throws(() => local.apply(invalidRefine), /不支持命名孔位/);
    const witness = await success({ kind: "apply", command: "· exact 0" });
    assert.deepEqual(witness, JSON.parse(JSON.stringify(local.apply("· exact 0"))));
    assert.equal(witness.goals.length, 1);
    assert.equal(parser.stringify(witness.goals[0].type),
        parser.stringify(parser.parseSurface("succ 0=succ 0")),
        "solving the witness updates the dependent goal across RPC");
    assert.deepEqual(await success({ kind: "undo" }), refined,
        "failed refine must not enter history or mutate the remaining goals");
    assert.deepEqual(local.undo(), localRefined);
    assert.deepEqual(await success({
        kind: "start", target: refineTarget, options, history: witness.history
    }), witness);
    local.start(refineTarget, options, witness.history);
    await success({ kind: "apply", command: "· rfl" });
    local.apply("· rfl");
    assert.deepEqual(await success({ kind: "qed" }), local.qed());

    await success({ kind: "start", target: "nat→nat", options });
    local.start("nat→nat", options);
    const lambda = await success({ kind: "apply", command: "refine λx:_.?_" });
    assert.deepEqual(lambda, JSON.parse(JSON.stringify(local.apply("refine λx:_.?_"))));
    assert.equal(lambda.goals.length, 1, "the inferred binder annotation is not a proof goal");
    assert.deepEqual(lambda.goals[0].context.map(([name, type]) => [name, parser.stringify(type)]),
        [["x", "nat"]], "the body hole retains its lambda binding");
    assert.equal(parser.stringify(lambda.goals[0].type), "nat");
    await success({ kind: "apply", command: "exact x" });
    local.apply("exact x");
    assert.deepEqual(await success({ kind: "qed" }), local.qed());

    await success({ kind: "start", target: "0=0", options });
    local.start("0=0", options);
    const inferred = await success({ kind: "apply", command: "refine refl _" });
    assert.deepEqual(inferred.goals, []);
    assert.deepEqual(inferred, JSON.parse(JSON.stringify(local.apply("refine refl _"))));
    assert.deepEqual(await success({ kind: "qed" }), local.qed());
} finally {
    await stopTTServer(server, session ? [session.sessionId] : []);
}
console.log("type-theory structured scripts isolated-process parity passed");
