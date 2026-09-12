import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { ASTParser } from "../js/tt/astparser.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";
import { TTProofSessionStore } from "../js/tt/proof-sessions.js";
import { SavesParser } from "../js/tt/savesparser.js";
import { jsonRequest, startTTServer, stopTTServer } from "./tt-process-test-utils.mjs";

const parser = new ASTParser();
const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_", timeout: 30_000, language: "zh"
};
const options = {
    disableMultipleApply: false, disableDestructConds: false, disableDestructEq: false
};
const target = "Πa:U,isProp([[a]])";
const commands = ["intro a", "expand isProp", "intros x y", "exact trunc x y"];
const engine = new TTAssistEngine();
engine.configure(config);
const completed = engine.start(target, options, commands);
assert.equal(completed.goals.length, 0);
const result = engine.qed();
assert.equal(result.theorem, parser.stringify(parser.parseSurface(target)));
assert.deepEqual(engine.snapshot(), completed);
assert.deepEqual(engine.qed(), result);
assert.equal(engine.undo().goals.length, 1);
const unfinished = engine.snapshot();
assert.throws(() => engine.qed(), /证明尚未完成/);
assert.deepEqual(engine.snapshot(), unfinished);
assert.throws(() => engine.apply("expand 2 isProp"), /未找到任何指定展开的项/);
assert.deepEqual(engine.snapshot(), unfinished);
engine.engine.core.withSilentErrors(() => assert.throws(() => engine.apply("exact x")));
assert.deepEqual(engine.snapshot(), unfinished);
engine.apply("exact trunc x y");
assert.deepEqual(engine.qed(), result);

// Roundtrip both GUI save-row forms and the completed proof page's replay data.
const rows = ["", "ttTruncProp"].map(name => ({
    kind: "theorem",
    value: `${name ? `${name}:=` : ""}${result.proof}:${result.theorem}`,
    local: false
}));
const sessions = new TTProofSessionStore();
sessions.openManual({ target, history: commands, script: `${commands.join("\n")}\nqed ttTruncProp` });
const saves = new SavesParser();
const saved = saves.serialize({
    serializeTheoremItems: () => rows,
    serializeProofSessions: () => sessions.serialize()
});
let restoredRows;
let restoredSessions;
saves.deserialize({
    resetProofAssistantForSaveLoad() {},
    restoreTheoremItems(value) { restoredRows = value; },
    queueProofSessionsRestore(value) { restoredSessions = value; }
}, saved);
assert.deepEqual(restoredRows, rows);
const page = TTProofSessionStore.deserialize(restoredSessions).active;
assert.deepEqual(page, sessions.active);
engine.start(page.target, options, page.history);
assert.deepEqual(engine.qed(), result);

const independent = new TTCoreEngine();
independent.configure(config);
function checkExport(value) {
    const ast = parser.parseSurface(value);
    const checked = ast.type === ":="
        ? independent.registerDefinition(ast)
        : independent.checkAst(ast);
    assert.equal(checked.ok, true, checked.error);
    assert.equal(checked.inferenceComplete, true);
}
for (const row of restoredRows) checkExport(row.value);

for (const [proposition, history] of [
    [target, ["intro a", "exact λx:[[a]].λy:[[a]].trunc x y"]],
    ["Πa:U,Πx:[[a]],Πy:[[a]],x=y", ["intros a x y", "exact trunc x y"]],
    ["Πa:U,isProp([[[[a]]]])", commands],
    ["Πu:U@,Πa:Uu,isProp([[a]])",
        ["intros u a", "expand isProp", "intros x y", "exact trunc x y"]],
    ["Πa:U,Πx:a,Πy:a,not(not([x]=[y]))",
        ["intros a x y", "expand not", "intro h", "exact h (trunc [x] [y])"]]
]) {
    engine.start(proposition, options, history);
    const exported = engine.qed();
    assert.equal(exported.theorem, parser.stringify(parser.parseSurface(proposition)));
    checkExport(`${exported.proof}:${exported.theorem}`);
}
const bad = independent.core.withSilentErrors(() =>
    independent.checkAst(parser.parseSurface("λa:U.λx:a.λy:a.trunc x y:Πa:U,isProp(a)"))
);
assert.equal(bad.ok, false, "truncation must not prove every untruncated type is a proposition");

// Exercise the actual isolated assistant process and a separate core session.
const server = await startTTServer(fileURLToPath(new URL("..", import.meta.url)));
let session;
try {
    const created = await jsonRequest(server.baseUrl, "/api/tt/session", { body: {} });
    assert.equal(created.body?.ok, true, server.output());
    session = created.body;
    const rpc = async (channel, request) => (await jsonRequest(server.baseUrl, "/api/tt/rpc", {
        body: { sessionId: session.sessionId, generation: session.generation, channel, request }
    })).body;
    const success = async (channel, request) => {
        const response = await rpc(channel, request);
        assert.equal(response?.ok, true, response?.error ?? server.output());
        return response.result;
    };
    for (const channel of ["assist", "core"]) {
        await success(channel, { kind: "configure", config, definitions: [] });
    }
    await success("assist", { kind: "start", target, options });
    for (const command of commands.slice(0, -1)) {
        await success("assist", { kind: "apply", command });
    }
    const failed = await rpc("assist", { kind: "qed" });
    assert.equal(failed.ok, false);
    assert.match(failed.error, /证明尚未完成/);
    const finished = await success("assist", { kind: "apply", command: commands.at(-1) });
    assert.equal(finished.goals.length, 0);
    assert.deepEqual(await success("assist", { kind: "qed" }), result);
    // Reconfiguration restores the persisted page through the same history path.
    await success("assist", { kind: "configure", config, definitions: [] });
    await success("assist", { kind: "start", target: page.target, options, history: page.history });
    assert.deepEqual(await success("assist", { kind: "qed" }), result);
    for (const [index, row] of restoredRows.entries()) {
        const checked = await success("core", {
            kind: "validate", index, ast: parser.parseSurface(row.value)
        });
        assert.equal(checked.ok, true, checked.error);
        assert.equal(checked.inferenceComplete, true);
    }
} finally {
    await stopTTServer(server, session ? [session.sessionId] : []);
}

console.log("GitHub issue #54 truncation qed, save/replay and isolated-process regression passed");
