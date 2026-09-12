import assert from "node:assert/strict";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_", timeout: 30_000, language: "zh"
};
const options = {
    disableMultipleApply: false, disableDestructConds: false, disableDestructEq: false
};

function makeEngine() {
    const engine = new TTAssistEngine();
    engine.configure(config);
    return engine;
}

function ids(snapshot) {
    assert.ok(snapshot.goals.every(goal => typeof goal.id === "string" && goal.id.length));
    assert.equal(new Set(snapshot.goals.map(goal => goal.id)).size, snapshot.goals.length);
    return snapshot.goals.map(goal => [goal.id, goal.holeName]);
}

// Constructing two goals must allocate identities once. Solving the first
// goal removes it from the queue without renumbering the surviving goal.
{
    const engine = makeEngine();
    const initial = engine.start("True×nat", options);
    const constructed = engine.apply("constructor");
    ids(constructed);
    assert.equal(constructed.goals[0].id, initial.goals[0].id);
    const survivingId = constructed.goals[1].id;
    const solved = engine.apply("exact true");
    assert.equal(solved.goals[0].id, survivingId);
    assert.equal(solved.goals[0].holeName, "(?#0)",
        "legacy holeName may still be renumbered for display compatibility");
}

// Intro changes the current Goal object in place; its ID is not tied to the
// generated hole label.
{
    const engine = makeEngine();
    engine.start("True→True", options);
    const initial = engine.snapshot();
    const introduced = engine.apply("intro h");
    assert.equal(introduced.goals[0].id, initial.goals[0].id);
}

// A failed command replays the accepted prefix. The replay must reconstruct
// the same IDs and must not enter the failed command into history.
{
    const engine = makeEngine();
    engine.start("True×nat", options);
    const constructed = engine.apply("constructor");
    engine.engine.core.withSilentErrors(() => {
        assert.throws(() => engine.apply("exact 0"), /无法对类型|类型/);
        assert.throws(() => engine.apply("· have h : True := by exact true\n  exact 0"),
            /无法对类型|类型/);
    });
    assert.deepEqual(ids(engine.snapshot()), ids(constructed));
    assert.deepEqual(engine.snapshot().history, constructed.history);
    assert.equal(engine.snapshot().goals[0].id, constructed.goals[0].id);
}

// Undo and history restoration replay the same accepted commands and therefore
// preserve identities for goals that still exist.
{
    const engine = makeEngine();
    engine.start("True×nat", options);
    const constructed = engine.apply("constructor");
    const solved = engine.apply("exact true");
    const undone = engine.undo();
    assert.deepEqual(ids(undone), ids(constructed));
    assert.deepEqual(engine.start("True×nat", options, solved.history), solved);
    assert.deepEqual(ids(engine.snapshot()), ids(solved));
}

// Structured tactic execution also registers goals created or retained inside
// the focused sub-proof, while the outer sibling keeps its own identity.
{
    const engine = makeEngine();
    engine.start("Σn:nat,n=n", options);
    const constructed = engine.apply("constructor");
    const siblingId = constructed.goals[1].id;
    const focused = engine.apply("· exact 0");
    assert.equal(focused.goals.length, 1);
    assert.equal(focused.goals[0].id, siblingId);
    assert.deepEqual(engine.start("Σn:nat,n=n", options, focused.history), focused);
}

// Register between tactics, not just at snapshot time: batching commands and
// focused have blocks must allocate the same IDs as separately applied steps.
{
    const engine = makeEngine();
    const target = "True×(True×nat)";
    engine.start(target, options);
    engine.apply("constructor");
    engine.apply("exact true");
    const separate = engine.apply("constructor");
    const batched = engine.start(target, options, ["constructor\nexact true\nconstructor"]);
    assert.deepEqual(ids(batched), ids(separate));

    engine.start("True×nat", options);
    const constructed = engine.apply("constructor");
    const focused = engine.apply("· have h : True := by exact true\n  exact h");
    assert.equal(focused.goals[0].id, constructed.goals[1].id);
    assert.deepEqual(engine.undo(), constructed);
    assert.deepEqual(engine.start("True×nat", options, focused.history), focused);
}

// IDs are deterministic per createAssist and do not leak across proof starts.
{
    const engine = makeEngine();
    const first = engine.start("True", options);
    engine.apply("exact true");
    const second = engine.start("True", options);
    assert.equal(first.goals[0].id, "goal-0");
    assert.equal(second.goals[0].id, "goal-0");
}

console.log("proof-assistant goal identity regression passed");
