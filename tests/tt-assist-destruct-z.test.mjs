import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { GameSaveLoad } from "../js/saveload.js";
import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const encoded = readFileSync(
    new URL("./fixtures/aug11-survival-save.txt", import.meta.url),
    "utf8"
).trim();
const saveLoader = Object.create(GameSaveLoad.prototype);
saveLoader.storageKey = "deductrium-save";
const [, , , ttData] = saveLoader.deserializeStr(encoded).split("-(=)-");
const savedTheorems = JSON.parse(ttData).items
    .filter(item => item.kind === "theorem")
    .map(item => item.value);
const target = "Px:Z.Py:Z.addZ (predZ x) y=predZ(addZ x y)";
const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
};
const validation = new TTCoreSession();
validation.configure(config);

const originalLog = console.log;
const originalWarn = console.warn;
try {
    console.log = () => { };
    console.warn = () => { };
    for (let index = 0; index < savedTheorems.length; index++) {
        const result = validation.validate(index, parser.parse(savedTheorems[index]));
        assert.equal(result.ok, true,
            `restored theorem ${index} must validate: ${result.error ?? "unknown error"}`);
    }

    const engine = new TTAssistEngine();
    const slots = validation.getDefinitionSlots();
    engine.configure({
        ...config,
        userDefinitions: slots.filter(Boolean).map(slot => [slot[0], Core.clone(slot[1])]),
        userDefinitionCaches: slots.filter(slot => slot?.[2]).map(slot => [slot[0], slot[2]])
    });

    const options = {
        disableMultipleApply: false,
        disableDestructConds: false,
        disableDestructEq: false
    };

    let snapshot = engine.start(target, options);
    snapshot = engine.apply("intro x");
    snapshot = engine.apply("intro y");

    const liveGoal = engine.assist.goal[0];
    const contextIds = new Set(liveGoal.context.map(([, , id]) => id).filter(Boolean));
    const pending = [liveGoal.type];
    while (pending.length) {
        const node = pending.pop();
        if (node.type === "var" && node.bondVarId) {
            assert.equal(contextIds.has(node.bondVarId), true,
                "tactic recommendation snapshots must not leave foreign binder ids in the live goal");
        }
        pending.push(...(node.nodes ?? []));
    }

    snapshot = engine.apply("destruct y");

    assert.deepEqual(
        snapshot.goals.map(goal => parser.stringify(goal.type)),
        [
            "((addZ (predZ x) 0Z)=(predZ (addZ x 0Z)))",
            "((addZ (predZ x) (pos y))=(predZ (addZ x (pos y))))",
            "((addZ (predZ x) (neg y))=(predZ (addZ x (neg y))))"
        ],
        "destruct Z must specialize the motive on the first execution"
    );
} finally {
    console.log = originalLog;
    console.warn = originalWarn;
}

console.log("proof-assistant Z destruct regression passed");
