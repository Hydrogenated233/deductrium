import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { GameSaveLoad } from "../js/saveload.js";
import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const encoded = readFileSync(
    new URL("./fixtures/aug11-rw-survival-save.txt", import.meta.url),
    "utf8"
).trim();
const saveLoader = Object.create(GameSaveLoad.prototype);
saveLoader.storageKey = "deductrium-save";
const [, , , ttData] = saveLoader.deserializeStr(encoded).split("-(=)-");
const theoremValues = JSON.parse(ttData).items
    .filter(item => item.kind === "theorem")
    .map(item => item.value);

assert.equal(theoremValues.length, 9);
assert.equal(theoremValues.at(-1),
    "Px:nat.Py:nat.Pz:nat.eq(add (add x y)z) (add (add x z) y)");

const parser = new ASTParser();
const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    disableSimpleFn: true,
    disableSimpleEq: true,
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
};
const validationSession = new TTCoreSession();
validationSession.configure(config);

const originalLog = console.log;
const originalWarn = console.warn;
try {
    console.log = () => { };
    console.warn = () => { };
    for (let index = 0; index < theoremValues.length - 1; index++) {
        const result = validationSession.validate(index, parser.parse(theoremValues[index]));
        assert.equal(result.ok, true,
            `restored theorem ${index} must validate: ${result.error ?? "unknown error"}`);
    }

    // Cross the same portable definition/cache boundary as the UI's validation
    // Worker -> proof-assistant Worker handoff.
    const slots = validationSession.getDefinitionSlots();
    const assist = new TTAssistEngine();
    assist.configure({
        ...config,
        userDefinitions: slots.filter(Boolean).map(slot => [slot[0], Core.clone(slot[1])]),
        userDefinitionCaches: slots.filter(slot => slot?.[2]).map(slot => [slot[0], slot[2]])
    });

    let snapshot = assist.start(theoremValues.at(-1), {
        disableMultipleApply: false,
        disableDestructConds: false,
        disableDestructEq: false
    });
    for (const command of ["intro x", "intro y", "intro z", "rw add_assoc _ _ _"]) {
        snapshot = assist.apply(command);
    }

    assert.equal(
        parser.stringify(snapshot.goals[0].type),
        "(eq (add x (add y z)) (add (add x z) y))",
        "rw add_assoc _ _ _ must infer all arguments after restoring the real survival save"
    );
    assert.match(parser.stringify(snapshot.elem), /add_assoc x y z/,
        "the inferred add_assoc arguments must be stored in the proof term");
} finally {
    console.log = originalLog;
    console.warn = originalWarn;
}

console.log("survival-save proof-assistant rewrite regression passed");
