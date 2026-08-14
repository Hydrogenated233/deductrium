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
    new URL("./fixtures/aug13-succ-mul-survival-save.txt", import.meta.url),
    "utf8"
).trim();
const saveLoader = Object.create(GameSaveLoad.prototype);
saveLoader.storageKey = "deductrium-save";
const [, , , ttData] = saveLoader.deserializeStr(encoded).split("-(=)-");
const theoremItems = JSON.parse(ttData).items.filter(item => item.kind === "theorem");

const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    disableSimpleFn: false,
    disableSimpleEq: false,
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
};
const options = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};

// Rebuild the Z folder's real definition slots. The preceding nat folder is
// local and therefore invisible to this proof-assistant scope.
const validation = new TTCoreSession();
validation.configure(config);
const originalLog = console.log;
const originalWarn = console.warn;
try {
    console.log = () => { };
    console.warn = () => { };
    for (let index = 0; index < theoremItems.length; index++) {
        if (index !== 0 && index < 13) {
            validation.setDefinition(index, null);
            continue;
        }
        const result = validation.validate(index, parser.parse(theoremItems[index].value));
        assert.equal(result.ok, true,
            `restored Z theorem ${index} must validate: ${result.error ?? "unknown error"}`);
    }

    const slots = validation.getDefinitionSlots();
    const engine = new TTAssistEngine();
    engine.configure({
        ...config,
        userDefinitions: slots.filter(Boolean).map(slot => [slot[0], Core.clone(slot[1])]),
        userDefinitionCaches: slots.filter(slot => slot?.[2]).map(slot => [slot[0], slot[2]])
    });

    const theorem = "Πx:Z,Πy:Z,mulZ (succZ x) y=addZ (mulZ x y) y";
    let snapshot = engine.start(theorem, options);
    for (const command of [
        "intro x", "intro y", "destruct y", "rfl", "destruct y", "rfl",
        "simpl", "rw y_", "rw add_succ _ _", "rw add_left_comm _ _ _",
        "rfl", "destruct y", "simpl", "apply negZ_succZ x", "simpl",
        "rw y_", "rw negZ_succZ _", "rw add_pred _ _",
        "rw add_left_comm _ _ _", "rfl"
    ]) {
        snapshot = engine.apply(command);
    }

    assert.equal(snapshot.goals.length, 0);
    const qed = engine.qed();
    assert.equal(qed.theorem, parser.stringify(parser.parse(theorem)));

    // The emitted name:=proof:theorem form must remain acceptable to the
    // ordinary theorem validator after qed's internal binder-id cleanup.
    const registered = validation.validate(
        theoremItems.length,
        parser.parse(`succ_mul_fixed:=${qed.proof}:${qed.theorem}`)
    );
    assert.equal(registered.ok, true,
        `named qed output must register: ${registered.error ?? "unknown error"}`);
} finally {
    console.log = originalLog;
    console.warn = originalWarn;
}

console.log("qed stale-binder-id regression passed");
