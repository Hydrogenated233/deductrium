import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { GameSaveLoad } from "../js/saveload.js";
import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { TTGui } from "../js/tt/gui.js";
import { initTypeSystem } from "../js/tt/initial.js";
import { TTCoreSession } from "../js/tt/core-session.js";

const encoded = readFileSync(
    new URL("./fixtures/aug11-survival-save.txt", import.meta.url),
    "utf8"
).trim();
const saveLoader = Object.create(GameSaveLoad.prototype);
saveLoader.storageKey = "deductrium-save";
const [, , , ttData] = saveLoader.deserializeStr(encoded).split("-(=)-");
const items = JSON.parse(ttData).items;

const constrainedNames = new Set([
    "what", "Fin", "code_nat", "ftr", "ftreq", "Combin", "factorial2",
    "fillList", "lastList", "firstList", "lenList", "invList", "sumList",
    "mapList", "count_0", "del_0", "joinList"
]);
const expectedNames = [
    "factorial2", "Combin", "fillList", "lastList", "firstList", "lenList",
    "invList", "sumList", "mapList", "count_0", "del_0", "joinList",
    "code_nat", "Fin"
];
const parser = new ASTParser();
const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
};
const workerSession = new TTCoreSession();
workerSession.configure(config);
const checkedNames = [];

for (const item of items) {
    if (item.kind !== "theorem") continue;
    const ast = parser.parse(item.value);
    if (ast.type !== ":=" || ast.nodes[0].type !== "var") continue;
    const name = ast.nodes[0].name;
    if (!constrainedNames.has(name)) continue;

    const result = workerSession.validate(checkedNames.length, ast);
    assert.equal(result.ok, true, `${name}: ${result.error ?? "validation failed"}`);
    checkedNames.push(name);

    // Rebuild the UI-side Core from the portable definitions and caches that
    // cross the Worker boundary. Puzzle validation runs on this Core.
    const slots = workerSession.getDefinitionSlots();
    const uiEngine = new TTCoreEngine();
    uiEngine.configure({
        ...config,
        userDefinitions: slots.filter(Boolean).map(slot => [slot[0], slot[1]]),
        userDefinitionCaches: slots.filter(slot => slot?.[2]).map(slot => [slot[0], slot[2]])
    });
    const gui = Object.create(TTGui.prototype);
    gui.core = uiEngine.core;
    gui.disableSimpleFn = false;
    gui.disableSimpleEq = false;
    gui.settlePendingTheorems = () => { };
    gui.getHottDefCtxt = () => { };
    gui.getInhabitatArray = () => slots;
    const originalCheckType = gui.core.checkType.bind(gui.core);
    gui.core.checkType = (...args) => {
        assert.equal(
            gui.core.state.disableSimpleFn,
            gui.disableSimpleFn,
            "puzzle checks must synchronize the function-syntax setting"
        );
        assert.equal(
            gui.core.state.disableSimpleEq,
            gui.disableSimpleEq,
            "puzzle checks must synchronize the equality-syntax setting"
        );
        return originalCheckType(...args);
    };

    const originalRandom = Math.random;
    try {
        for (const randomValue of [0.1, 0.9]) {
            Math.random = () => randomValue;
            // Puzzle checks must use the GUI's current syntax settings rather
            // than whichever state a previous main-thread operation left on
            // the Core. `mapList` exposes this when function simplification is
            // accidentally left disabled during a restored-save validation.
            gui.core.state.disableSimpleFn = true;
            gui.core.state.disableSimpleEq = true;
            assert.equal(
                gui.queryDefPuzzle(name),
                true,
                `${name} must satisfy its survival-mode puzzle after Worker cache restore`
            );
        }
    } finally {
        Math.random = originalRandom;
    }
}

assert.deepEqual(checkedNames, expectedNames);
console.log("survival save puzzle-definition regression passed");
