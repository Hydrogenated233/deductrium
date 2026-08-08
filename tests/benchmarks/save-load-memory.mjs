import { readFileSync } from "node:fs";

import { GameSaveLoad } from "../../js/saveload.js";
import { ASTParser } from "../../js/tt/astparser.js";
import { TTCoreSession } from "../../js/tt/core-session.js";
import { initTypeSystem } from "../../js/tt/initial.js";

const encoded = readFileSync(new URL("../fixtures/meikai-save.txt", import.meta.url), "utf8").trim();
const saveLoader = Object.create(GameSaveLoad.prototype);
saveLoader.storageKey = "deductrium-save";
const [, , , ttData] = saveLoader.deserializeStr(encoded).split("-(=)-");
const theoremValues = JSON.parse(ttData).items
    .filter(item => item.kind === "theorem")
    .map(item => item.value);

const parser = new ASTParser();
const session = new TTCoreSession();
session.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

const started = performance.now();
let peakHeap = 0;
for (let index = 0; index < theoremValues.length; index++) {
    const result = session.validate(index, parser.parse(theoremValues[index]));
    if (!result.ok) throw new Error(`theorem ${index} failed: ${result.error}`);
    peakHeap = Math.max(peakHeap, process.memoryUsage().heapUsed);
}

console.log(JSON.stringify({
    theorems: theoremValues.length,
    elapsedMs: Math.round(performance.now() - started),
    peakHeapMB: Math.round(peakHeap / 1024 / 1024)
}, null, 2));
