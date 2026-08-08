import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { GameSaveLoad } from "../js/saveload.js";
import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

// This is a real save that used to make the browser heap grow into the GB
// range while its 63 theorem bodies were revalidated in order.
const encoded = readFileSync(new URL("./fixtures/meikai-save.txt", import.meta.url), "utf8").trim();
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

for (let index = 0; index < theoremValues.length; index++) {
    const ast = parser.parse(theoremValues[index]);
    const result = session.validate(index, ast);
    assert.equal(result.ok, true, `theorem ${index} failed: ${result.error ?? "unknown error"}`);
}

assert.equal(theoremValues.length, 63);
console.log("large save theorem revalidation regression passed");
