import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { GameSaveLoad } from "../js/saveload.js";
import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const encoded = readFileSync(
    new URL("./fixtures/aug11-survival-save.txt", import.meta.url),
    "utf8"
).trim();
const saveLoader = Object.create(GameSaveLoad.prototype);
saveLoader.storageKey = "deductrium-save";
const [, , , ttData] = saveLoader.deserializeStr(encoded).split("-(=)-");
const theoremValues = JSON.parse(ttData).items
    .filter(item => item.kind === "theorem")
    .map(item => item.value);
const targetIndex = theoremValues.indexOf("S1_U base===Bool");
assert.equal(targetIndex, 76);
assert.equal(theoremValues.length, 125);

const previousRecursive = Core.semanticTypeCheckRecursive;
const previousMinimum = Core.semanticTypeCheckRecursiveMinDefinitions;
const parser = new ASTParser();
const session = new TTCoreSession();

try {
    Core.semanticTypeCheckRecursive = true;
    Core.semanticTypeCheckRecursiveMinDefinitions = 0;
    session.configure({
        unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
        inferDisplayMode: "_",
        timeout: 60_000,
        language: "zh"
    });

    const core = session.engine.core;
    for (let index = 0; index < theoremValues.length; index++) {
        const ast = parser.parse(theoremValues[index]);
        const result = session.validate(index, ast);
        assert.equal(
            result.ok,
            true,
            `theorem ${index} left pure NbE: ${result.error ?? "unknown error"}`
        );
    }
} finally {
    Core.semanticTypeCheckRecursive = previousRecursive;
    Core.semanticTypeCheckRecursiveMinDefinitions = previousMinimum;
}

console.log("pure NbE August 11 survival-save regression passed");
