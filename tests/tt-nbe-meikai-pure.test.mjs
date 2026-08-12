import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { GameSaveLoad } from "../js/saveload.js";
import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const encoded = readFileSync(
    new URL("./fixtures/meikai-save.txt", import.meta.url),
    "utf8"
).trim();
const saveLoader = Object.create(GameSaveLoad.prototype);
saveLoader.storageKey = "deductrium-save";
const ttData = saveLoader.deserializeStr(encoded).split("-(=)-")[3];
const theoremValues = JSON.parse(ttData).items
    .filter(item => item.kind === "theorem")
    .map(item => item.value);

assert.equal(theoremValues.length, 63);

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
        const name = ast.nodes?.[0]?.name ?? `theorem-${index}`;
        const fastPathHitsBefore = Core.semanticTypeCheckFastPathHits;
        const result = session.validate(index, ast);
        assert.equal(
            result.ok,
            true,
            `meikai theorem ${index} (${name}) left the pure NbE path: ${result.error ?? "unknown error"}`
        );
        assert.ok(
            Core.semanticTypeCheckFastPathHits > fastPathHitsBefore,
            `meikai theorem ${index} (${name}) must use semantic root checking`
        );
}

console.log("pure semantic meikai save regression passed");
