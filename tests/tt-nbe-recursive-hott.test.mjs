import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const statements = readFileSync(new URL("./fixtures/hott-complex.txt", import.meta.url), "utf8")
    .split(/\r?\n\s*\r?\n/)
    .map(statement => statement.trim())
    .filter(Boolean);

const previousRecursive = Core.semanticTypeCheckRecursive;
const previousMinimum = Core.semanticTypeCheckRecursiveMinDefinitions;
const previousFastPathHits = Core.semanticTypeCheckFastPathHits;

try {
    Core.semanticTypeCheckRecursive = true;
    Core.semanticTypeCheckRecursiveMinDefinitions = 0;
    Core.semanticTypeCheckFastPathHits = 0;

    const session = new TTCoreSession();
    session.configure({
        unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
        disableSimpleFn: false,
        disableSimpleEq: false,
        inferDisplayMode: "_",
        timeout: 60_000,
        language: "zh"
    });

    for (let index = 0; index < statements.length; index++) {
        const fastPathHitsBefore = Core.semanticTypeCheckFastPathHits;
        const result = session.validate(index, parser.parse(statements[index]));
        assert.equal(
            result.ok,
            true,
            `recursive semantic checking rejected HoTT statement ${index}: ${result.error ?? "unknown error"}`
        );
        assert.ok(
            Core.semanticTypeCheckFastPathHits > fastPathHitsBefore,
            `HoTT statement ${index} must bypass the legacy InferTable`
        );
    }
} finally {
    Core.semanticTypeCheckRecursive = previousRecursive;
    Core.semanticTypeCheckRecursiveMinDefinitions = previousMinimum;
    Core.semanticTypeCheckFastPathHits = previousFastPathHits;
}

console.log("recursive semantic HoTT regression passed");
