import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";
import { decodeK609Theorems } from "./helpers/k609-workload.mjs";

const parser = new ASTParser();
const encoded = readFileSync(
    new URL("./fixtures/k609-one-formula-before-perm-master.txt", import.meta.url),
    "utf8"
);
const theoremValues = decodeK609Theorems(encoded).slice(0, 154);
const previousRecursiveTypecheck = Core.semanticTypeCheckRecursive;
const previousTypecheckAttempts = Core.semanticTypeCheckAttempts;
const previousTypecheckHits = Core.semanticTypeCheckHits;
const previousFastPathHits = Core.semanticTypeCheckFastPathHits;

assert.equal(theoremValues.length, 154, "K609 fixture must contain theorem index 153");

try {
    Core.semanticTypeCheckRecursive = false;

    const session = new TTCoreSession();
    session.configure({
        unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
        disableSimpleFn: false,
        disableSimpleEq: false,
        inferDisplayMode: "_",
        timeout: Number.MAX_SAFE_INTEGER,
        language: "zh"
    });

    // System initialization also performs semantic checks. Measure only the
    // restored theorem prefix so the counters describe this workload.
    Core.semanticTypeCheckAttempts = 0;
    Core.semanticTypeCheckHits = 0;
    Core.semanticTypeCheckFastPathHits = 0;

    for (let index = 0; index < theoremValues.length; index++) {
        const result = session.validate(index, parser.parse(theoremValues[index]));
        assert.equal(result.ok, true,
            `pure NbE must preserve K609 theorem ${index}: ${result.error ?? "unknown error"}`);
    }

    assert.equal(Core.semanticTypeCheckAttempts, theoremValues.length,
        "the K609 prefix must require only one root semantic attempt per theorem");
    assert.equal(Core.semanticTypeCheckHits, theoremValues.length,
        "every K609 prefix theorem must succeed on the semantic type-check path");
    assert.equal(Core.semanticTypeCheckFastPathHits, theoremValues.length,
        "every K609 prefix theorem must avoid the legacy checker");
} finally {
    Core.semanticTypeCheckRecursive = previousRecursiveTypecheck;
    Core.semanticTypeCheckAttempts = previousTypecheckAttempts;
    Core.semanticTypeCheckHits = previousTypecheckHits;
    Core.semanticTypeCheckFastPathHits = previousFastPathHits;
}

console.log("K609 pure semantic prefix regression passed");
