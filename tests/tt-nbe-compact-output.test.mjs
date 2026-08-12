import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";
import { createK609BenchmarkTheorems } from "./helpers/k609-workload.mjs";

const parser = new ASTParser();
const theorem = createK609BenchmarkTheorems(readFileSync(
    new URL("./fixtures/k609-one-formula-before-perm-master.txt", import.meta.url),
    "utf8"
))[0];
const previous = {
    recursive: Core.semanticTypeCheckRecursive,
    recursiveMin: Core.semanticTypeCheckRecursiveMinDefinitions,
    elaborationNodes: Core.semanticTypeElaborationMaxNodes,
    outputNodes: Core.semanticTypeCheckMaxOutputNodes
};

try {
    Core.semanticTypeCheckRecursive = true;
    Core.semanticTypeCheckRecursiveMinDefinitions = 0;
    Core.semanticTypeElaborationMaxNodes = 512;
    Core.semanticTypeCheckMaxOutputNodes = 64;

    const session = new TTCoreSession();
    session.configure({
        unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
        disableSimpleFn: false,
        disableSimpleEq: false,
        inferDisplayMode: "_",
        timeout: Number.MAX_SAFE_INTEGER,
        language: "zh"
    });

    const result = session.validate(0, parser.parse(theorem));
    assert.equal(result.ok, true, result.error ?? "K609 theorem 0 must validate");
    assert.equal(result.definitionCache?.kind, "nbe",
        "a 57-node alias-folded type must produce a native semantic cache");
    assert.doesNotMatch(parser.stringify(result.definitionCache.type), /@eq|@pair/,
        "semantic caches must fold elaboration-only prefixes to their internal public aliases");
    assert.doesNotMatch(parser.stringify(result.ast), /@eq|@pair/,
        "budget accounting must not replace the user's surface proof with explicit kernel aliases");
} finally {
    Core.semanticTypeCheckRecursive = previous.recursive;
    Core.semanticTypeCheckRecursiveMinDefinitions = previous.recursiveMin;
    Core.semanticTypeElaborationMaxNodes = previous.elaborationNodes;
    Core.semanticTypeCheckMaxOutputNodes = previous.outputNodes;
}

console.log("compact semantic type output regression passed");
