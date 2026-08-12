import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";
import { createK609BenchmarkTheorems } from "./helpers/k609-workload.mjs";

const parser = new ASTParser();
const theoremValues = createK609BenchmarkTheorems(readFileSync(
    new URL("./fixtures/k609-one-formula-before-perm-master.txt", import.meta.url),
    "utf8"
));
const previous = {
    recursive: Core.semanticTypeCheckRecursive,
    recursiveMin: Core.semanticTypeCheckRecursiveMinDefinitions,
    elaborationNodes: Core.semanticTypeElaborationMaxNodes,
    outputNodes: Core.semanticTypeCheckMaxOutputNodes,
    synthesisSteps: Core.semanticTypeSynthesisMaxSteps
};
const originalLog = console.log;

try {
    console.log = () => { };
    Core.semanticTypeCheckRecursive = true;
    Core.semanticTypeCheckRecursiveMinDefinitions = 0;
    Core.semanticTypeElaborationMaxNodes = 512;
    Core.semanticTypeCheckMaxOutputNodes = 256;
    // This regression deliberately exercises a large semantic elaboration.
    // Production keeps a lower speculative budget so expensive cases can
    // fall back to the legacy checker without stalling the UI.
    Core.semanticTypeSynthesisMaxSteps = 65_536;

    const session = new TTCoreSession();
    session.configure({
        unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
        disableSimpleFn: false,
        disableSimpleEq: false,
        inferDisplayMode: "_",
        timeout: Number.MAX_SAFE_INTEGER,
        language: "zh"
    });

    for (let index = 0; index <= 78; index++) {
        const result = session.validate(index, parser.parse(theoremValues[index]));
        assert.equal(result.ok, true,
            `large semantic cache setup must preserve K609 theorem ${index}: ${result.error ?? "unknown error"}`);
        if (index === 73) {
            assert.equal(result.definitionCache?.kind, "nbe");
            const cachedType = parser.stringify(result.definitionCache.type);
            assert.match(cachedType, /restrictNotLastF_pm/,
                "semantic type output must retain compact definition aliases");
        }
        if (index === 78) {
            assert.equal(result.definitionCache?.kind, "nbe",
                "eqvComp must be accepted by the semantic definition path");
            const cachedType = parser.stringify(result.definitionCache.type);
            assert.match(cachedType, /Πe:eqv a b/,
                "semantic binder checking must keep the compact eqv domain");
            assert.match(cachedType, /Πk:eqv b c/,
                "the second compact eqv domain must survive elaboration too");
        }
    }
} finally {
    console.log = originalLog;
    Core.semanticTypeCheckRecursive = previous.recursive;
    Core.semanticTypeCheckRecursiveMinDefinitions = previous.recursiveMin;
    Core.semanticTypeElaborationMaxNodes = previous.elaborationNodes;
    Core.semanticTypeCheckMaxOutputNodes = previous.outputNodes;
    Core.semanticTypeSynthesisMaxSteps = previous.synthesisSteps;
}

console.log("large semantic definition-cache regression passed");
