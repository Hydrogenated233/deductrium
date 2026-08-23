import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";

import { ASTParser } from "../../js/tt/astparser.js";
import { Core } from "../../js/tt/core.js";
import { TTCoreSession } from "../../js/tt/core-session.js";
import { initTypeSystem } from "../../js/tt/initial.js";
import { SemanticNbeTypeChecker } from "../../js/tt/nbe-checker.js";

const parser = new ASTParser();
const statements = readFileSync(
    new URL("../fixtures/issue-5-resource-limit.txt", import.meta.url),
    "utf8"
).trim().split(/\r?\n\s*\r?\n/).map(source => source.trim()).filter(Boolean);
const unlockedTypes = [...new Set(initTypeSystem().map(rule => rule.id))];
const scales = [1, 2, 3, 4, 8];

function countNodes(ast) {
    let count = 0;
    const stack = [ast];
    const seen = new WeakSet();
    while (stack.length) {
        const node = stack.pop();
        if (!node || typeof node !== "object" || seen.has(node)) continue;
        seen.add(node);
        count++;
        for (const child of node.nodes ?? []) stack.push(child);
    }
    return count;
}

function round(value) {
    return Math.round(value * 100) / 100;
}

function measureStructuredClone(ast, repetitions = 5) {
    const started = performance.now();
    for (let index = 0; index < repetitions; index++) structuredClone(ast);
    return (performance.now() - started) / repetitions;
}

function runScale(scale) {
    const session = new TTCoreSession();
    let started = performance.now();
    session.configure({
        unlockedTypes,
        disableSimpleFn: false,
        disableSimpleEq: false,
        inferDisplayMode: "_",
        timeout: 60_000,
        semanticResourceScale: scale,
        language: "zh"
    });
    const configureMs = performance.now() - started;

    started = performance.now();
    for (let index = 0; index < statements.length - 1; index++) {
        const result = session.validate(index, parser.parse(statements[index]));
        if (!result.ok) {
            throw new Error(`Issue #5 prerequisite ${index} failed: ${result.error}`);
        }
    }
    const prerequisitesMs = performance.now() - started;

    started = performance.now();
    const finalAst = parser.parse(statements.at(-1));
    const parseMs = performance.now() - started;
    const sourceAssertion = finalAst.nodes?.[1];
    const sourceTermNodes = countNodes(sourceAssertion?.nodes?.[0]);
    const sourceTypeNodes = countNodes(sourceAssertion?.nodes?.[1]);
    const structuredCloneMs = measureStructuredClone(finalAst);

    const corePrototype = Core.prototype;
    const sessionPrototype = TTCoreSession.prototype;
    const checkerPrototype = SemanticNbeTypeChecker.prototype;
    const originalAssertion = corePrototype.trySemanticTypeAssertion;
    const originalFinalize = corePrototype.finalizeSemanticResult;
    const originalRestoreCache = corePrototype.restoreDefinitionCache;
    const originalSetUserDefinition = corePrototype.setUserDefinition;
    const originalStoreDefinition = sessionPrototype.definitionFromResult;
    const originalCheck = checkerPrototype.tryCheck;
    let assertionMs = 0;
    let checkerMs = 0;
    let finalizeMs = 0;
    let restoreCacheMs = 0;
    let setUserDefinitionMs = 0;
    let storeDefinitionMs = 0;
    let assertionCalls = 0;
    let checkerCalls = 0;
    let kernelTermNodes = 0;
    let kernelTypeNodes = 0;

    corePrototype.trySemanticTypeAssertion = function (...args) {
        assertionCalls++;
        kernelTermNodes = countNodes(args[0]?.nodes?.[0]);
        kernelTypeNodes = countNodes(args[0]?.nodes?.[1]);
        const assertionStarted = performance.now();
        try {
            return originalAssertion.apply(this, args);
        } finally {
            assertionMs += performance.now() - assertionStarted;
        }
    };
    checkerPrototype.tryCheck = function (...args) {
        checkerCalls++;
        const checkerStarted = performance.now();
        try {
            return originalCheck.apply(this, args);
        } finally {
            checkerMs += performance.now() - checkerStarted;
        }
    };
    corePrototype.finalizeSemanticResult = function (...args) {
        const finalizeStarted = performance.now();
        try {
            return originalFinalize.apply(this, args);
        } finally {
            finalizeMs += performance.now() - finalizeStarted;
        }
    };
    corePrototype.restoreDefinitionCache = function (...args) {
        const restoreStarted = performance.now();
        try {
            return originalRestoreCache.apply(this, args);
        } finally {
            restoreCacheMs += performance.now() - restoreStarted;
        }
    };
    corePrototype.setUserDefinition = function (...args) {
        const definitionStarted = performance.now();
        try {
            return originalSetUserDefinition.apply(this, args);
        } finally {
            setUserDefinitionMs += performance.now() - definitionStarted;
        }
    };
    sessionPrototype.definitionFromResult = function (...args) {
        const storeStarted = performance.now();
        try {
            return originalStoreDefinition.apply(this, args);
        } finally {
            storeDefinitionMs += performance.now() - storeStarted;
        }
    };

    const attemptsBefore = Core.semanticTypeCheckAttempts;
    const hitsBefore = Core.semanticTypeCheckHits;
    const originalConsoleLog = console.log;
    console.log = () => { };
    let result;
    started = performance.now();
    try {
        result = session.validate(statements.length - 1, finalAst);
    } finally {
        console.log = originalConsoleLog;
        corePrototype.trySemanticTypeAssertion = originalAssertion;
        corePrototype.finalizeSemanticResult = originalFinalize;
        corePrototype.restoreDefinitionCache = originalRestoreCache;
        corePrototype.setUserDefinition = originalSetUserDefinition;
        sessionPrototype.definitionFromResult = originalStoreDefinition;
        checkerPrototype.tryCheck = originalCheck;
    }
    const finalMs = performance.now() - started;

    return {
        scale,
        result: result.ok ? "ok" : "resource-limit",
        configureMs: round(configureMs),
        prerequisitesMs: round(prerequisitesMs),
        parseMs: round(parseMs),
        structuredCloneMs: round(structuredCloneMs),
        finalMs: round(finalMs),
        assertionMs: round(assertionMs),
        checkerMs: round(checkerMs),
        finalizeMs: round(finalizeMs),
        storeDefinitionMs: round(storeDefinitionMs),
        setUserDefinitionMs: round(setUserDefinitionMs),
        restoreCacheMs: round(restoreCacheMs),
        postCheckMs: round(Math.max(0, finalMs - assertionMs)),
        assertionCalls,
        checkerCalls,
        semanticAttempts: Core.semanticTypeCheckAttempts - attemptsBefore,
        semanticHits: Core.semanticTypeCheckHits - hitsBefore,
        sourceTermNodes,
        kernelTermNodes,
        sourceTypeNodes,
        kernelTypeNodes,
        assertionNodeLimit: Core.semanticTypeAssertionMaxNodes,
        assertionStepLimit: Core.semanticTypeAssertionMaxSteps
    };
}

console.log("GitHub issue #5 resource-limit benchmark");
console.log("Timing values are informational only; no machine-specific threshold is asserted.");
console.table(scales.map(runScale));
