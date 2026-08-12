import assert from "node:assert/strict";

import { Core } from "../js/tt/core.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

const core = engine.core;
const originalConsoleLog = console.log;

function assertPureSemanticBudgetFailure(source, label) {
    const result = engine.check(source);
    assert.equal(result.ok, false, `${label} must stop at the semantic resource boundary`);
    assert.match(result.error ?? "", /类型推断(?:超时|.*(?:资源|复杂度|超限))/,
        `${label} must report a clear Chinese semantic resource error`);
}

try {
    console.log = () => { };
    for (const [source, label] of [
        ["succ(".repeat(255) + "0" + ")".repeat(255),
            "a term at the semantic input-node boundary"],
        ["λx:True.".repeat(127) + "true",
            "a synthesized type at the semantic output-node boundary"]
    ]) {
        const result = engine.check(source);
        assert.equal(result.ok, true, `${label} must still use pure NbE successfully`);
    }

    assertPureSemanticBudgetFailure(
        "succ(".repeat(256) + "0" + ")".repeat(256),
        "a term beyond the semantic input-node budget"
    );
    assertPureSemanticBudgetFailure(
        "λx:True.".repeat(128) + "true",
        "a synthesized type beyond the semantic output-node budget"
    );

    const originalMaxSteps = Core.semanticTypeSynthesisMaxSteps;
    try {
        Core.semanticTypeSynthesisMaxSteps = 1;
        assertPureSemanticBudgetFailure(
            "succ 0",
            "a term beyond the semantic evaluation-step budget"
        );
    } finally {
        Core.semanticTypeSynthesisMaxSteps = originalMaxSteps;
    }

    const originalAssertionMaxSteps = Core.semanticTypeAssertionMaxSteps;
    try {
        Core.semanticTypeAssertionMaxSteps = 1;
        assertPureSemanticBudgetFailure(
            "true:True",
            "a type assertion beyond the semantic evaluation-step budget"
        );
        assertPureSemanticBudgetFailure(
            "true===true",
            "a definitional equality beyond the semantic evaluation-step budget"
        );
    } finally {
        Core.semanticTypeAssertionMaxSteps = originalAssertionMaxSteps;
    }

    const originalTimeout = Core.timeout;
    try {
        Core.timeout = 0;
        const result = engine.check("succ 0");
        assert.equal(result.ok, false,
            "an expired semantic deadline must stop type synthesis");
        assert.match(result.error ?? "", /类型推断(?:超时|.*(?:资源|复杂度|超限))/,
            "an expired semantic deadline must report a clear Chinese resource error");
        assert.equal(result.timeout, true,
            "an expired semantic deadline must retain the public timeout signal");
    } finally {
        Core.timeout = originalTimeout;
    }
} finally {
    console.log = originalConsoleLog;
}

originalConsoleLog("pure NbE budget-boundary regression passed");
