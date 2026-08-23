import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const statements = readFileSync(
    new URL("./fixtures/issue-5-resource-limit.txt", import.meta.url),
    "utf8"
).trim().split(/\r?\n\s*\r?\n/).map(source => source.trim()).filter(Boolean);
const unlockedTypes = [...new Set(initTypeSystem().map(rule => rule.id))];
const previous = {
    timeout: Core.timeout,
    timeoutOccured: Core.timeoutOccured,
    scale: Core.semanticResourceScale,
    nbeMaxNodes: Core.semanticNbEMaxNodes,
    elaborationMaxNodes: Core.semanticTypeElaborationMaxNodes,
    synthesisMaxSteps: Core.semanticTypeSynthesisMaxSteps,
    assertionMaxSteps: Core.semanticTypeAssertionMaxSteps,
    assertionMaxNodes: Core.semanticTypeAssertionMaxNodes,
    outputMaxNodes: Core.semanticTypeCheckMaxOutputNodes
};
const originalConsoleLog = console.log;

function createSession(semanticResourceScale) {
    const session = new TTCoreSession();
    session.configure({
        unlockedTypes,
        disableSimpleFn: false,
        disableSimpleEq: false,
        inferDisplayMode: "_",
        timeout: 60_000,
        semanticResourceScale,
        language: "zh"
    });
    return session;
}

function prepareIssueFixture(semanticResourceScale) {
    const session = createSession(semanticResourceScale);
    for (let index = 0; index < statements.length - 1; index++) {
        const result = session.validate(index, parser.parse(statements[index]));
        assert.equal(
            result.ok,
            true,
            `GitHub issue #5 prerequisite ${index} failed: ${result.error ?? "unknown error"}`
        );
    }
    return session;
}

function runIssueFixture(semanticResourceScale) {
    const session = prepareIssueFixture(semanticResourceScale);
    return session.validate(
        statements.length - 1,
        parser.parse(statements[statements.length - 1])
    );
}

function runIssueAssistAssertion(semanticResourceScale) {
    const session = prepareIssueFixture(semanticResourceScale);
    const assertion = parser.parse(statements[statements.length - 1]).nodes[1];
    try {
        session.engine.core.checkType(assertion, [], true, undefined, false, true);
        return { ok: true };
    } catch (error) {
        return { ok: false, error: String(error) };
    }
}

function countAstNodes(ast) {
    const stack = [ast];
    let count = 0;
    while (stack.length) {
        const node = stack.pop();
        if (!node) continue;
        count++;
        for (const child of node.nodes ?? []) stack.push(child);
    }
    return count;
}

try {
    console.log = () => { };

    const defaultResult = runIssueFixture(1);
    assert.equal(defaultResult.ok, false,
        "GitHub issue #5 must reproduce at the default finite resource boundary");
    assert.match(defaultResult.error ?? "", /类型推断资源超限/,
        "the default boundary must retain its explicit Chinese resource error");
    assert.equal(defaultResult.timeout, false,
        "the issue is a semantic node budget, not a wall-clock timeout");

    const raisedResult = runIssueFixture(2);
    assert.equal(
        raisedResult.ok,
        true,
        `GitHub issue #5 explicit assertion must pass at 2x resources: ${raisedResult.error ?? "unknown error"}`
    );
    assert.equal(Core.semanticResourceScale, 2);
    assert.equal(Core.semanticTypeAssertionMaxNodes, 4_096,
        "Worker/session configuration must scale the explicit-assertion node boundary");
    assert.equal(Core.semanticTypeAssertionMaxSteps, 262_144,
        "the same setting must scale semantic evaluation work as one bounded resource policy");

    const assistResult = runIssueAssistAssertion(2);
    assert.equal(
        assistResult.ok,
        true,
        `proof-assistant semantic assertions must use the same source budget: ${assistResult.error}`
    );

    const sugarSession = createSession(1);
    let productType = "True";
    let productValue = "true";
    for (let index = 0; index < 26; index++) {
        productType = `(True×${productType})`;
        productValue = `(true,${productValue})`;
    }
    const productAssertion = parser.parse(
        `((λx:${productType}.true) ${productValue}):True`
    );
    const productKernel = sugarSession.engine.core.desugar(
        Core.clone(productAssertion),
        true
    );
    assert.ok(countAstNodes(productAssertion.nodes[0]) <= 128);
    assert.ok(countAstNodes(productKernel.nodes[0]) > 256,
        "the regression must exceed the former fixed 2x desugaring allowance");
    Core.semanticTypeAssertionMaxNodes = 128;
    assert.doesNotThrow(
        () => sugarSession.engine.core.checkType(productAssertion, [], false),
        "trusted product/tuple desugaring must not consume the user's source budget"
    );

    let truncTerm = "true";
    let truncType = "True";
    for (let index = 0; index < 4; index++) {
        truncTerm = `[ ${truncTerm} ]`;
        truncType = `[[ ${truncType} ]]`;
    }
    const truncAssertion = parser.parse(`${truncTerm}:${truncType}`);
    const truncKernel = sugarSession.engine.core.desugar(Core.clone(truncAssertion), true);
    assert.ok(countAstNodes(truncAssertion.nodes[0]) <= 8);
    assert.ok(countAstNodes(truncKernel.nodes[0]) > 16,
        "nested truncation must also exceed the former fixed 2x allowance");
    Core.semanticTypeAssertionMaxNodes = 8;
    assert.doesNotThrow(
        () => sugarSession.engine.core.checkType(truncAssertion, [], false),
        "trusted truncation desugaring must not consume the user's source budget"
    );

    Core.setSemanticResourceScale(10_000);
    assert.equal(Core.semanticResourceScale, Core.semanticResourceScaleMax,
        "user-controlled resource scaling must retain a finite upper bound");
} finally {
    console.log = originalConsoleLog;
    Core.timeout = previous.timeout;
    Core.timeoutOccured = previous.timeoutOccured;
    Core.semanticResourceScale = previous.scale;
    Core.semanticNbEMaxNodes = previous.nbeMaxNodes;
    Core.semanticTypeElaborationMaxNodes = previous.elaborationMaxNodes;
    Core.semanticTypeSynthesisMaxSteps = previous.synthesisMaxSteps;
    Core.semanticTypeAssertionMaxSteps = previous.assertionMaxSteps;
    Core.semanticTypeAssertionMaxNodes = previous.assertionMaxNodes;
    Core.semanticTypeCheckMaxOutputNodes = previous.outputMaxNodes;
}

originalConsoleLog("GitHub issue #5 resource-limit regression passed");
