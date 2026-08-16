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

function runIssueFixture(semanticResourceScale) {
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
    for (let index = 0; index < statements.length - 1; index++) {
        const result = session.validate(index, parser.parse(statements[index]));
        assert.equal(
            result.ok,
            true,
            `GitHub issue #5 prerequisite ${index} failed: ${result.error ?? "unknown error"}`
        );
    }
    return session.validate(
        statements.length - 1,
        parser.parse(statements[statements.length - 1])
    );
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

    const raisedResult = runIssueFixture(3);
    assert.equal(
        raisedResult.ok,
        true,
        `GitHub issue #5 must pass at 3x resources: ${raisedResult.error ?? "unknown error"}`
    );
    assert.equal(Core.semanticResourceScale, 3);
    assert.equal(Core.semanticTypeAssertionMaxNodes, 6_144,
        "Worker/session configuration must scale the explicit-assertion node boundary");
    assert.equal(Core.semanticTypeAssertionMaxSteps, 393_216,
        "the same setting must scale semantic evaluation work as one bounded resource policy");

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
