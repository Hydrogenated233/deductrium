import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { ASTParser } from "../js/tt/astparser.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const statements = readFileSync(
    new URL("./fixtures/issue-1-semantic-nbe-unsupported.txt", import.meta.url),
    "utf8"
).split(/\r?\n\s*\r?\n/).map(source => source.trim()).filter(Boolean);

const session = new TTCoreSession();
session.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    disableSimpleFn: false,
    disableSimpleEq: false,
    inferDisplayMode: "_",
    timeout: 60_000,
    language: "zh"
});

for (let index = 0; index < statements.length - 1; index++) {
    const result = session.validate(index, parser.parse(statements[index]));
    assert.equal(
        result.ok,
        true,
        `GitHub issue #1 statement ${index} failed: ${result.error ?? "unknown error"}`
    );
}

const checker = session.engine.core.semanticTypeChecker;
const originalTrySynthesize = checker.trySynthesize.bind(checker);
const elaborationAttempts = [];
checker.trySynthesize = (...args) => {
    elaborationAttempts.push({
        elaborateMetas: args[2]?.elaborateMetas,
        maxSteps: args[2]?.maxSteps
    });
    return originalTrySynthesize(...args);
};

const finalIndex = statements.length - 1;
const finalResult = session.validate(finalIndex, parser.parse(statements[finalIndex]));
assert.equal(
    finalResult.ok,
    true,
    `GitHub issue #1 statement ${finalIndex} failed: ${finalResult.error ?? "unknown error"}`
);
assert.deepEqual(
    elaborationAttempts.map(attempt => attempt.elaborateMetas),
    [false, true],
    "a complete term that references hole-bearing definitions must retry with definition elaboration"
);
assert.equal(
    elaborationAttempts[1].maxSteps,
    elaborationAttempts[0].maxSteps * 4,
    "the rare hidden-definition retry must remain bounded by the configured synthesis budget"
);

const assist = new TTAssistEngine(session.engine);
const snapshot = assist.start(statements[finalIndex], {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
});
assert.equal(snapshot.goals.length, 1,
    "a universe-polymorphic proposition accepted by the core must open in the proof assistant");
assert.throws(
    () => assist.start("@0", {
        disableMultipleApply: false,
        disableDestructConds: false,
        disableDestructEq: false
    }),
    /不是命题类型/,
    "a universe-level term must not be accepted as a proposition"
);

console.log("GitHub issue #1 semantic NbE regression passed");
