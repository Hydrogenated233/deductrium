import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const statements = readFileSync(
    new URL("./fixtures/issue-1-semantic-nbe-unsupported.txt", import.meta.url),
    "utf8"
).split(/\r?\n\s*\r?\n/).map(source => source.trim()).filter(Boolean);

const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    disableSimpleFn: false,
    disableSimpleEq: false,
    inferDisplayMode: "_",
    timeout: 60_000,
    language: "zh"
};
const options = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};

const session = new TTCoreSession();
session.configure(config);
for (let index = 0; index < statements.length - 1; index++) {
    const result = session.validate(index, parser.parse(statements[index]));
    assert.equal(
        result.ok,
        true,
        `GitHub issue #1 dependency ${index} failed: ${result.error ?? "unknown error"}`
    );
}

const definitions = session.getDefinitionSlots(statements.length - 1).filter(Boolean);
const assist = new TTAssistEngine();
assist.configure({
    ...config,
    userDefinitions: definitions.map(([name, value]) => [name, value]),
    userDefinitionCaches: definitions
        .filter(([, , cache]) => !!cache)
        .map(([name, , cache]) => [name, cache])
});

const target = parser.parse(statements.at(-1));
const targetSort = assist.engine.core.checkType(target, [], false);
assert.equal(targetSort.type, "var");
assert.equal(targetSort.name, "U@:",
    "the issue target is a universe-polymorphic proposition in the external universe sort");

const snapshot = assist.start(statements.at(-1), options);
assert.equal(snapshot.goals.length, 1,
    "a valid universe-polymorphic proposition must open in the proof assistant");

assert.throws(
    () => assist.start("@0", options),
    /不是命题类型/,
    "a universe-level value itself must not be accepted as a proof target"
);

console.log("GitHub issue #1 proof-assistant universe-sort regression passed");
