import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { Assist } from "../js/tt/assist.js";
import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
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
    assert.equal(result.ok, true,
        `GitHub issue #1 dependency ${index} failed: ${result.error ?? "unknown error"}`);
}

const previousOptions = {
    disableMultipleApply: Assist.disableMultipleApply,
    disableDestructConds: Assist.disableDestructConds,
    disableDestructEq: Assist.disableDestructEq
};
const originalLog = console.log;
const originalWarn = console.warn;
try {
    console.log = () => { };
    console.warn = () => { };
    Assist.disableMultipleApply = false;
    Assist.disableDestructConds = false;
    Assist.disableDestructEq = false;

    const makeIntroducedAssist = () => {
        const assist = new Assist(session.engine.core, parser.parse(statements.at(-1)));
        for (const name of ["u", "v", "a", "b", "f", "x", "y", "p", "q", "r"]) {
            assist.intro(name);
        }
        return assist;
    };

    const recommendationAssist = makeIntroducedAssist();
    const retainedErrors = [{ ast: parser.parse("True"), msg: "retained" }];
    session.engine.core.state.errormsg = retainedErrors;
    Core.timeoutOccured = false;
    const recommendationLogs = [];
    console.log = (...args) => recommendationLogs.push(args.map(String).join(" "));
    const recommended = recommendationAssist.autofillTactics();
    assert.deepEqual(recommendationLogs, [],
        "speculative recommendation checks must not print expected failures");
    assert.equal(session.engine.core.state.errormsg, retainedErrors,
        "speculative recommendation checks must restore the caller's diagnostics");
    assert.equal(Core.timeoutOccured, false,
        "speculative recommendation checks must not leak a timeout indicator");
    console.log = () => { };
    for (const variable of ["p", "q", "r"]) {
        assert.ok(recommended.includes(`destruct ${variable}`),
            `syntax-based recommendations must retain destruct ${variable}`);

        const assist = makeIntroducedAssist();
        assert.doesNotThrow(() => assist.destruct(variable),
            `destruct ${variable} must not re-synthesize the large eliminator application`);
        assert.equal(assist.goal.length, 1);
        assert.doesNotMatch(parser.stringify(assist.goal[0].type), /\?nbe\d+/,
            "specializing the known eliminator type must solve its private semantic metas");
    }
} finally {
    Assist.disableMultipleApply = previousOptions.disableMultipleApply;
    Assist.disableDestructConds = previousOptions.disableDestructConds;
    Assist.disableDestructEq = previousOptions.disableDestructEq;
    console.log = originalLog;
    console.warn = originalWarn;
}

console.log("GitHub issue #1 proof-assistant destruct regression passed");
