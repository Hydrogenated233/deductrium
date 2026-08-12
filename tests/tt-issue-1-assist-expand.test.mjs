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

const originalLog = console.log;
const originalWarn = console.warn;
try {
    const recommendationLogs = [];
    console.log = (...args) => recommendationLogs.push(args.map(String).join(" "));
    console.warn = () => { };

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

    const assist = new TTAssistEngine(session.engine);
    assist.start(statements.at(-1), options);
    for (const name of ["u", "v", "a", "b", "f", "x", "y", "p", "q", "r"]) {
        assist["executeCommand"](`intro ${name}`, true);
    }

    const suggested = assist["snapshot"]().tactics;
    assert.deepEqual(
        suggested,
        [
            "rw r", "rwb r", "destruct r",
            "rw q", "rwb q", "destruct q",
            "rw p", "rwb p", "destruct p",
            "expand @ap2", "expand @trans2const", "expand @apd_ap",
            "eq"
        ],
        "the original syntax-based possibly-applicable suggestions must remain intact"
    );
    assert.deepEqual(
        recommendationLogs,
        [],
        "speculative recommendation checks must not print expected NbE failures"
    );
    for (const command of ["expand @ap2", "expand @trans2const", "expand @apd_ap"]) {
        assert.ok(suggested.includes(command), `${command} must remain a syntax-based suggestion`);
        assert.doesNotThrow(
            () => assist["executeCommand"](command, true),
            `${command} must not fail with semantic-nbe-unsupported or a resource limit`
        );
    }
    assert.equal(assist["snapshot"]().goals.length, 1,
        "the expanded issue goal must remain available for the next proof step");
} finally {
    console.log = originalLog;
    console.warn = originalWarn;
}

console.log("GitHub issue #1 proof-assistant expand regression passed");
