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
    assert.equal(result.ok, true,
        `GitHub issue #1 dependency ${index} failed: ${result.error ?? "unknown error"}`);
}

const options = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};
const history = ["u", "v", "a", "b", "f", "x", "y", "p", "q", "r"]
    .map(name => `intro ${name}`);
const commands = ["rw r", "rwb r", "rw q", "rwb q", "rw p", "rwb p", "eq"];

const originalLog = console.log;
const originalWarn = console.warn;
try {
    console.log = () => { };
    console.warn = () => { };
    for (const command of commands) {
        const assist = new TTAssistEngine(session.engine);
        const snapshot = assist.start(statements.at(-1), options, history);
        assert.ok(snapshot.tactics.includes(command),
            `${command} must remain a syntax-based possibly-applicable suggestion`);
        const before = JSON.stringify(snapshot);
        if (/^rwb\s/.test(command)) {
            const after = assist.apply(command);
            assert.equal(after.goals.length, 1,
                `${command} must construct the valid reverse transport and leave its rewritten goal`);
            assert.doesNotMatch(parser.stringify(after.goals[0].type), /\?nbe\d+/,
                `${command} must not expose private semantic metas in the rewritten goal`);
        } else {
            assert.throws(() => assist.apply(command),
                /函数作用类型不匹配|类型推断无法判定类型是否相等|类型推断暂不支持/,
                `${command} must reject the ill-typed dependent transport`);
            assert.equal(JSON.stringify(assist.snapshot()), before,
                `${command} rejection must leave the proof state unchanged`);
        }
    }
} finally {
    console.log = originalLog;
    console.warn = originalWarn;
}

console.log("GitHub issue #1 proof-assistant rewrite regression passed");
