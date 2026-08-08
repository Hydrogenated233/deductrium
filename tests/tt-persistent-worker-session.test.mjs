import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
};
const ftr = "ftr:=ind_nat(λ_:_._)True(λ_:_.λa:_.True→a)";
const ftreq = "ftreq:=ind_nat(λa:_.ftr a→_)(λa:_.a=true)(λa:_.λb:ftr a→_.λc:ftr(succ a).Πd:True,b (c d))";

const session = new TTCoreSession();
session.configure(config);
const persistentCore = session.engine.core;

assert.equal(session.validate(0, parser.parse(ftr)).ok, true);
assert.equal(session.validate(1, parser.parse(ftreq)).ok, true);
assert.equal(session.engine.core, persistentCore, "sequential validation rebuilt the Core instance");
assert.equal(session.validate(2, parser.parse("ftreq 3")).ok, true);

const snapshot = session.getDefinitionSlots(2);
const restored = new TTCoreSession();
restored.configure(config, snapshot);
assert.equal(restored.validate(2, parser.parse("ftreq 4")).ok, true);

session.truncate(1);
const originalLog = console.log;
console.log = () => { };
const missing = session.validate(2, parser.parse("ftreq 0"));
console.log = originalLog;
assert.equal(missing.ok, false);
assert.match(missing.error, /未知的变量.*ftreq/);

assert.equal(session.validate(1, parser.parse(ftreq)).ok, true);
assert.equal(session.validate(2, parser.parse("ftreq 2")).ok, true);

console.log("persistent Worker definition session regression passed");
