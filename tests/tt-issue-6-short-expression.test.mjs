import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { TTGui } from "../js/tt/gui.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
};

function countConfigurations(session) {
    const configure = session.engine.configure.bind(session.engine);
    let count = 0;
    session.engine.configure = (...args) => {
        count++;
        return configure(...args);
    };
    return () => count;
}

{
    const session = new TTCoreSession();
    const configurations = countConfigurations(session);
    session.configure(config);

    assert.equal(session.validate(0, parser.parse("True")).ok, true);
    assert.equal(session.validate(0, parser.parse("base")).ok, true);
    assert.equal(configurations(), 1,
        "rechecking one ordinary theorem row must not rebuild the whole Worker engine");
}

{
    const session = new TTCoreSession();
    const configurations = countConfigurations(session);
    session.configure(config, [
        null,
        ["later", parser.parse("true")]
    ]);

    assert.equal(session.validate(2, parser.parse("later")).ok, true,
        "a loaded later definition must initially be available after its slot");
    const originalLog = console.log;
    console.log = () => { };
    const forwardReference = session.validate(0, parser.parse("later"));
    console.log = originalLog;
    assert.equal(forwardReference.ok, false,
        "rewinding the Worker must remove later definitions before checking an earlier row");
    assert.match(forwardReference.error ?? "", /未知的变量.*later/);
    assert.equal(session.validate(2, parser.parse("later")).ok, true,
        "advancing again must reload retained definition slots incrementally");
    assert.equal(configurations(), 1,
        "rewinding across uniquely named definitions must not rebuild the engine");
}

{
    const session = new TTCoreSession();
    const configurations = countConfigurations(session);
    session.configure(config, [
        ["shadow", parser.parse("true")],
        ["shadow", parser.parse("0b")]
    ]);

    assert.equal(session.validate(2, parser.parse("shadow:Bool")).ok, true);
    assert.equal(session.validate(1, parser.parse("shadow:True")).ok, true,
        "removing a shadowing definition must restore the retained definition with the same name");
    assert.equal(configurations(), 2,
        "same-name shadow restoration may use the bounded rebuild fallback");
}

{
    const gui = Object.create(TTGui.prototype);
    gui.skipRendering = false;
    gui.coreWorker = {};
    gui.theoremItems = [];
    gui.userDefinedConsts = [];
    gui.unlockedTypes = new Set(["True"]);
    let warmups = 0;
    let revalidations = 0;
    gui.updateTypeList = () => { };
    gui.prepareCoreWorker = async (index, scopeFolderId) => {
        assert.equal(index, 0);
        assert.equal(scopeFolderId, null);
        warmups++;
    };
    gui.revalidateTheorems = () => { revalidations++; };

    gui.updateAfterUnlock();
    assert.equal(warmups, 1,
        "an empty theorem editor must warm the core Worker before the first input");
    assert.equal(revalidations, 1);

    gui.theoremItems = [{ kind: "theorem", input: { value: "True" } }];
    gui.updateAfterUnlock();
    assert.equal(warmups, 1,
        "save restoration must let theorem validation configure the Worker instead of warming twice");
}

console.log("GitHub issue #6 short-expression Worker regression passed");
