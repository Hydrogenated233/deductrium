import assert from "node:assert/strict";

import { langMgr } from "../js/lang.js";
import { AssertionSystem } from "../js/fs/assertion.js";
import { ASTParser as FsAstParser } from "../js/fs/astparser.js";
import { FormalSystem } from "../js/fs/formalsystem.js";
import { Assist } from "../js/tt/assist.js";
import { ASTParser as TtAstParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";

const fsParser = new FsAstParser();
const ttParser = new TtAstParser();

// ast2deduction() is an internal constructor, but its result still has to
// satisfy the Deduction contract before addDeduction() applies any fallback.
{
    const system = new FormalSystem();
    const deduction = system.ast2deduction(fsParser.parse("⊢a=a"));
    assert.ok(deduction.tempvars instanceof Set,
        "ast2deduction must initialize tempvars as a Set");
}

// A repeated replacement variable must distinguish #rp-wrapped and ordinary
// values so callers receive the dedicated diagnostic instead of a generic one.
{
    const previousLanguage = langMgr.lang;
    langMgr.lang = "zh";
    try {
        const assertion = new AssertionSystem();
        const result = {};
        const varTable = {};
        const astAssertions = {};
        const patternAssertions = [];
        assertion.match(
            fsParser.parse("a"),
            fsParser.parse("$x"),
            /^\$/,
            false,
            result,
            varTable,
            astAssertions,
            patternAssertions
        );
        assert.throws(
            () => assertion.match(
                fsParser.parse("#rp(a,b,c)"),
                fsParser.parse("$x"),
                /^\$/,
                false,
                result,
                varTable,
                astAssertions,
                patternAssertions
            ),
            /替换函数#rp导致模式匹配/,
            "#rp mismatch must use the dedicated diagnostic"
        );
    } finally {
        langMgr.lang = previousLanguage;
    }
}

// Formal-system assertion errors should be translated rather than exposing
// the old hard-coded English message.
{
    const previousLanguage = langMgr.lang;
    langMgr.lang = "zh";
    try {
        const assertion = new AssertionSystem();
        let removeError;
        try {
            assertion.removeFn(fsParser.parse("a"));
        } catch (error) {
            removeError = String(error);
        }
        assert.match(removeError, /非.*#fn|removeFn/);

        const resfn = {};
        assertion.getReplVarsType(fsParser.parse("f(a)"), {}, true, resfn);
        let typeError;
        try {
            assertion.getReplVarsType(fsParser.parse("f(a)"), {}, false, resfn);
        } catch (error) {
            typeError = String(error);
        }
        assert.match(typeError, /符号|Token/);
        assert.match(typeError, /不能同时为函数和谓词/);
    } finally {
        langMgr.lang = previousLanguage;
    }
}

// Proof-assistant AST search must recurse through unary and 3+ child nodes.
{
    const assist = new Assist(new Core(), ttParser.parse("True"));
    assert.equal(
        assist.search(ttParser.parse("[y]"), ttParser.parse("y")),
        true,
        "search must recurse through unary nodes"
    );
    const child = ttParser.parse("needle");
    const root = { type: "synthetic", name: "root", nodes: [
        ttParser.parse("a"),
        ttParser.parse("b"),
        child
    ] };
    assert.equal(
        assist.search(root, child),
        true,
        "search must recurse through every child"
    );
}

// Generic substitution must visit all children, including children after the
// binary prefix used by the current parser.
{
    const assist = new Assist(new Core(), ttParser.parse("True"));
    const root = { type: "synthetic", name: "root", nodes: [
        ttParser.parse("x"),
        ttParser.parse("y"),
        ttParser.parse("x"),
        ttParser.parse("x")
    ] };
    assist.replaceFreeVar(root, "x", ttParser.parse("z"));
    assert.deepEqual(root.nodes.map(node => node.name), ["z", "y", "z", "z"]);
}

console.log("second review regression tests passed");
