import assert from "node:assert/strict";
import { ASTParser } from "../js/fs/astparser.js";
import { initFormalSystem } from "../js/fs/initial.js";

const parser = new ASTParser();

// A saved completed rule can contain proof steps that rely on a generated
// helper outside the current unlock scope.  Conditionalization for entr must
// still treat that completed rule as an atomic source instead of dereferencing
// the unavailable helper and throwing on null.conditions.
{
    const fs = initFormalSystem(false).fs;
    fs.addDeduction(".testFF", parser.parse("A,B⊢A<>B"), "test");
    fs.deductions[".testFF"].steps = [{
        deductionIdx: "<a1",
        conditionIdxs: [],
        replaceValues: []
    }];
    fs.fastmetarules = "c";
    assert.doesNotThrow(() => fs.generateDeduction("c.testFF"));
    assert.ok(fs.deductions["c.testFF"]?.conditions?.length);
}

console.log("proof-assistant entr conditionalization regression passed");
