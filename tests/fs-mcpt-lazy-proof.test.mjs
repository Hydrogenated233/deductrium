import assert from "node:assert/strict";
import { ASTParser } from "../js/fs/astparser.js";
import { FormalSystem } from "../js/fs/formalsystem.js";
import { initFormalSystem } from "../js/fs/initial.js";
import { SavesParser } from "../js/fs/savesparser.js";

const parser = new ASTParser();
const proposition = "$0>$0";

function makeFormalSystem() {
    return initFormalSystem(true).fs;
}

function addCompleteTheorem(fs, name) {
    fs.metaCompleteTheorem(parser.parse(proposition), name, "元规则生成*");
    return fs.deductions[name];
}

function useCompleteTheorem(fs, name) {
    const deduction = fs.deductions[name];
    return fs.deduct({
        deductionIdx: name,
        conditionIdxs: [],
        replaceValues: deduction.replaceNames.map(replvar => parser.parse(replvar))
    });
}

const fs = makeFormalSystem();
const lazy = addCompleteTheorem(fs, "lazyCpt");
assert.equal(lazy.deferredKind, "cpt");
assert.equal(lazy.steps, undefined);
assert.equal(fs.propositions.length, 0, "creating cpt must not generate proof propositions");

const directProposition = useCompleteTheorem(fs, "lazyCpt");
assert.equal(parser.stringifyTight(fs.propositions[directProposition].value), proposition);
assert.equal(lazy.steps, undefined, "ordinary deduction must leave cpt proof deferred");

const expandFs = makeFormalSystem();
const expandLazy = addCompleteTheorem(expandFs, "expandCpt");
expandFs.expandMacroWithDefaultValue("expandCpt");
assert.ok(expandLazy.steps?.length, "entr rule expansion must materialize cpt steps");
assert.ok(expandFs.propositions.length > 1);

const inlineFs = makeFormalSystem();
const inlineLazy = addCompleteTheorem(inlineFs, "inlineCpt");
inlineFs.inlineMacroInProp(useCompleteTheorem(inlineFs, "inlineCpt"));
assert.ok(inlineLazy.steps?.length, "inln must materialize cpt steps");
assert.ok(inlineFs.propositions.length > 1);

const propExpandFs = makeFormalSystem();
const propExpandLazy = addCompleteTheorem(propExpandFs, "propExpandCpt");
propExpandFs.expandMacroWithProp(useCompleteTheorem(propExpandFs, "propExpandCpt"));
assert.ok(propExpandLazy.steps?.length, "entr proposition expansion must materialize cpt steps");
assert.ok(propExpandFs.propositions.length > 1);

const saves = new SavesParser(true);
const serialized = saves.serializeDeduction(inlineLazy);
assert.equal(serialized[2], undefined, "materialized cpt steps must not enter the save payload");
assert.equal(serialized[3], undefined, "deferred cpt temp variables are derived on demand");
assert.equal(serialized[4], "cpt");
const savedJson = JSON.parse(JSON.stringify(serialized));
assert.equal(savedJson[2], null);
assert.equal(savedJson[3], null);

const restoredFs = makeFormalSystem();
saves.deserializeDeduction("restoredCpt", restoredFs, savedJson);
const restored = restoredFs.deductions.restoredCpt;
assert.equal(restored.deferredKind, "cpt");
assert.equal(restored.steps, undefined);
restoredFs.expandMacroWithDefaultValue("restoredCpt");
assert.ok(restored.steps?.length, "restored cpt must materialize when expanded");

const invalidFs = new FormalSystem();
assert.throws(
    () => invalidFs.metaCompleteTheorem(parser.parse("$0"), "invalidCpt", "元规则生成*"),
    /tautology|重言式/i
);
assert.equal(invalidFs.deductions.invalidCpt, undefined);

const tooManyVariables = Array.from({ length: 31 }, (_, idx) => `$${idx}>$${idx}`).join("&");
assert.throws(
    () => new FormalSystem().metaCompleteTheorem(parser.parse(tooManyVariables), "tooManyCpt", "元规则生成*"),
    /variables|变量|重言式/i
);

console.log("mcpt lazy-proof and save regression passed");
