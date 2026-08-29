import assert from "node:assert/strict";
import { ASTParser } from "../js/fs/astparser.js";
import { FSCmd } from "../js/fs/cmd.js";
import { FormalSystem } from "../js/fs/formalsystem.js";

const parser = new ASTParser();

function createCommand(ruleNames) {
    const formalSystem = new FormalSystem();
    for (const name of ruleNames) formalSystem.addDeduction(name, parser.parse("⊢A"), "test");
    const folderUpdates = [];
    let deductionUpdates = 0;
    let propositionUpdates = 0;
    const gui = {
        formalSystem,
        deductions: ruleNames.slice(),
        unlockedMacro: true,
        isMobile: true,
        actionInput: { value: "" },
        hintText: { innerText: "" },
        cmdBtns: [],
        removeDeductionFolderCount(names) { folderUpdates.push(names.slice()); },
        updateDeductionList() { deductionUpdates++; },
        updatePropositionList() { propositionUpdates++; }
    };
    const command = Object.create(FSCmd.prototype);
    Object.assign(command, {
        gui,
        cmdBuffer: [],
        escClear: true,
        pListMasked: false,
        expansionBusy: false
    });
    return {
        command,
        gui,
        folderUpdates,
        get deductionUpdates() { return deductionUpdates; },
        get propositionUpdates() { return propositionUpdates; }
    };
}

{
    const state = createCommand(["s1", "s3", "s43"]);
    state.command.cmdBuffer = ["del s1 s3 s43"];
    state.command.execCmdBuffer();

    assert.deepEqual(Object.keys(state.gui.formalSystem.deductions), []);
    assert.deepEqual(state.gui.deductions, []);
    assert.deepEqual(state.folderUpdates, [["s1", "s3", "s43"]]);
    assert.equal(state.deductionUpdates, 1);
    assert.equal(state.propositionUpdates, 1);
}

{
    const state = createCommand(["s1", "s3"]);
    state.command.cmdBuffer = ["del", "s1 s3"];
    state.command.execCmdBuffer();
    assert.deepEqual(state.gui.deductions, []);
}

{
    const formalSystem = new FormalSystem();
    formalSystem.addDeduction("base", parser.parse("⊢A"), "test");
    formalSystem.addDeduction("derived", parser.parse("⊢A"), "test", [{
        deductionIdx: "base",
        conditionIdxs: [],
        replaceValues: []
    }]);

    assert.throws(() => formalSystem.removeDeduction("base"), /derived/);
    const results = formalSystem.removeDeductions(["base", "derived"]);
    assert.deepEqual([...results], [["base", true], ["derived", true]]);
    assert.deepEqual(Object.keys(formalSystem.deductions), []);
}

{
    const formalSystem = new FormalSystem();
    formalSystem.addDeduction("keep", parser.parse("⊢A"), "test");
    assert.throws(() => formalSystem.removeDeductions(["keep", "missing"]), /missing/);
    assert.ok(formalSystem.deductions.keep);
}

console.log("multi-rule del command regression passed");
