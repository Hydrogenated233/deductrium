import assert from "node:assert/strict";
import { FSCmd } from "../js/fs/cmd.js";
import { ASTParser } from "../js/fs/astparser.js";
import { FormalSystem } from "../js/fs/formalsystem.js";

const parser = new ASTParser();

function makeCommand(formalSystem) {
    const gui = {
        formalSystem,
        deductions: Object.keys(formalSystem.deductions),
        actionInput: { value: "", selectionStart: 0, selectionEnd: 0 },
        hintText: { innerText: "", innerHTML: "" },
        cmdBtns: [],
        isMobile: true,
        pListMasked: false,
        clearPListMasked() { },
        updatePropositionList() { },
        addToDeductions(name) { this.deductions.push(name); }
    };
    gui.getDeduction = name => formalSystem.deductions[name];
    const command = Object.create(FSCmd.prototype);
    Object.assign(command, {
        gui,
        cmdBuffer: [],
        escClear: true,
        pListMasked: false,
        expansionBusy: false,
        expansionGeneration: 0,
        commandGeneration: 0,
        lastDeduction: null,
        autoCompleteIdx: -1,
        _selStart: 0,
        _selEnd: 0
    });
    return { command, gui };
}

const formalSystem = new FormalSystem();
formalSystem.addDeduction("mp-test", parser.parse("$0,($0>$1)⊢$1"), "test");
formalSystem.addDeduction("axiom", parser.parse("⊢A"), "test");
formalSystem.propositions.push({
    value: parser.parse("A"),
    from: { deductionIdx: "axiom", conditionIdxs: [], replaceValues: [] }
});

const { command, gui } = makeCommand(formalSystem);

// A failed token in a space-separated command must abort the remaining queue.
// Before the generation guard, the trailing `d` was appended to a newly
// cleared buffer and left the editor in a fresh, unrelated command state.
{
    const queued = makeCommand(formalSystem);
    queued.command.cmdBuffer = ["not-a-command d"];
    queued.command.execCmdBuffer();
    assert.deepEqual(queued.command.cmdBuffer, []);
    assert.equal(queued.command.escClear, true);
}

// An invalid premise index must cancel the complete command, even when the
// deduction had already entered its multi-step (escClear=false) state.
command.cmdBuffer = ["d", "mp-test", "0", "99"];
command.escClear = false;
command.execDeduct();
assert.deepEqual(command.cmdBuffer, []);
assert.equal(command.escClear, true);
assert.doesNotMatch(gui.hintText.innerText, /## error/);

// A new macro started after that failure must consume only the active theorem
// list, never stale command tokens from the failed deduction.
command.cmdBuffer = ["m", "fresh"];
command.execMacro();
const recorded = formalSystem.deductions.fresh;
assert.ok(recorded);
assert.equal(recorded.conclusion.name, "A");
assert.equal(recorded.conditions.length, 0);
assert.doesNotMatch(JSON.stringify(recorded), /mp-test|## error|99/);
assert.deepEqual(command.cmdBuffer, []);

// A space-separated command is replayed token by token.  Once one token
// fails, the remainder must not be interpreted as a fresh command sequence.
command.cmdBuffer = ["d mp-test 0 99 m queueFresh"];
command.commandGeneration = 0;
gui.unlockedMacro = true;
command.execCmdBuffer();
assert.deepEqual(command.cmdBuffer, []);
assert.equal(formalSystem.deductions.queueFresh, undefined);

// An exception escaping command dispatch must use the same hard reset even
// when the command was in a multi-step state.
command.cmdBuffer = ["not-a-command", "stale"];
command.escClear = false;
command.execCmdBuffer();
assert.deepEqual(command.cmdBuffer, []);
assert.equal(command.escClear, true);

console.log("inference command failure reset regression passed");
