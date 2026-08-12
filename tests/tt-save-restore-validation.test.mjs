import assert from "node:assert/strict";

import { TTGui } from "../js/tt/gui.js";

function restoreWithRenderingState(skipRendering) {
    const gui = Object.create(TTGui.prototype);
    gui.skipRendering = skipRendering;
    gui.definitionRevision = 0;
    gui.theoremStructureRevision = 0;
    gui.gatePreviewStructureRevision = 0;
    gui.userDefinedConsts = [];
    gui.theoremItems = [];
    gui.core = { state: { defTypes: {} } };
    gui.gateQueryCache = { clear() { } };
    gui.refreshUserConstNames = () => { };
    gui.renderTheoremStructure = () => { };
    gui.addTheoremFolder = () => { throw new Error("unexpected folder"); };
    gui.updateInhabitList = function () {
        const input = { value: "", dataset: {} };
        this.theoremItems.push({
            kind: "theorem",
            wrapper: { remove() { } },
            input,
            localCheckbox: { checked: false }
        });
        return input;
    };
    let validations = 0;
    gui.revalidateTheorems = () => validations++;

    gui.restoreTheoremItems([{ kind: "theorem", value: "True" }]);
    assert.equal(gui.theoremItems[0].input.value, "True");
    return validations;
}

assert.equal(restoreWithRenderingState(true), 0,
    "startup restore must wait until system axioms have been registered");
assert.equal(restoreWithRenderingState(false), 1,
    "an in-app save import still validates immediately");

const coordinated = Object.create(TTGui.prototype);
coordinated.skipRendering = false;
coordinated.unlockedTypes = new Set;
coordinated.updateTypeList = () => { };
coordinated.getInhabitatArray = () => [{ onblur() { throw new Error("legacy direct validation"); } }];
let coordinatedValidations = 0;
coordinated.revalidateTheorems = () => coordinatedValidations++;
coordinated.updateAfterUnlock();
assert.equal(coordinatedValidations, 1,
    "startup unlock refresh must enter the validation coordinator exactly once");

console.log("save restore validation scheduling regression passed");
