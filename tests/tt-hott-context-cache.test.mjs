import assert from "node:assert/strict";

import { TTGui } from "../js/tt/gui.js";

const gui = Object.create(TTGui.prototype);
gui.definitionRevision = 7;
gui.theoremStructureRevision = 3;
gui.disableSimpleFn = false;
gui.disableSimpleEq = false;
gui.inferDisplayMode = "_";
gui.semanticResourceScale = 1;
gui.core = { state: {} };
gui.unlockedTypes = new Set(["True", "nat"]);
gui.theoremItems = [];
gui.userDefinedConsts = [
    ["first", { type: "var", name: "true" }],
    ["second", { type: "var", name: "true" }],
    null
];
gui.getInhabitatArray = () => [{}, {}, {}];
gui.getActiveTacticScopeId = () => null;
gui.isDefinitionVisible = (index, targetIndex, scopeId) =>
    index < targetIndex && scopeId === null;
let clearCount = 0;
let addCount = 0;
gui.clearUserDefinitionContext = () => { clearCount++; };
gui.addUserDefinitionToContext = () => { addCount++; };

assert.equal(gui.getHottDefCtxt(3), 3);
assert.equal(clearCount, 1);
assert.equal(addCount, 2);

gui.getHottDefCtxt(3);
assert.equal(clearCount, 1,
    "repeated gate queries should reuse the already materialized context");
assert.equal(addCount, 2);
assert.equal(gui.core.state.disableSimpleFn, false);
assert.equal(gui.core.state.disableSimpleEq, false);

gui.definitionRevision++;
gui.getHottDefCtxt(3);
assert.equal(clearCount, 1,
    "a revision-only change with the same visible prefix can reuse the context");
assert.equal(addCount, 2);

gui.userDefinedConsts[1] = ["second-edited", { type: "var", name: "true" }];
gui.definitionRevision++;
gui.getHottDefCtxt(3);
assert.equal(clearCount, 2,
    "changing a materialized definition must rebuild the context");
assert.equal(addCount, 4);

gui.userDefinedConsts[2] = ["third", { type: "var", name: "true" }];
gui.definitionRevision++;
gui.getHottDefCtxt(3);
assert.equal(clearCount, 2,
    "a visible definition appended to the same prefix should be materialized incrementally");
assert.equal(addCount, 5);

gui.getHottDefCtxt(3, "folder-a");
assert.equal(clearCount, 3,
    "a different folder scope must materialize a different context");
assert.equal(addCount, 5,
    "the scoped fixture has no visible global definitions");

console.log("HoTT definition-context cache regression passed");
