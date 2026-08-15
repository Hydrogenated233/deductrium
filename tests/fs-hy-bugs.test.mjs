import assert from "node:assert/strict";
import { ASTParser } from "../js/fs/astparser.js";
import { AssertionSystem } from "../js/fs/assertion.js";
import { FormalSystem } from "../js/fs/formalsystem.js";
import { ConstrainSolver } from "../js/fs/metarule.js";
import { Proof } from "../js/fs/proof.js";
import { SavesParser } from "../js/fs/savesparser.js";
import { Hvec, Rotor } from "../js/hy/algebra.js";
import { HWorld } from "../js/hy/hworld.js";
import { LocalDraw } from "../js/hy/localdraw.js";

const parser = new ASTParser();

// Missing generated rules should be treated as absent, not dereferenced.
const fs = new FormalSystem();
assert.deepEqual(
    [...fs.findLocalNamesInDeductionStep([{
        deductionIdx: "missing-rule",
        conditionIdxs: [],
        replaceValues: [{ type: "replvar", name: "##x" }]
    }])],
    ["##x"]
);

// More than eight independent constraints are valid and must not look like a cycle.
const constraints = [];
for (let i = 0; i < 10; i++) {
    constraints.push([
        { type: "fn", name: "f", nodes: [{ type: "replvar", name: `$${i}` }] },
        { type: "fn", name: "f", nodes: [{ type: "replvar", name: "a" }] },
        false
    ]);
}
assert.equal(Object.keys(new ConstrainSolver().solveConstrain(constraints, [])).length, 10);

// Invalid grammar paths throw so callers can report the error consistently.
const assertion = new AssertionSystem();
assert.throws(() => assertion.checkGrammer(parser.parse("Vx:True"), "i"));

// Save migration helpers tolerate unrelated/malformed rule names.
assert.equal(new SavesParser().fixbug260330("foo>.a1_bad"), "foo>.a1_bad");

// EOF is a normal parser state, not a property-access exception.
assert.equal(new ASTParser().acceptVar(), false);

// Hyperbolic values must remain finite when normalization receives an invalid metric.
const invalidPoint = new Hvec(0, 1, 1).normalize();
assert.deepEqual([invalidPoint.x, invalidPoint.y, invalidPoint.z], [0, 0, 1]);
const invalidRotor = new Rotor(0, 1, 1, 0).normalize();
assert.deepEqual([invalidRotor.r, invalidRotor.x, invalidRotor.y, invalidRotor.z], [1, 0, 0, 0]);
assert.deepEqual([Rotor.moveTo(new Hvec(0, 0, 0)).r], [1]);
assert.equal(Hvec.precalcLerp(new Hvec, new Hvec), null);

// A failed inline macro must not leave propositions from successful substeps behind.
const eq = parser.parse("a=a");
const invalidConclusion = parser.parse("a+b");
const makeDeduction = (conclusion, steps) => ({
    value: conclusion,
    conditions: [],
    conclusion,
    replaceNames: [],
    replaceTypes: {},
    from: "test",
    steps,
    tempvars: new Set()
});
const macroFs = new FormalSystem();
macroFs.generateDeduction = name => name === "main"
    ? makeDeduction(eq, [
        { deductionIdx: "ok", conditionIdxs: [], replaceValues: [] },
        { deductionIdx: "bad", conditionIdxs: [], replaceValues: [] }
    ])
    : name === "ok" ? makeDeduction(eq) : makeDeduction(invalidConclusion);
assert.throws(() => macroFs.deduct({ deductionIdx: "main", conditionIdxs: [], replaceValues: [] }, "inline"));
assert.equal(macroFs.propositions.length, 0);

// Camera updates reject invalid rotors before touching the live matrix.
const world = Object.create(HWorld.prototype);
world.localCamMat = new Rotor;
assert.equal(world.setCameraMatrix(new Rotor(0, 1, 1, 0)), false);
assert.deepEqual([world.localCamMat.r, world.localCamMat.x, world.localCamMat.y, world.localCamMat.z], [1, 0, 0, 0]);
world.getBlock = () => ({ type: 99 });
assert.equal(world.hitTest([999]), false);

// hitTestPoincareDisk has the conventional inside=true contract.
globalThis.window = { devicePixelRatio: 1 };
const draw = new LocalDraw({
    width: 100,
    height: 100,
    getContext: () => ({})
});
assert.equal(draw.hitTestPoincareDisk(50, 50), true);
assert.equal(draw.hitTestPoincareDisk(0, 0), false);

console.log("fs/hy bug regressions passed");
