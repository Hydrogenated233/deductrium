import assert from "node:assert/strict";

const { ASTParser } = await import("../js/tt/astparser.js");
const { wrapVar } = await import("../js/tt/core.js");
const { TTCoreEngine } = await import("../js/tt/engine.js");
const { TTGui } = await import("../js/tt/gui.js");
const { initTypeSystem } = await import("../js/tt/initial.js");

const parser = new ASTParser();

function queryGenericTheorem(expression, target, staleInferName) {
    const engine = new TTCoreEngine();
    engine.configure({ unlockedTypes: initTypeSystem().map(rule => rule.id) });
    const theorem = parser.parse(expression);
    assert.equal(engine.checkAst(theorem, []).ok, true, expression);

    // Simulate a previous theorem reusing the same metavariable for an
    // incompatible type. Matching must instantiate it independently.
    engine.core.state.inferTable.rel[staleInferName] = wrapVar("True");
    const input = {
        dataset: { validatedTypeKey: parser.stringify(theorem.checked) },
        validatedType: theorem.checked,
        parentElement: { classList: { contains() { return false; } } }
    };
    const gui = Object.create(TTGui.prototype);
    gui.gateQueryCache = new Map();
    gui.core = engine.core;
    gui.disableSimpleFn = false;
    gui.disableSimpleEq = false;
    gui.getInhabitatArray = () => [input];
    gui.isTheoremInputDisabled = () => false;
    gui.getHottDefCtxt = () => { };
    return { gui, engine };
}

const listCase = queryGenericTheorem("nil: List ?1", "List False", "?1");
assert.equal(listCase.gui.queryType("List False"), true,
    "nil: List ?1 should satisfy a List False gate by fuzzy matching");
assert.equal(parser.stringify(listCase.engine.core.state.inferTable.rel["?1"]), "True");

const equalityCase = queryGenericTheorem("rfl: ?a = ?a", "False = False", "?a");
assert.equal(equalityCase.gui.queryType("False = False"), true,
    "an equality axiom with ?a should match a concrete equality gate");

const valueCase = queryGenericTheorem("true: ?x", "True", "?x");
assert.equal(valueCase.gui.queryType("True"), true,
    "a value with a generic ?x type should match its concrete gate");

const negativeCase = queryGenericTheorem("nil: List ?1", "Bool", "?1");
assert.equal(negativeCase.gui.queryType("Bool"), false,
    "a generic List inhabitant must not satisfy an unrelated gate type");

console.log("generic type-theorem gate matching regression passed");
