import assert from "node:assert/strict";

const { ASTParser } = await import("../js/tt/astparser.js");
const { TTCoreEngine } = await import("../js/tt/engine.js");
const { TTGui } = await import("../js/tt/gui.js");
const { initTypeSystem } = await import("../js/tt/initial.js");

const parser = new ASTParser();

function queryGenericTheorem(expression, target, staleInferName) {
    const engine = new TTCoreEngine();
    engine.configure({ unlockedTypes: initTypeSystem().map(rule => rule.id) });
    const theorem = parser.parse(expression);
    assert.equal(engine.checkAst(theorem, []).ok, true, expression);

    // Every query gets its own semantic matcher, so schematic source types do
    // not inherit assignments from an earlier theorem.
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

function querySemantically({ gui, engine }, target, invoke = () => gui.queryType(target)) {
    const originalCheckType = engine.core.checkType;
    let checkTypeCalls = 0;
    engine.core.checkType = function (...args) {
        checkTypeCalls++;
        return originalCheckType.apply(this, args);
    };
    try {
        const result = invoke();
        assert.equal(checkTypeCalls, 0,
            `gate query ${target} must not call legacy-capable checkType`);
        return result;
    } finally {
        engine.core.checkType = originalCheckType;
    }
}

const listCase = queryGenericTheorem("nil: List ?1", "List False", "?1");
assert.equal(querySemantically(listCase, "List False"), true,
    "nil: List ?1 should satisfy a List False gate by fuzzy matching");

const equalityCase = queryGenericTheorem("rfl: ?a = ?a", "False = False", "?a");
assert.equal(querySemantically(equalityCase, "False = False"), true,
    "an equality axiom with ?a should match a concrete equality gate");
assert.equal(querySemantically(equalityCase, "False = True"), false,
    "repeated gate metavariables must receive one consistent value");

const valueCase = queryGenericTheorem("true: ?x", "True", "?x");
assert.equal(querySemantically(valueCase, "True"), true,
    "a value with a generic ?x type should match its concrete gate");
assert.equal(querySemantically(
    valueCase,
    "?x ~ True",
    () => valueCase.gui.equalGateTypes(parser.parse("?x"), parser.parse("True"))
), true, "a bare source type metavariable must match a concrete gate type semantically");

const negativeCase = queryGenericTheorem("nil: List ?1", "Bool", "?1");
assert.equal(querySemantically(negativeCase, "Bool"), false,
    "a generic List inhabitant must not satisfy an unrelated gate type");

const unusedPiCase = queryGenericTheorem(
    "λa:U.λb:U.λc:U.λx:a.λy:b.x",
    "Πa:U,Πb:U,Πc:U,a→b→a",
    null
);
assert.equal(querySemantically(unusedPiCase, "Πa:U,Πb:U,Πc:U,a→b→a"), true,
    "a non-dependent Pi inferred as an arrow must satisfy an alpha-equivalent gate type");
assert.equal(querySemantically(unusedPiCase, "Πp:U,Πq:U,Πr:U,p→q→p"), true,
    "gate type comparison must ignore bound-variable names");

console.log("generic type-theorem gate matching regression passed");
