import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { SemanticNbeKernel } from "../js/tt/nbe-kernel.js";
import {
    ScopeCursor,
    contextBindings,
    collectFreeBondVarIds,
    findContextBinding,
    findContextByName,
    findContextIndexByBondVarId,
    findKernelScopeIndex,
    isBinderNode,
    lookupScope,
    markScopedBondVars,
    referencesBoundBinder,
    scopePosition,
    validBondVarId
} from "../js/tt/scoped-syntax.js";

const parser = new ASTParser();
const variable = name => ({ type: "var", name });

assert.equal(isBinderNode(parser.parse("Lx:True.true")), true);
assert.equal(isBinderNode(variable("true")), false);
assert.equal(validBondVarId(1), true);
assert.equal(validBondVarId(0), false);
assert.equal(validBondVarId(Infinity), false);

const inner = ["x", variable("True"), 11];
const outer = ["x", variable("Bool"), 22];
const context = [inner, outer];
assert.equal(findContextByName(context, "x"), inner);
assert.equal(findContextIndexByBondVarId(context, 22, (left, right) => left === right), 1);
assert.deepEqual(contextBindings(context).bindings.map(binding => binding.key), [
    "context-id:11",
    "context-id:22"
]);
assert.strictEqual(contextBindings(context), contextBindings(context),
    "the indexed context view is reused while the source context is unchanged");
assert.equal(findContextBinding({ type: "var", name: "x", bondVarId: 22 }, contextBindings(context))?.key,
    "context-id:22");

const cursor = new ScopeCursor();
assert.equal(cursor.length, 0);
const outerResult = cursor.withBinding({ name: "x" }, () => {
    assert.equal(cursor.findIndex(variable("x")), 0);
    const markedResult = cursor.withBinding({ name: "x", id: 7 }, () => {
        assert.equal(cursor.findIndex({ type: "var", name: "x", bondVarId: 7 }), 0);
        assert.equal(cursor.findIndex(variable("x")), 1,
            "an unmarked occurrence skips marked shadowing binders");
        assert.equal(cursor.hasName("x"), true);
        return cursor.at(1)?.name;
    });
    assert.equal(markedResult, "x");
    assert.equal(cursor.findIndex(variable("x")), 0);
    return cursor.length;
});
assert.equal(outerResult, 1);
assert.equal(cursor.length, 0, "withBinding must restore the cursor after errors/results");

const sourceAwareCursor = new ScopeCursor();
sourceAwareCursor.push({ name: "source", id: 101, sourceId: 41 });
assert.equal(lookupScope({ type: "var", name: "source", bondVarId: 41 }, sourceAwareCursor)?.id, 101,
    "checker lookup keeps source ids authoritative after freshening");
assert.equal(scopePosition({ type: "var", name: "source", bondVarId: 41 }, sourceAwareCursor), 0);
sourceAwareCursor.pop();

const sourceAndIdCursor = new ScopeCursor();
sourceAndIdCursor.push({ name: "outer", id: 7, sourceId: 3 });
sourceAndIdCursor.push({ name: "inner", id: 3, sourceId: 11 });
assert.equal(sourceAndIdCursor.findBySourceOrId(3)?.name, "inner",
    "combined source/id lookup preserves legacy nearest-first matching");
assert.deepEqual([...sourceAndIdCursor.activeBondVarIds()].sort((left, right) => left - right), [3, 7]);
sourceAndIdCursor.pop();
sourceAndIdCursor.pop();

const unmarkedSourceCursor = new ScopeCursor();
unmarkedSourceCursor.push({ name: "x", id: 1 });
unmarkedSourceCursor.push({ name: "x", id: 2, sourceId: 22 });
assert.equal(unmarkedSourceCursor.findByUnmarkedSourceName("x")?.id, 1,
    "an id-less occurrence cannot be captured by a marked source binder");
unmarkedSourceCursor.pop();
unmarkedSourceCursor.pop();

const syntax = parser.parse("Lx:True.x");
let nextId = 40;
markScopedBondVars(syntax, [], () => nextId++);
assert.equal(syntax.bondVarId, 40);
assert.equal(syntax.nodes[1].bondVarId, 40);

const kernelScope = new ScopeCursor();
kernelScope.withBinding({ name: "x", id: 9 }, () => {
    assert.equal(findKernelScopeIndex({ type: "var", name: "x", bondVarId: 9 }, kernelScope), 0);
    assert.equal(findKernelScopeIndex(variable("x"), kernelScope), -1);
});

const scopedTerm = parser.parse("Lx:True.Ly:True.x y");
scopedTerm.bondVarId = 51;
scopedTerm.nodes[1].bondVarId = 52;
scopedTerm.nodes[1].nodes[0].bondVarId = 51;
scopedTerm.nodes[1].nodes[1].bondVarId = 52;
assert.deepEqual([...collectFreeBondVarIds(scopedTerm)], [],
    "references bound by the corresponding binder are not free");
scopedTerm.nodes[1].nodes[1].nodes[0].bondVarId = 99;
assert.deepEqual([...collectFreeBondVarIds(scopedTerm)], [99],
    "a foreign binder id is reported as free");
assert.equal(referencesBoundBinder(scopedTerm.nodes[1], 51), true);
const shadowedBody = {
    type: "L",
    name: "x",
    bondVarId: 51,
    nodes: [variable("True"), { type: "var", name: "x", bondVarId: 51 }]
};
assert.equal(referencesBoundBinder(shadowedBody, 51), false,
    "a nested binder with a reused id shadows only its own body");

const originalWithBinding = ScopeCursor.prototype.withBinding;
ScopeCursor.prototype.withBinding = () => {
    throw new Error("kernel compilation must use explicit cursor push/pop");
};
try {
    assert.ok(new SemanticNbeKernel().tryNormalize(telescope(128), [], { maxSteps: 10_000_000 }),
        "recursive kernel compilation must not add callback stack frames per binder");
} finally {
    ScopeCursor.prototype.withBinding = originalWithBinding;
}

console.log("scoped syntax indexing and cursor regression passed");

function telescope(depth) {
    let body = variable("U");
    for (let index = 0; index < depth; index++) {
        body = {
            type: "P",
            name: `x${index}`,
            bondVarId: index + 1,
            nodes: [variable("U"), body]
        };
    }
    return body;
}
