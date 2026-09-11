import assert from "node:assert/strict";

import { SemanticNbeKernel } from "../js/tt/nbe-kernel.js";

const variable = name => ({ type: "var", name });
const application = (fn, arg) => ({ type: "apply", name: "", nodes: [fn, arg] });

function flattenApplication(term) {
    const args = [];
    let head = term;
    while (head?.kind === "application") {
        args.unshift(head.arg);
        head = head.fn;
    }
    return { head, args };
}

// The repository runner imports tests sequentially, so keep this regression
// synchronous instead of registering a detached `node:test` callback.
{
    const repeated = application(variable("f"), variable("x"));
    // Distinct AST objects model the repeated hit_dep2_comp subtrees emitted by
    // sandbox lowering; sharing must happen only in the private semantic term.
    const source = application(
        application(variable("pair"), repeated),
        application(variable("f"), variable("x"))
    );
    const sourceSnapshot = JSON.stringify(source);
    const kernel = new SemanticNbeKernel();
    assert.equal(kernel.replaceDefinitions([
        ["dup", source],
        ["dup2", application(variable("f"), variable("x"))]
    ]), 2);

    // TS private fields are runtime-private only by convention; this test
    // intentionally inspects the semantic DAG, never the public save/bundle.
    const term = kernel.definitions.get("dup");
    const { args } = flattenApplication(term);
    assert.equal(args.length, 2);
    assert.strictEqual(args[0], args[1]);
    assert.strictEqual(args[0], kernel.definitions.get("dup2"));

    // Compression is semantic-only: it neither mutates the public AST nor
    // creates a helper definition that could leak into bundles or saves.
    assert.equal(JSON.stringify(source), sourceSnapshot);
    assert.deepEqual([...kernel.definitions.keys()], ["dup", "dup2"]);
}

{
    const left = { type: "x", name: "y:z", nodes: [] };
    const right = { type: "x:y", name: "z", nodes: [] };
    const kernel = new SemanticNbeKernel();

    assert.equal(kernel.replaceDefinitions([
        ["leftRigid", left],
        ["rightRigid", right]
    ]), 2);
    assert.notStrictEqual(
        kernel.definitions.get("leftRigid"),
        kernel.definitions.get("rightRigid"),
        "different rigid type/name pairs must occupy different semantic nodes"
    );
    assert.equal(
        kernel.tryEqualResult(variable("leftRigid"), variable("rightRigid")),
        "unequal",
        "bulk interning must not change definitional equality"
    );
}

{
    const kernel = new SemanticNbeKernel();
    kernel.withSemanticTermSharing(() => {
        kernel.withSemanticTermSharing(() => {
            assert.equal(kernel.tryEqualResult(
                application(variable("f"), variable("x")),
                application(variable("f"), variable("x"))
            ), "equal");
        });
    });
    assert.throws(() => kernel.withSemanticTermSharing(() => {
        throw new Error("scope failure");
    }), /scope failure/);
    assert.equal(kernel.tryEqualResult(
        application(variable("f"), variable("x")),
        application(variable("f"), variable("x"))
    ), "equal");
}

console.log("NBE term sharing regressions passed");
