import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { SemanticNbeTypeChecker } from "../js/tt/nbe-checker.js";
import { SemanticNbeKernel } from "../js/tt/nbe-kernel.js";

const parser = new ASTParser();

function prepareNamedMeta() {
    const checker = new SemanticNbeTypeChecker(new SemanticNbeKernel());
    const prepared = checker.prepare(
        parser.parse("?m"),
        [],
        { allowNamedSchematicMetas: true }
    );
    assert.equal(prepared.status, "success");
    return {
        checker,
        ast: prepared.value.ast,
        context: prepared.value.context,
        state: prepared.value.state
    };
}

// Scope checking happens inside bindMeta(), before a solution is stored. This
// malformed/future 3-child apply still looks like a valid universe-level max
// to the binary application flattener, so child 2 is the exact regression.
{
    const { checker, ast, context, state } = prepareNamedMeta();
    state.metaAllowedContextIds.set(ast.name, new Set());
    const candidate = {
        type: "apply",
        name: "",
        nodes: [
            {
                type: "apply",
                name: "",
                nodes: [
                    { type: "var", name: "@max" },
                    { type: "var", name: "@0" }
                ]
            },
            { type: "var", name: "@0" },
            { type: "var", name: "escaped", bondVarId: 99 }
        ]
    };
    assert.equal(
        checker.bindMeta(ast.name, candidate, context, state),
        "unsupported",
        "meta scope checking must reject a free binder in every AST child"
    );
    assert.equal(state.metaSolutions.has(ast.name), false);
}

// An occurs-check failure is a definite unification failure, not an
// unsupported decision. Keeping it unequal prevents a legacy fallback from
// retrying a cyclic type through a less precise path.
{
    const checker = new SemanticNbeTypeChecker(new SemanticNbeKernel());
    const cyclic = {
        type: "P",
        name: "x",
        nodes: [
            { type: "var", name: "?m" },
            { type: "var", name: "?m" }
        ]
    };
    assert.deepEqual(
        checker.tryDefinitionalEquality(
            { type: "var", name: "?m" },
            cyclic,
            [],
            {
                sourceMetas: [{
                    name: "?m",
                    role: "type",
                    allowedBondVarIds: []
                }]
            }
        ),
        { status: "invalid", code: "type-mismatch" }
    );
}

console.log("NbE full-review audit regressions passed");
