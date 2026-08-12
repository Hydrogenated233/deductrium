import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { SemanticNbeTypeChecker } from "../js/tt/nbe-checker.js";
import { SemanticNbeKernel } from "../js/tt/nbe-kernel.js";

const parser = new ASTParser();

function createFixture() {
    const sourceCore = new Core();
    const kernel = new SemanticNbeKernel();
    const checker = new SemanticNbeTypeChecker(kernel);
    const mark = (source, context = []) => sourceCore.markBondVars(parser.parse(source), context);

    const sameType = mark("Pa:U,a->a->U");
    assert.equal(checker.setConstantSchemeSnapshot("same", {
        type: sameType,
        // The unused generalized meta mirrors the implicit metas present
        // while aliases such as fnext are recursively checked.
        metas: [{ name: "?0", expectedType: parser.parse("U@") }]
    }), true);

    let telescope = mark("Pa:U,Pb:U,Pf:a->b,Pz:?9,Px:a,U");
    const context = [];
    while (telescope.type === "P") {
        context.unshift([
            telescope.name,
            Core.clone(telescope.nodes[0]),
            telescope.bondVarId
        ]);
        telescope = telescope.nodes[1];
    }
    const term = mark("same a x (z (f x))", context);
    const sourceMeta = {
        name: "?9",
        role: "type",
        allowedBondVarIds: context.slice(2).map(([, , id]) => id)
    };
    return { checker, context, term, sourceMeta, mark };
}

{
    const { checker, context, term } = createFixture();
    assert.deepEqual(
        checker.trySynthesize(term, context, {
            elaborateMetas: false,
            maxSteps: 100_000
        }),
        { status: "invalid", code: "expected-function" },
        "an unregistered legacy context meta must remain on the fallback path"
    );
}

{
    const { checker, context, term, sourceMeta } = createFixture();
    const termBefore = parser.stringify(term);
    const contextBefore = context.map(([name, type, id]) => [name, parser.stringify(type), id]);
    const result = checker.trySynthesize(term, context, {
        elaborateMetas: false,
        maxSteps: 100_000,
        sourceMetas: [sourceMeta]
    });

    assert.equal(result.status, "success");
    assert.equal(parser.stringify(result.type), "U");
    assert.equal(result.sourceMetaConstraints?.length, 1);
    assert.equal(result.sourceMetaConstraints[0].name, "?9");
    assert.equal(result.sourceMetaConstraints[0].value.type, "P");
    assert.equal(parser.stringify(result.sourceMetaConstraints[0].value.nodes[0]), "b");
    assert.equal(parser.stringify(result.sourceMetaConstraints[0].value.nodes[1]), "a");
    assert.equal(parser.stringify(term), termBefore,
        "source-meta refinement must keep the caller-owned term immutable");
    assert.deepEqual(
        context.map(([name, type, id]) => [name, parser.stringify(type), id]),
        contextBefore,
        "source-meta refinement must keep the caller-owned context immutable"
    );
}

{
    const { checker, context, term, sourceMeta } = createFixture();
    const result = checker.trySynthesize(term, context, {
        elaborateMetas: false,
        maxSteps: 100_000,
        sourceMetas: [{
            ...sourceMeta,
            allowedBondVarIds: sourceMeta.allowedBondVarIds.slice(0, 1)
        }]
    });
    assert.notEqual(result.status, "success",
        "a source type meta must not capture a type outside its creation context");
}

{
    const { checker, context, sourceMeta, mark } = createFixture();
    const result = checker.trySynthesize(mark("z (f x)", context), context, {
        elaborateMetas: false,
        maxSteps: 100_000,
        sourceMetas: [sourceMeta]
    });
    assert.notEqual(result.status, "success",
        "an unconstrained application must not invent a codomain meta");
}

{
    const core = new Core();
    core.clearSemanticState();
    const mark = (source, context = []) => core.markBondVars(parser.parse(source), context);
    assert.equal(core.semanticTypeChecker.setConstantSchemeSnapshot("same", {
        type: mark("Pa:U,a->a->U"),
        metas: [{ name: "?0", expectedType: parser.parse("U@") }]
    }), true);

    let telescope = mark("Pa:U,Pb:U,Pf:a->b,Pz:?9,Px:a,U");
    const context = [];
    while (telescope.type === "P") {
        context.unshift([
            telescope.name,
            Core.clone(telescope.nodes[0]),
            telescope.bondVarId
        ]);
        telescope = telescope.nodes[1];
    }
    const term = mark("same a x (z (f x))", context);

    const previousOutputNodes = Core.semanticTypeCheckMaxOutputNodes;
    try {
        core.state.time = Date.now();
        Core.semanticTypeCheckMaxOutputNodes = 0;
        const rejectedContext = Core.cloneContext(context);
        assert.equal(core.trySemanticTypeSynthesis(term, rejectedContext), undefined);
        assert.equal(parser.stringify(rejectedContext[1][1]), "?9",
            "a rejected semantic output must not commit source-meta constraints");

        Core.semanticTypeCheckMaxOutputNodes = 64;
        const acceptedContext = Core.cloneContext(context);
        const type = core.trySemanticTypeSynthesis(term, acceptedContext);
        assert.equal(parser.stringify(type), "U");
        const committed = acceptedContext[1][1];
        assert.equal(committed?.type, "P");
        assert.equal(parser.stringify(committed.nodes[0]), "b");
        assert.equal(parser.stringify(committed.nodes[1]), "a");
    } finally {
        Core.semanticTypeCheckMaxOutputNodes = previousOutputNodes;
    }
}

console.log("semantic source-meta constraint regression passed");
