import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";
import { createK609BenchmarkTheorems } from "./helpers/k609-workload.mjs";

const parser = new ASTParser();
const encoded = readFileSync(
    new URL("./fixtures/k609-one-formula-before-perm-master.txt", import.meta.url),
    "utf8"
);
const theoremValues = createK609BenchmarkTheorems(encoded);
const pureSemanticRegressionIndices = new Set([
    24, 25, 32, 33, 56, 72, 80, 132, 150, 151
]);
{
    const session = new TTCoreSession();
    session.configure({
        unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
        disableSimpleFn: false,
        disableSimpleEq: false,
        inferDisplayMode: "_",
        timeout: Number.MAX_SAFE_INTEGER,
        language: "zh"
    });
    const core = session.engine.core;
        for (let index = 0; index < theoremValues.length; index++) {
            if (pureSemanticRegressionIndices.has(index) && index !== 24) {
                assertPureSemanticDefinition(core, theoremValues[index], index);
            }
            if (index === 24) {
            const context = lambdaContext(
                core,
                "La:U,Lb:U,Lf:a->b,Ll:leftInv_ip a b f,True"
            );
            const term = core.markBondVars(
                core.desugar(parser.parse("refl(pr0 l)"), false),
                context
            );
            const expected = core.markBondVars(core.desugar(parser.parse(
                "(pr0(leftFromFiber_ip a b f (leftToFiber_ip a b f l)))=(pr0 l)"
            ), false), context);
            const projectionRoundTrip = core.semanticTypeChecker.tryCheck(
                term,
                expected,
                context,
                { elaborateMetas: true, maxSteps: 65_536 }
            );
            assert.equal(projectionRoundTrip.status, "success",
                "lazy transparent definitions must re-enter @pr0 computation after unfolding");

            assertPureSemanticDefinition(core, theoremValues[index], index);
            }
            if (index === 153) {
                const definition = parser.parse(theoremValues[index]);
                core.clearState();
                const prepared = core.markBondVars(
                    core.desugar(Core.clone(definition.nodes[1]), false),
                    []
                );
                let nextBondVarId = core.state.bondVarId;
                const pureSemantic = core.semanticTypeChecker.trySynthesize(prepared, [], {
                    elaborateMetas: true,
                    maxSteps: Core.semanticTypeSynthesisMaxSteps,
                    freshBondVarId: () => nextBondVarId++
                });
                assert.equal(pureSemantic.status, "success",
                    `K609 theorem 153 must bind compact endpoints before delta expansion: ${pureSemantic.code ?? "unknown error"}`);
            }
            const fastPathHitsBefore = Core.semanticTypeCheckFastPathHits;
            const result = session.validate(index, parser.parse(theoremValues[index]));
            assert.equal(result.ok, true,
                `semantic WHNF must preserve K609 theorem ${index}: ${result.error ?? "unknown error"}`);
            if (index === 38) {
                assert.ok(Core.semanticTypeCheckFastPathHits > fastPathHitsBefore,
                    "Fin must use the immutable elaboration path");
                assert.equal(result.definitionCache?.kind, "nbe");
                assert.deepEqual(result.definitionCache?.metas, [],
                    "Fin must store no generalized metas after local universe-hole solving");
                assert.equal(containsHole(result.filledDefinition), false,
                    "Fin must persist the solved @Sum universe arguments");
            }
            if (index === 80) {
                assert.ok(Core.semanticTypeCheckFastPathHits > fastPathHitsBefore,
                    "topSwapEqv_pm must use the independently bounded elaboration input path");
            }
            if (index === 9) {
                assert.ok(Core.semanticTypeCheckFastPathHits > fastPathHitsBefore,
                    "binder-local aliases in idEqvFiberContr_ip must remain on the semantic path");
            }
            if (index === 133) {
                const stored = core.state.userDefs.agentAAutSplitFV5_pm;
                const marked = new Core().markBondVars(Core.clone(stored), []);
                const application = findNestedFunctionApplication(marked, "g");
                assert.ok(application,
                    "agentAAutSplitFV5_pm must retain its nested function application");
                assert.notEqual(
                    application.nodes[0].bondVarId,
                    application.nodes[1].bondVarId,
                    "clearing portable definition ids must not capture the outer function as the inner argument"
                );
            }
            if (index === 153) {
                assert.ok(Core.semanticTypeCheckFastPathHits > fastPathHitsBefore,
                    "a hole-free definition must try the non-elaborating semantic path before expanding alias holes");
            }
        }
}

function containsHole(ast) {
    if (!ast) return false;
    if (ast.type === "var" && (ast.name === "_" || ast.name?.startsWith("?"))) return true;
    return (ast.nodes ?? []).some(containsHole);
}

function findNestedFunctionApplication(ast, functionName) {
    if (!ast) return null;
    if (ast.type === "apply"
        && ast.nodes?.[0]?.type === "var"
        && ast.nodes[0].name === functionName
        && ast.nodes[1]?.type === "apply"
        && ast.nodes[1].nodes?.[0]?.type === "var"
        && ast.nodes[1].nodes?.[1]?.type === "var") {
        return ast.nodes[1];
    }
    for (const child of ast.nodes ?? []) {
        const found = findNestedFunctionApplication(child, functionName);
        if (found) return found;
    }
    return null;
}

function lambdaContext(core, source) {
    let term = core.markBondVars(core.desugar(parser.parse(source), false), []);
    const context = [];
    while (term.type === "L") {
        context.unshift([term.name, term.nodes[0], term.bondVarId]);
        term = term.nodes[1];
    }
    return context;
}

function assertPureSemanticDefinition(core, source, index) {
    core.clearState();
    const definition = parser.parse(source);
    const prepared = core.markBondVars(
        core.desugar(Core.clone(definition.nodes[1]), false),
        []
    );
    const result = core.semanticTypeChecker.trySynthesize(prepared, [], {
        elaborateMetas: true,
        maxSteps: 65_536
    });
    assert.equal(result.status, "success",
        `K609 theorem ${index} must stay on the pure semantic path: ${result.code ?? "unknown error"}`);
    if (index === 56 || index === 72) {
        assert.ok(result.term, `K609 theorem ${index} must return an elaborated term`);
        assert.equal(containsHole(result.term), false,
            `K609 theorem ${index} must compact hidden alias metas before returning`);
    }
}

console.log("semantic WHNF full K609 regression passed");
