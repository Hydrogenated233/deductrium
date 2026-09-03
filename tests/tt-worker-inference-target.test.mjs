import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";
import {
    theoremInferenceComplete,
    theoremInferenceStatus,
    theoremInferenceTarget
} from "../js/tt/theorem-validation.js";

const parser = new ASTParser();
const session = new TTCoreSession();
session.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: Number.MAX_SAFE_INTEGER,
    language: "zh"
});

const source = "ftr:=ind_nat(λ_:_._)True(λ_:_.λa:_.True→a)";
const surfaceDefinition = parser.parse(source);
const result = session.validate(0, surfaceDefinition);

assert.equal(result.ok, true, result.error);
assert.equal(result.inferenceComplete, true,
    "a Worker-filled definition must report its solved surface holes as complete");
assert.match(parser.stringify(surfaceDefinition), /_/, "the display AST must preserve the user's holes");

const inferenceTarget = theoremInferenceTarget(surfaceDefinition, result.filledDefinition);
assert.equal(inferenceTarget, result.filledDefinition,
    "a validated definition must inspect the Worker's filled definition");
assert.equal(hasInferenceHole(inferenceTarget), false,
    "a solved surface hole must not leave the theorem marked as infering");
assert.equal(hasInferenceHole(surfaceDefinition), true,
    "selecting the filled definition must not mutate the display AST");

const proposition = parser.parse("True");
assert.equal(theoremInferenceTarget(proposition, result.filledDefinition), proposition,
    "non-definition checks must continue inspecting their checked surface AST");

const solvedAssertion = session.validate(1, parser.parse("(λx:_.x):(True→True)"));
assert.equal(solvedAssertion.ok, true, solvedAssertion.error);
assert.equal(solvedAssertion.inferenceComplete, true,
    "a Worker-successful assertion must report holes solved by its expected type as complete");
assert.equal(theoremInferenceStatus(solvedAssertion.inferenceComplete), "complete",
    "finish() must trust the Worker's successful elaboration instead of probing display holes");
assert.match(parser.stringify(solvedAssertion.ast), /_/,
    "the Worker completion signal must not rewrite the displayed assertion");

const unresolvedTerm = session.validate(2, parser.parse("λx:_.x"));
assert.equal(unresolvedTerm.ok, true, unresolvedTerm.error);
assert.equal(unresolvedTerm.inferenceComplete, false,
    "Worker success alone must not hide a genuinely underconstrained inference hole");
assert.equal(theoremInferenceStatus(unresolvedTerm.inferenceComplete), "incomplete",
    "finish() must keep genuinely unresolved terms marked as infering");
assert.equal(theoremInferenceStatus(undefined), "legacy",
    "callers without the new Worker signal must retain the legacy inference probe");

const nbeInternalMetavariable = session.validate(3,
    parser.parse("add_zero:=(λx:nat.rfl):(Πx:nat,eq (add x 0) x)"));
assert.equal(nbeInternalMetavariable.ok, true, nbeInternalMetavariable.error);
assert.equal(nbeInternalMetavariable.inferenceComplete, true,
    "NbE-private metavariables introduced for refl must not mark a completed theorem as infering");
assert.equal(theoremInferenceComplete(theoremInferenceTarget(
    nbeInternalMetavariable.ast,
    nbeInternalMetavariable.filledDefinition
)), true, "the legacy inference fallback must also ignore NbE-private metavariables");
const reflMeta = nbeInternalMetavariable.filledDefinition.nodes[0].nodes[1].nodes[1];
assert.equal(reflMeta.name, "?0");
assert.equal(reflMeta.nbeGeneratedMeta, true,
    "the Worker result must preserve NbE-generated provenance after public renaming");
assert.equal(theoremInferenceComplete({
    type: "apply",
    name: "",
    nodes: [
        { type: "var", name: "refl" },
        { type: "var", name: "?nbe0" }
    ]
}), false, "an unmarked user metavariable must not be trusted because of its spelling");

function hasInferenceHole(ast, seen = new WeakSet()) {
    if (!ast || seen.has(ast)) return false;
    seen.add(ast);
    if (ast.type === "var" && (ast.name === "_" || ast.name.startsWith("?"))) return true;
    return (ast.nodes ?? []).some(node => hasInferenceHole(node, seen));
}

console.log("worker filled-definition inference target regression passed");
