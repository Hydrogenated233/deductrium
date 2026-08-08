import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";
import { TTCoreEngine } from "../js/tt/engine.js";

const unlockedTypes = [
    "True", "False", "False.not", "eq", "nat", "eq.rfl", "Bool", "Bool.ind",
    "False.ind", "True.ind", "Prod", "Sum", "Sum.ind", "Prod.ind", "nat.ind",
    "nat.double", "nat.add", "eq.ind", "eq.*", "eq.inv", "Prod.pr0", "Prod.pr1",
    "Prod.prd1", "nat.mul", "List", "nat.pow", "eq.=", "eq.ap", "nat.!", "nat.pred",
    "Even", "Aleph", "Z", "S1", "eq.apd", "eq.trans", "eq.transconst", "S1.ind",
    "Z.succ", "Z.nat2", "Z.neg", "Z.pred", "Z.predsucc", "Z.succpred", "Z.add",
    "Z.le", "Z.abs", "Z.mul", "S1.loop_pow", "eqv", "eq.rightrfl", "eq.invinv",
    "eq.rightinv", "eq.leftinv", "fnext", "eq.happly", "LiftU", "eqv.id2eqv",
    "eqv.refl", "ua"
];
const config = {
    unlockedTypes,
    disableSimpleFn: false,
    disableSimpleEq: false,
    inferDisplayMode: "_",
    timeout: 10_000,
    language: "zh"
};
const parser = new ASTParser();

function clearBondIds(ast) {
    ast.bondVarId = null;
    for (const node of ast.nodes ?? []) clearBondIds(node);
    if (ast.checked) clearBondIds(ast.checked);
    return ast;
}

function storedDefinition(engine, result) {
    return engine.core.desugar(clearBondIds(Core.clone(result.filledDefinition, true)), true);
}

const worker = new TTCoreEngine();
worker.configure(config);
const ftrResult = worker.registerDefinition(parser.parse(
    "ftr:=ind_nat(λ_:_._)True(λ_:_.λa:_.True→a)"
));
assert.equal(ftrResult.ok, true, ftrResult.error);
const ftr = storedDefinition(worker, ftrResult);

worker.configure({ ...config, userDefinitions: [["ftr", ftr]] });
const ftreqResult = worker.registerDefinition(parser.parse(
    "ftreq:=ind_nat(λa:_.ftr a→_)(λa:_.a=true)(λa:_.λb:ftr a→_.λc:ftr(succ a).Πd:True,b (c d))"
));
assert.equal(ftreqResult.ok, true, ftreqResult.error);
assert.ok(ftreqResult.definitionCache, "Worker result did not include the definition type cache");
const ftreq = storedDefinition(worker, ftreqResult);

const main = new TTCoreEngine();
main.configure({ ...config, userDefinitions: [["ftr", ftr], ["ftreq", ftreq]] });
const log = console.log;
try {
    console.log = () => { };
    assert.throws(
        () => main.core.checkType(parser.parse("ftreq 0 === Lx:ftr 0,eq (x ) true"), [], false),
        /@1.*@0/
    );
} finally {
    console.log = log;
}
main.core.restoreDefinitionCache("ftreq", ftreqResult.definitionCache);

let binders = "";
let args = "";
let primes = "";
for (let i = 0; i < 5; i++) {
    main.core.checkType(parser.parse(
        `ftreq ${i} === Lx:ftr ${i},${binders}eq (x ${args}) true`
    ), [], false);
    binders += `Pa${primes}:True,`;
    args += `a${primes} `;
    primes += "'";
}

console.log("ftreq Worker cache regression passed");
