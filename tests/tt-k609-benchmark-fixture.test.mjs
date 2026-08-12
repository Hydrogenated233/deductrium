import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { ASTParser } from "../js/tt/astparser.js";
import {
    createK609BenchmarkTheorems,
    decodeK609Theorems,
    K609_FINAL_THEOREM
} from "./helpers/k609-workload.mjs";

const encoded = readFileSync(
    new URL("./fixtures/k609-one-formula-before-perm-master.txt", import.meta.url),
    "utf8"
);
const savedTheorems = decodeK609Theorems(encoded);
const benchmarkTheorems = createK609BenchmarkTheorems(encoded);

assert.equal(savedTheorems.length, 195);
assert.equal(savedTheorems.some(value => value.startsWith("permEqvV87K_pg10:=")), false);
assert.equal(benchmarkTheorems.length, 196);
assert.equal(benchmarkTheorems.at(-1), K609_FINAL_THEOREM);

const finalAst = new ASTParser().parse(benchmarkTheorems.at(-1));
assert.equal(finalAst.type, ":=");
assert.equal(finalAst.nodes[0].name, "permEqvV87K_pg10");

console.log("K609 benchmark fixture shape regression passed");
