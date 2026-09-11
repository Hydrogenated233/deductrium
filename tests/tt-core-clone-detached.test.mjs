import assert from "node:assert/strict";
import { ASTParser } from "../js/tt/astparser.js";
import { Core } from "../js/tt/core.js";

const parser = new ASTParser();
const source = parser.parse("Πx:U,x→x");
const clone = Core.clone;

assert.doesNotThrow(() => clone(source), "Core.clone must be safe when detached");
const copied = clone(source);
assert.notEqual(copied, source);
assert.notEqual(copied.nodes, source.nodes);
assert.equal(copied.type, source.type);
assert.equal(copied.nodes?.[0]?.type, source.nodes?.[0]?.type);
assert.equal(copied.nodes?.[1]?.nodes?.[1]?.name, source.nodes?.[1]?.nodes?.[1]?.name);

console.log("detached Core.clone regression passed");
