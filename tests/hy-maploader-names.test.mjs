import assert from "node:assert/strict";
import { Polygon } from "../js/hy/tiling.js";
import { blockMap, duplicateNames, initMap, nameMap } from "../js/hy/maploader.js";

initMap(new Polygon(6, 4));

// The two relief stations must keep distinct stable names. A duplicate used to
// overwrite the first entry in nameMap and left blockMap/nameMap inconsistent.
assert.equal(duplicateNames.length, 0);
const first = nameMap.get("JJZI-1");
const second = nameMap.get("JJZI-2");
assert.ok(first && second && first !== second);
assert.equal(blockMap.get(first)?.name, "JJZI-1");
assert.equal(blockMap.get(second)?.name, "JJZI-2");

for (const [tile, block] of blockMap) {
  if (block.name) assert.equal(nameMap.get(block.name), tile);
}

console.log("maploader duplicate-name regression passed");
