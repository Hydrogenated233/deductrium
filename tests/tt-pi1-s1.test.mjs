import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const script = fileURLToPath(new URL("../work/check-pi1-complete.mjs", import.meta.url));
const result = spawnSync(process.execPath, [script], {
    cwd: fileURLToPath(new URL("..", import.meta.url)),
    encoding: "utf8"
});

assert.equal(result.status, 0, result.stderr || result.stdout);
assert.match(result.stdout, /pi1S1 true/);

console.log("π₁(S¹) equivalence proof regression passed");
