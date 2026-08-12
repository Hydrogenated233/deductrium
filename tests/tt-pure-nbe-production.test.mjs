import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const runner = fileURLToPath(new URL("./helpers/strict-nbe-runner.mjs", import.meta.url));
const productionTests = [
    // Engine/bootstrap and ordinary Worker/session validation.
    "tt-nbe-system-initialization.test.mjs",
    "tt-worker-cache.test.mjs",
    "tt-worker-definition-caches.test.mjs",
    "tt-persistent-worker-session.test.mjs",
    // Portable cache boundaries and representative real-world saves.
    "tt-nbe-legacy-cache-migration.test.mjs",
    "tt-save-puzzle-definitions.test.mjs",
    "tt-nbe-meikai-pure.test.mjs",
    "tt-nbe-whnf-k609.test.mjs",
    // Proof-assistant and GUI-adjacent semantic production paths.
    "tt-assist-engine.test.mjs",
    "tt-assist-survival-save-rw.test.mjs",
    "tt-assist-explicit-hole-arguments.test.mjs",
    "tt-gate-fuzzy-matching.test.mjs"
];

const failures = [];
for (const test of productionTests) {
    const result = spawnSync(process.execPath, [runner, test], {
        cwd: fileURLToPath(new URL("..", import.meta.url)),
        encoding: "utf8",
        maxBuffer: 16 * 1024 * 1024
    });
    if (result.status !== 0) {
        failures.push({
            test,
            status: result.status,
            output: `${result.stdout ?? ""}${result.stderr ?? ""}`.trim()
        });
    }
}

assert.deepEqual(
    failures,
    [],
    failures.map(({ test, status, output }) =>
        `${test} exited ${status}\n${output}`
    ).join("\n\n")
);

console.log(`${productionTests.length} production paths passed the strict NbE gate`);
