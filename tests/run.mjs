const tests = [
    "./tt-validation-scheduling.test.mjs",
    "./tt-theorem-identifier-rendering.test.mjs",
    "./tt-assist-invalid-command.test.mjs",
    "./tt-assist-even.test.mjs",
    "./tt-s2-assist.test.mjs",
    "./tt-worker-cache.test.mjs",
    "./tt-save-cache-compaction.test.mjs",
    "./tt-worker-definition-caches.test.mjs",
    "./tt-bug1-cache-revalidation.test.mjs",
    "./save-load-overwrite.test.mjs",
    "./tt-persistent-worker-session.test.mjs",
    "./tt-worker-mutation-queue.test.mjs",
    "./tt-pi1-s1.test.mjs",
    "./tt-universe-equivalence.test.mjs",
    "./tt-assist-engine.test.mjs",
    "./tt-assist-intermediate-holes.test.mjs",
    "./tt-assist-expand-eqv.test.mjs"
];

for (const test of tests) {
    console.log(`\n[TEST] ${test}`);
    await import(new URL(test, import.meta.url));
}

console.log(`\n${tests.length} regression tests passed`);
