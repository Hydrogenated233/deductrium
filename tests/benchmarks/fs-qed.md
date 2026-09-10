# Inference Qed Benchmark

Run `npm run benchmark:fs-qed` for a Node worker replay or
`npm run benchmark:fs-qed -- --sync` for synchronous comparison.
Run `npm run benchmark:fs-qed:browser` for the actual browser GUI and module
worker, including cancellation, retry, and duplicate-submit checks.

The fixture is the inference-system section of the issue #43 save, plus its
53-command `xNatCommonMultiple` proof. It excludes game/map state. The benchmark
rebuilds the proof under a new name rather than citing the already recorded
macro. It retains the original unlocked rules and checks the other page rows.

The browser benchmark uses a fresh temporary profile and an ephemeral loopback
origin. It boots only FSGui, without Game, autosave, or player storage. It never
attaches to an existing browser or port 4174. Optional `FS_QED_SCREENSHOT` names
an output PNG captured while validation is busy.

Reported timings include elapsed submission time, event-loop heartbeat gaps,
Long Tasks, and main-thread snapshot/install/render phases. They are diagnostic
measurements, not correctness thresholds. Worker validation is still CPU work;
snapshot installation and rule-list rendering remain synchronous. Independent
browser results do not replace acceptance in the player's original save.

The deterministic regression is `tests/fs-issue-43-qed-worker.test.mjs`.
It checks shared-DAG cost traversal without wall-clock assertions, full worker
validation and scope rejection, bare/named commits, stale result rejection,
draft preservation, sliced replay cancellation, save replacement, and worker
timeout/unavailability/retry. No failed worker request falls back to main-thread
qed.
