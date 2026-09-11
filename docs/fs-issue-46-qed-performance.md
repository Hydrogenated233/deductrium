# Issue 46: Universal Qed Replay

## Cause

The generated-rule search considers `c`, `u`, and `>` candidates as well as
universal lifting. These paths materialized closed deferred assistant macros
before knowing whether their proof steps were needed. A search while replaying
one macro therefore replayed its dependencies, which performed more searches
and replayed further dependencies.

The September 11, 2026 CPU profile of the real quantified proof reached seven
nested `materializeForDeferred` calls. The profiled commit took 179862ms.
The same free-variable core committed in 139ms; separately generalizing the
checked core took 264ms.

## Change

- `u` delegates closed sources to the existing closed `v` path before replay.
- `c` applies a closed source atomically and derives its weakening with the
  existing `a1`/`mp` rules, without expanding the source's stored proof.
- `>` rejects sources with no hypotheses before attempting replay.

The candidate set, rule matching, non-freeness checks, conditional-source
handling, Worker deadline, and current-proof validation remain unchanged.
Explicit expansion still replays a deferred source. No new axioms or trusted
user rules are installed by this optimization.

## Verification

`tests/fs-issue-46-qed-generalization.test.mjs` records a real identity macro,
uses it inside a quantified implication proof, and checks that committing
the new proof materializes only that proof once. It also expands the result
and compares the final proposition. The assertion is structural, not timed.

The real-save timing workload is separate:

```text
npm run benchmark:fs-universal-qed -- quantified
npm run benchmark:fs-universal-qed -- split
npm run benchmark:fs-universal-qed -- original
npm run benchmark:fs-universal-qed -- worker
```

Each benchmark runs in an isolated child process with a 240-second safety
deadline. `worker` exercises the same snapshot/qed Worker implementation used
by the GUI, with `allowMcpt: false` and the captured survival rule scope.
It does not interact with the browser or install results into a live save.

Local post-fix measurements: quantified 10-tactic commit 604-679ms; original
21-tactic commit 1730-1795ms; Worker commit including snapshot serialization
and thread startup 1167ms. These are individual measurements, not portable
limits. The pre-fix profile includes sampling overhead.

## Fixture

`tests/fixtures/fs-issue-46-union.json.gz` is gzip-compressed JSON containing
only the inference-layer save data, the target, and the original 21 commands.
The original game map, type-theory data, and browser storage are not included.
It was extracted from `zfc-wellordering-theorem-before-gate-save.txt`, whose
SHA256 is:

```text
bcb0ae5f685b02b4fcd95a6bb6daf2db00e140f7391cf8319e32bfd91b14a730
```

The rule scope ends immediately before `xFamilyUnionCompatibleCore`, matching
the issue's quantified/split differential. Later saved rules remain hidden.
