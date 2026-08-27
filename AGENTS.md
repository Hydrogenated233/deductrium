# Deductrium HoTT Optimization

This repository is a browser application with a worker-backed HoTT/type-theory
engine. The user-facing application is in the repository root; TypeScript
sources live under `src/`, generated browser JavaScript is written to `js/`,
and release archives are written to `release/`.

## Development Checks

- Before changing code, run `npm test` once to establish the current baseline.
- After changing code, run `npm test` again. Run `npm run typecheck` whenever a
  TypeScript source file changes; `npm run build` is also required before a
  release.
- The complete test runner is `tests/run.mjs`. It imports tests sequentially,
  so a hang or timeout must be diagnosed rather than hidden by removing a test.
  If the full suite is too slow while iterating, run the smallest relevant
  test directly and report that the full suite still needs to run.
- Put correctness regressions in `tests/*.test.mjs` and reusable inputs in
  `tests/fixtures/`.
- Put timing-only workloads in `tests/benchmarks/`. Run them with the matching
  `npm run benchmark:*` command and do not use machine-specific timings as
  correctness assertions.
- Keep tests deterministic. Do not make correctness depend on wall-clock
  timing, browser garbage collection, or a particular worker scheduling order.

Useful commands:

```text
npm test
npm run typecheck
npm run build
npm run benchmark
npm run benchmark:save
npm run benchmark:k609
npm run benchmark:k609:browser
npm run package
```

## Type-Theory Engine

- `src/tt/core.ts` is the legacy/core checking and inference layer. The NbE
  implementation is split between `nbe-kernel.ts`, `nbe-checker.ts`, and the
  semantic helpers used by `core.ts` and `core-session.ts`.
- `core-worker.ts` and `assist-worker.ts` own the long-running workers;
  `core-worker-client.ts` and `assist-worker-client.ts` are their browser
  clients. Preserve worker message contracts when changing either side.
- `core-session.ts` is intended to keep one configured session alive while
  validating an ordered prefix of definitions. Do not configure and copy the
  entire definition prefix for every theorem: that reintroduces browser-side
  O(n^2) work. Prefer incremental append/validate operations, and truncate or
  rebuild only after an edit that invalidates the suffix.
- Inference/cache snapshots must remain bounded. When serializing a definition
  cache, retain only the inference variables, relations, deferred constraints,
  and AST nodes reachable from the cache roots. Use existing snapshot/clone
  helpers instead of inventing a second cache format.
- Semantic NbE equality is the authority for definitional equality and gate
  matching. Keep the old syntactic/shape heuristic where the UI uses it for
  "possibly applicable" recommendations, but never replace a kernel check
  with a recommendation result.
- Any semantic-NbE unsupported or budget-limited path must fail explicitly and
  predictably. Do not convert resource exhaustion into a successful proof or a
  generic `undefined`/`null` dereference.
- Preserve binder scope and universe levels when elaborating or normalizing.
  In particular, do not leak generated `?nbe...` variables into user-visible
  syntax; generated holes should use the project's existing `?` convention,
  while explicit user-entered `@name` references must remain visible as `@name`.
- Preserve surface syntax in presentation and error messages. Normalization
  may use semantic terms internally, but the UI should not rewrite every term
  into an `@...` elaborated form or erase familiar `=`, `->`, and `▪` notation.

## Proof Assistant Rules

- Proof-assistant command behavior is covered by `src/tt/assist-engine.ts`,
  `assist.ts`, and the assist worker. Keep `intro`, `destruct`, `exact`,
  `apply`, `rw`, `simpl`, and `qed` behavior compatible with existing saves.
- `_` arguments in `apply` and `rw` are elaboration holes for inference. They
  must not be treated as literal identifiers, and unresolved holes must remain
  visible until the command reports a useful error.
- `qed name` stores the proof under the requested name and must preserve the
  theorem proposition. Stale proof-goal/bond identifiers must be rejected
  without corrupting the current editing state.
- Failed commands must not cancel the editor, reset the input, or leave a
  partially-mutated goal tree. Repeated clicks and repeated validation requests
  must be serialized or cancelled through the existing mutation queue.
- `destruct` must remove eliminated variables and update all dependent goals;
  nested destructs must not leave the old variable in a displayed target.
  Motives for self-loop and indexed inductive cases need explicit validation.
- Rewriting may use semantic matching, including inferred `_` arguments, but
  retain the user's surface rewrite notation after a successful `rw`.
- Local constants are scoped to the selected proof context/folder. Opening a
  theorem from a different list position must not silently change the constant
  pool; references should follow the user's selected folder scope.

## UI, Folders, and Saves

- The GUI is in `src/tt/gui.ts` and the root HTML/CSS files. Keep validation
  asynchronous and responsive; never block the main thread with a full
  re-check when an incremental suffix check is sufficient.
- Folder drag/drop semantics are user-visible: a collapsed folder is not a
  valid drop target, and dropping on an expanded folder inserts at the folder's
  bottom. The dedicated folder-bottom theorem action follows the same ordering
  rules as drag/drop.
- The "disable child theorems" option is recursive and must affect both
  validation and theorem availability. It must not mark unrelated preceding
  definitions as invalid.
- Save/load must preserve theorem order, folder state, map data, achievements,
  validation metadata, and auto-save state. A loaded save should restore the
  validation schedule without duplicating checks or losing system axioms.
- Do not overwrite user-authored README content, including AI-programming
  declarations added online. Avoid unrelated formatting or metadata churn.

## Regression Tests and Fixtures

- Add a focused regression test for every bug fix. Prefer a small fixture or
  inline input that reproduces the original failure before asserting the fix.
- Save files and large theorem inputs belong in `tests/fixtures/`; do not put
  machine-specific absolute paths in tests.
- Performance workloads belong in `tests/benchmarks/` and should report useful
  counters such as theorem count, elapsed time, and peak heap, while allowing
  generous machine-dependent variation.
- For worker races, test both ordering and cancellation. For UI-only changes,
  keep the behavior covered at the state/helper level when a browser test is
  not available.

## Git and Release Workflow

- The active optimization branch is `HoTT-Optimization`. Do not rewrite or
  discard unrelated user changes. In particular, leave an untracked `$null`
  file alone unless the user explicitly asks to remove it.
- Before pushing, inspect `git diff`, `git status`, and the commit being
  published. Use the SSH-over-443 remote when HTTPS certificate validation is
  unavailable:

  ```text
  git push ssh://git@ssh.github.com:443/Hydrogenated233/deductrium.git HoTT-Optimization:HoTT-Optimization
  ```

- GitHub Pages deployment is intentionally not used. Releases are built by
  `.github/workflows/release.yml` on `hott-v*` tags or manual dispatch. The
  workflow resolves the date in China Standard Time, runs tests/typecheck/build,
  invokes `npm run package`, uploads the ZIP, and creates or updates the GitHub
  Release for that tag.
- The package script must include only runtime files and `js/`; it must not
  include `src/` or `node_modules/`. Verify the generated ZIP and SHA256 before
  reporting a release.
- When reusing a same-day release, verify that the lightweight tag, release
  target commit, and uploaded ZIP all point to the workflow's commit.

## Agent skills

### Issue tracker

Issues and specifications live in GitHub Issues for Hydrogenated233/deductrium; use the gh CLI. See docs/agents/issue-tracker.md.

### Triage labels

Use the default triage labels: needs-triage, needs-info, ready-for-agent, ready-for-human, and wontfix. See docs/agents/triage-labels.md.

### Domain docs

This is a single-context repository with root CONTEXT.md and docs/adr/ conventions. See docs/agents/domain.md.
