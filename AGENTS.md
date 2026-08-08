# Development Checks

- Before changing code, run `npm test` once to establish the current baseline.
- After changing code, run `npm test` again. Run `npm run typecheck` when TypeScript source changed.
- Put correctness regressions in `tests/*.test.mjs` and reusable inputs in `tests/fixtures/`.
- Put timing-only workloads in `tests/benchmarks/`; run them with `npm run benchmark` and do not use machine-specific timings as correctness assertions.
