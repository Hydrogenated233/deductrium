# Symbol Input

The progress panel contains the complete input tables. They are rendered from
the same data as the editors, grouped by output symbol and separated by layer.
Type one backslash and an alias, then press Space. Names remain case-insensitive.

`src/symbol-aliases.ts` owns shared arrows, products, pair-pattern brackets, and
Greek identifier spellings. The inference and type-theory modules import that
table and append only their own syntax. Synchronization does not make both
languages support every symbol: inference-only logic and set notation must not
appear in type-theory input help or its resolver.

## Lean Input Subset

Spellings were checked on September 11, 2026 against the official input table:

```text
https://raw.githubusercontent.com/leanprover/vscode-lean4/master/lean4-unicode-input/src/abbreviations.json
```

This is a selected, compatible subset, not a complete Lean input-method port.
The imported spellings include:

- Shared: `\r`, `\rightarrow`, `\imp`, `\langle`, `\rangle`, and Greek letter
  names such as `\alpha`, `\beta`, `\theta`, `\eps`, and `\om`.
- Inference: `\all`, `\ex`, `\an`, `\v`, `\union`, `\inter`,
  `\intersection`, `\leq`, `\geq`, and `\smallsetminus`.
- Type theory: `\la` and `\equiv`.

Existing project meanings take precedence over Lean when spellings conflict:
`\l` remains lambda, `\pi`/`\sigma` remain the capital dependent-type binders,
`\*`/`\star` remain path composition, and `\setminus` remains the mathematical
set-difference character U+2216. No new parser constructs or axioms are added.
Pair brackets are for tactics' pair patterns, not new term syntax.

## Compatibility Boundaries

The layer-specific scanners keep their original quoted-text, comment, and
escaped-backslash behavior. Inference aliases need a left identifier boundary
to preserve legacy set differences such as `Q\and` and `α\and`. Type-theory
input retains adjacent composition aliases such as `a\*b`.

New input data must have no case-insensitive duplicate names. Shared spellings,
full help-table coverage, paste/caret conversion, layer exclusions, and legacy
spellings are covered by `tests/symbol-alias-sync.test.mjs`.
