# Lean-style Type-Theory Tactics

These spellings use Deductrium's existing type-theory proof constructors and
NbE checker. They are not a complete Lean parser or tactic interpreter.
Theorems are stored as kernel-checked proof terms, not tactic transcripts.
Command history is for undo and unfinished proof sessions. Legacy spellings
still present in the implementation are not a constraint on new syntax.

| Command | Effect | Survival unlock |
| --- | --- | --- |
| `have h : T` | Prove `T` first, then continue the original goal with `h : T` | `hyp` |
| `have h := t` | Infer the type of `t` and bind a checked local fact | `hyp` |
| `have h : T := t` | Check `t : T` and bind the local fact | `hyp` |
| `have h : T := by ...` | Prove a typed local lemma in a focused block | `hyp` |
| `use t` | Supply one witness for a dependent pair goal | `ex` |
| `rcases h with ⟨x, hx⟩` | Eliminate a local product/dependent pair with explicit names | `destruct` |
| `obtain h [: T] := t` | Bind a checked local fact, with optional type annotation | `hyp` and `destruct` |
| `obtain ⟨x, hx⟩ [: T] := t` | Check a term and eliminate its product/dependent pair into named local facts | `hyp` and `destruct` |

Local names must not collide with names already in the current context.
An `rcases` component may be `_` to request a fresh unused name; ASCII
`<x, hx>` is also accepted. Pair patterns may nest on either side, such as
`⟨n, ⟨m, h⟩⟩` or `⟨⟨n, hn⟩, h⟩`. Every pair must contain exactly two
components and have matching delimiters. Disjunction patterns are not
implemented. Bare `rcases h` and the existing compact `with x hx` form retain
their earlier behavior. `use` accepts one term; it does not implement a
comma-separated sequence of witnesses or automatically close the remaining
goal. `have` requires an explicit local name. A `by` proof additionally
requires the type annotation; inferring a local lemma's type from tactics
is not supported.

For target `Πh:(Σn:nat,n=n),Σm:nat,m=m`:

```text
intro h
rcases h with ⟨n, hn⟩
have equality : n=n := hn
use n
exact equality
qed
```

The local fact is represented by a checked lambda application, not an extra
axiom. Its continuation retains the entire original goal. A dependent outer
goal is resolved only when that continuation is finished, not when the local
lemma is proved. Non-type declarations such as `have h : 0` are rejected.

The Worker and fallback use the same `TTAssistEngine` command interface.
Failed commands reconstruct the preceding history; undo and saved-history
replay retain the user's spelling. Individual command entry accepts the new
spellings when their original tactics are unlocked; text replay keeps its
existing availability behavior. Final `qed` still checks the full proof term.

`obtain` accepts the same nested pair patterns as `rcases`, including ASCII
`<x, hx>` and `_` components. It requires a supplied term after `:=`; postponed
proofs (`obtain ... : T` without a term), alternative patterns, and `by`
blocks are not supported. Use `have h : T` followed by a proof and
`rcases h with ...` for a postponed proof. The optional annotation is checked
before elimination. The source term's existing local bindings remain available;
only the fresh temporary fact is eliminated. A failed elimination rolls back
the local fact as part of the existing command transaction.

For the same target above, the complete proof may also be written:

```text
intro h
obtain ⟨n, hn⟩ := h
use n
exact hn
qed
```

## Nested Pair Patterns

`rcases`, `obtain`, and the pair components of `rintro` share the same pattern
parser and dependent elimination implementation. Explicit names are reserved
across the entire pattern before automatic names are chosen; repeated explicit
names are rejected. Intermediate pair bindings are eliminated, leaving the
leaf bindings in left-to-right pattern order. Splitting a left component
updates dependent sibling types before the next split. The existing
`disableDestructConds` restriction still applies to dependent context handling.

For target `Πp:(Σn:nat,Σm:nat,n=m),Σa:nat,Σb:nat,a=b`:

```text
rintro ⟨n, ⟨m, h⟩⟩
use n
use m
exact h
qed
```

Alternatively, start with `intro p` and then either
`rcases p with ⟨n, ⟨m, h⟩⟩` or `obtain ⟨n, ⟨m, h⟩⟩ := p`.
The latter retains the original `p`, as with the non-nested form.
One nested command is one history/undo entry. Any failed inner elimination
restores the entire preceding command state, including pending goals.
Patterns are limited to 64 nested pairs and 255 total pair/name nodes;
these are deterministic syntax limits, not new type-theory rules.

## Structured Proofs

The text editor and `TTAssistEngine.apply` share `tactic-script.ts`.
The editor submits one top-level command or block at a time. No worker
message or theorem-save format change is needed.

For target `True → (True × True) × True`:

```text
by
  intro h
  have pair : True × True := by
    constructor
    · exact h
    · exact h
  constructor
  · exact pair
  · exact by
      exact h
qed example
```

- An optional leading `by` wraps the script. `qed name` remains the explicit
  final save command and may be inside or outside that outer indentation.
- `·` focuses the next goal. The block must solve that goal and every goal
  it creates before returning to the hidden siblings. It cannot consume a
  sibling, even after finishing its own goal.
- `have h : T := by` focuses the local lemma proof, then resumes the original
  goal with `h`. Neither `h` itself nor the continuation is available inside
  the lemma proof.
- `exact by` focuses and completely solves the current goal.
- Bullets and local lemma blocks may nest. Inline forms such as `· rfl`,
  `exact by rfl`, and `have h : T := by exact t` are accepted.
- Indentation uses spaces. A block's statements align; child blocks indent
  further. After an inline bullet, continuation statements align two spaces
  past the bullet. Blank lines and `--` comments are ignored.
- A failed top-level block is rolled back in full. Undo removes one accepted
  top-level block. Draft text retains unfinished blocks, while the accepted
  history contains only complete successful blocks.
- Executing to the caret only accepts complete blocks in that prefix.
  An unfinished block reports an error and is not partially committed.
- Resource limits are 64 nested blocks and 4096 parsed nodes per submitted
  script. Empty blocks, inconsistent indentation, and unknown commands fail
  explicitly with line numbers. Only registered tactics can be dispatched;
  internal assistant methods are not commands.

Focus preserves live goal and dependency references. For a target
`Σn:nat,n=n`, `constructor`, `· exact 0`, `· rfl` therefore updates the hidden
second goal to `0=0`. Final `qed` checks the entire resulting term again.
If a local name shadows a public constructor alias (for example `pair`),
the printed proof retains the corresponding `@pair` kernel application.
It must not shorten that application into a reference to the local fact.
Regression tests reload exported definitions into a fresh checking session.

This is a supported subset, not a full Lean interpreter: tactic combinators
such as `<;>`, named `case ... =>` alternatives, `all_goals`, term-level `by`
inside arbitrary expressions, and `obtain ... := by` are not implemented.
Symbol input aliases, including the branch bullet, are listed only in the
progress panel's per-layer symbol tables.
