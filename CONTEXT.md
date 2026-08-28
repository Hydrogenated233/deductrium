# Deductrium Domain Glossary

## Theorem Workspace / 定理工作区

The theorem workspace is the ordered collection of theorem rows and folders in
the type layer. It owns ordering, folder membership, visibility, local-constant
scope, disabled-subtree state, and the serialized save shape. Rendering,
validation execution, and type-theory caches consume workspace decisions but do
not define them.

## Theorem row

A theorem row is one user-entered proposition or definition in the theorem
workspace. Its position is part of the ordered validation sequence. A row may
be a local constant when it is inside a folder and marked local.

## Folder

A folder is an ordered workspace item containing the following theorem rows.
Its open state controls whether descendants are visible as drop targets; its
disabled state recursively removes descendants from theorem availability and
validation without changing their stored text or cached result.

## Workspace scope

Workspace scope is the set of folders that contain a theorem row. A selected
folder scope may expose local constants owned by that folder or one of its
ancestors; a parent folder cannot see helpers local to a child folder. Global
constants remain available according to their position.

## Validation suffix

The validation suffix is the ordered theorem-row range that must be rechecked
after a workspace mutation. A workspace mutation reports the earliest affected
row so validation scheduling remains an adapter concern.

## Scoped Syntax / 作用域语法

Scoped syntax is the binder-aware representation shared by the legacy checker,
semantic checker, NbE kernel, and persistent definition session. Contexts are
ordered from the nearest binding outward; positive `bondVarId` values identify
real binders, `0` retains proof-assistant name fallback semantics, and
`Infinity` remains a sentinel. The scoped-syntax module owns lookup/indexing,
portable binder traversal, and the mutable lexical cursor used by hot NbE
compilation paths. Surface AST spelling and explicit `@` markers remain the
responsibility of presentation adapters.

## Persistent Execution Session / 持久执行会话

The persistent execution session owns one configured Core, its ordered
definition slots, cache restoration, and the loaded-prefix cursor. It exposes
the core command vocabulary (`configure`, `truncate`, `set-definition`,
`check`, and `validate`) through one synchronous dispatch interface. Browser
Workers and Node process threads are adapters over this interface; request IDs,
RPC generations, transport queues, recovery snapshots, and proof-assistant
state remain outside the session.

## Type-theory Proof Pages / 类型论证明页

**Type-theory proof page / 类型论证明页**:
A persistent, independently recoverable proof workspace. A page may be blank or
hold one type-theory target together with its command history, text draft,
reference scope, and current proof state. Reopening a theorem row reuses its
existing bound page. Successful `qed` clears the page back to a blank
target-selection state without deleting or reordering it.

**Type-theory proof page collection / 类型论证明页集合**:
The ordered set of open type-theory proof pages, with exactly one active page.
The collection preserves blank pages, drafts, order, and active-page identity
across saves while only the active page advances.

**Stale proof session / 陈旧证明会话**:
A theorem-bound session whose proposition or reference scope has changed since
its last replay. Its draft remains available, but it cannot complete against
the former target and must be replayed in the theorem's current context.

**Detached proof session / 脱离证明会话**:
A session whose bound theorem row has been deleted. Its draft remains available
for inspection or completion, but a completed proof creates a new theorem
rather than updating the deleted row.

## Inference Page / 推理表

An inference page is one independently numbered proposition workspace in the
deduction layer. It owns its proposition list, pending command input, and
pending command state. Constants, functions, predicates, deduction rules, and
metarules are shared across all inference pages.

Inference pages are ordered and uniquely named. One page is active for editing,
but changing page order does not change the active page. The workspace always
contains at least one page; legacy saves are restored into a single page named
`主表`.

## Page-local proposition / 表内定理

A page-local proposition belongs to exactly one inference page and is numbered
only within that page. Deduction conditions may reference propositions from the
active page, never from another page. Recording a macro consumes and clears only
the active page; other pages remain unchanged.

## Deduction gate witness / 推理门见证

A deduction-layer `#p` gate is witnessed by any inference page that contains the
gate proposition and contains no hypotheses. Gate checking examines pages
independently and does not depend on which page is active.

## Inference page selection / 推理表选择

The page selector is rendered between the theorem list wrapper and the
theorem-list heading (`before-list-wrapper`) in the deduction panel. Creating a
page appends it to the selector but does not activate it; the current page keeps
its selection until the user explicitly switches pages.

Validation is page-local: editing a page checks only its affected suffix,
while page creation, deletion, reordering, and switching do not recheck other
pages. Loading a save validates all restored pages in order. A failed page is
marked locally, and `#p` checks only verified, hypothesis-free propositions from
each page.

The `d` command resolves proposition indices in the active page. Metarules and
recorded macros remain globally available, but a recorded macro captures only
the active page and never stores page names or page-local proposition numbers.
Page names are unique single tokens; page operations are available independently
of macro unlocks. Page names, order, active page, per-page propositions, and
pending command state are persisted by saves and autosave.

Recording a macro keeps the existing failure boundary: if the active page has
no valid theorem derivation steps, macro creation fails with
`无有效定理推导步骤，创建宏推导失败` and leaves that page unchanged.

## Inference-layer Proof Assistant / 推理层证明助手

The inference-layer proof assistant operates on propositions, hypotheses,
deduction rules, metarules, and macros; it is independent of the type-theory
proof assistant and its NbE goal engine. A session is scoped to the active
inference page. Opening a gate uses the page containing that gate; entering a
proposition uses the active page. The session keeps a transactional draft and
writes to the page only when `qed` succeeds.

Only proposition grammar is accepted as a proof target. `intro [name]` moves an
implication or quantified premise into a temporary hypothesis context; an
omitted name receives a generated `h1`, `h2`, ... name. `exact` may consume a
named temporary hypothesis, an active-page proposition, a shared deduction
rule, or proposition text, using semantic matching and never crossing page
boundaries.

`apply` matches the conclusion of a visible rule or theorem in reverse,
infers replacement values, and creates one subgoal per condition. This first
version does not treat `_` as an inference wildcard in the inference-layer
assistant; replacement parameters are either omitted for whole-rule reverse
matching or written explicitly. Ambiguous matches are reported as candidates
instead of being selected by list order. `have <proposition> <name>` creates a
temporary subgoal and binds its proven result under the supplied second
argument; for example, `have $0 h233`.

`tauto` is one replayable assistant command backed by MCPT. Its internal
derivation is not persisted or recorded as a rule; `entr`/`inln` may expand it
later on demand. All commands are atomic: failed parsing, matching, or proof
construction leaves the draft and history unchanged. Undo replays the command
history, and repeated requests are serialized or cancelled by generation.

`qed <name>` materializes the generated deduction steps in the active page,
then invokes the existing `m <name>` macro recorder; the active page is cleared
according to the existing `m` semantics. Bare `qed` writes the completed steps
without recording a macro. The resulting macro and page propositions use the
original proposition surface syntax. Proof drafts
are page-local and may be saved/restored with their command history, while
MCPT's internal steps are excluded. Recommendation buttons remain syntactic
"可能适用" hints only; kernel/deduction validation is authoritative.

### Command Details

The assistant consumes one binder per `intro [name]`: an implication premise is
added as a temporary hypothesis, while a universal binder introduces an
arbitrary replacement variable. `exact` resolves `p3` as proposition 3 in the
active page, a bare name as a local fact or shared rule, and a proposition text
as a semantic target; local facts take precedence on name collisions.

`apply <rule> [arguments...]` allows omitted trailing replacement arguments,
which are filled by reverse conclusion matching. The inference-layer assistant
does not support `_` wildcard arguments. `have <proposition> <name>` keeps the
named intermediate fact in the final derivation chain. Multiple subgoals are
processed depth-first in rule-condition order.

Metatheorem-backed commands use the unlock snapshot captured when the proof
page starts. Implication `intro` requires both conditional deduction (`c`) and
inverse deduction (`<`), while universal `intro` requires conditional universal
(`v`); branch tactics that introduce hypotheses inherit the implication-intro
requirements. Generated
deduction names such as `>rule` and `<rule` are accepted by `apply`/`exact` only
when that metatheorem prefix is unlocked and every underlying atomic rule is
visible in the selected proof scope. Newly generated helper deductions are
audited recursively, so `<`/`>` prefixes in their emitted substeps cannot bypass
the unlock state. Cached generated rules do not bypass these checks, and the
snapshot is persisted with deferred assistant steps.

Completed assistant steps are appended to the active page in generation order,
including temporary hypotheses and the final conclusion. A named `qed` writes
those rows and then performs `m <name>` as one transaction; a macro-name
collision or recording failure restores the page to its pre-qed state. `tauto`
writes one deferred MCPT/CPT node and leaves its internal enumeration steps for
later `entr`/`inln` materialization. `have` names are unique within a session;
`qed` names use the existing macro name validation and never overwrite a rule.
