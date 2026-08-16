# Deductrium

This branch used ai coding.

A game that combines mathematical formal systems and hyperbolic space in the browser using Typescript. Currently includes propositional logic, first-order logic, Peano axioms, ZFC set theory, and some type theory.

This optimization branch is not deployed to GitHub Pages. Run it through the local server or download a GitHub Release archive. Original online version: [wxyhly.github.io/deductrium](https://wxyhly.github.io/deductrium/).

## Local startup

The optimized type-theory engine runs in an isolated Node.js child process started by the local server, so do **not** open `index.html` directly with a `file://` URL.

For the Windows release package:

1. Install [Node.js 18 or newer](https://nodejs.org/).
2. Extract the archive.
3. Double-click `start.cmd`.
4. The default browser opens `http://127.0.0.1:4174/`.

The release package does not require `npm install`; its `package.json` only preserves the ES Module mode required by the browser scripts.

To run from source:

```powershell
npm install
npm run build
npm start
```

Use `npm run typecheck` to check TypeScript without emitting JavaScript. Set the `PORT` environment variable before starting if port `4174` is already occupied.

Each open game page creates an isolated Node.js type-theory child process on demand. The process runs core checking and the proof assistant in separate worker threads, so a long type check does not block tactic search. Closing the page disposes its session, and stopping the local server terminates any remaining child processes. The browser falls back to Web Workers only when the server truly does not expose the process API; a normally started release package always uses the isolated process.

The child process has a 2048 MB heap limit by default. Large saves can raise it before startup:

```powershell
$env:DEDUCTRIUM_TT_HEAP_MB=4096
node server.mjs
```

This heap cap is separate from the in-game inference resource multiplier: the former controls available Node.js memory, while the latter controls the amount of semantic-inference work allowed for one request.

The server also caps the maximum wait for one RPC at 30 minutes by default. Set `DEDUCTRIUM_TT_MAX_RPC_TIMEOUT_MS` to lower that cap. `DEDUCTRIUM_TT_MAX_PENDING` and `DEDUCTRIUM_TT_MAX_SESSIONS` limit queued requests per session and simultaneously open pages.

The type-theory process keeps validated definitions and inference caches alive between requests. Edits, moves, and disabled folders only invalidate the affected suffix. The proof assistant runs in its own worker thread, so tactic search and undo do not block the main page or wait behind core checking.

Run correctness regressions and the complex type-theory benchmark with:

```powershell
npm test
npm run benchmark
```

Timing workloads live under `tests/benchmarks/`. The benchmark reports the median of three runs and does not assert a machine-specific time limit. Use `BENCHMARK_RUNS` to change the sample count and `TT_BENCHMARK_TIMEOUT_MS` to change the per-theorem safety timeout.

### Packaging a release

Run this command from the project root:

```powershell
npm run package
```

The script runs regression tests, type-checks, and builds the project. It then starts the isolated process from the packaged directory and performs a health check plus a minimal type check before creating the runnable directory and ZIP archive under `release/`. It also prints the archive SHA256.

### Automated GitHub Releases

`.github/workflows/release.yml` runs the tests, builds the archive, and creates a GitHub Release whenever a `hott-v*` tag is pushed:

```powershell
git tag hott-v2026.08.16
git push origin hott-v2026.08.16
```

The `Package Release` workflow can also be run manually. With no tag input it automatically uses `hott-vYYYY.MM.DD` in China Standard Time; rerunning it on the same date retargets that release and replaces its ZIP with the latest commit.

Game progress is stored in the browser for the current origin. Export a text save from the Progress Layer before changing browsers or ports.

## Deduct Layer Tutorial

### Command Input Box
The command input box is at the bottom. When prompted to enter a command, you can enter the content in the brackets of the buttons at the bottom of the proposition table to execute the command. The effect is the same as clicking the button. A command may be completed by entering it multiple times. If you want to exit halfway, please press the `Esc` key to execute other commands.

### Deduction
Rules in the deduction rule table \[D\] are all in this form:
`( A1, A2, ..An ⊢ C )`  
This means if conditions `A1`, `A2`, ..., `An` are all propositions in the \[P\] table, executing this rule will lead to add conclusion `C` to the proposition table. To execute a deduction rule, first ensure that there is no command being executed (if there is, press Esc to cancel it), then:  
- Enter the rule name  
- Or directly click the rule in \[D\] table with the mouse  

When executing a rule, the command prompt will ask you to specify which propositions in the \[P\] table correspond to conditions `A1`, `A2`, ..., `An`. You can directly select in the theorem table. Words starting with `$` in expressions are called replacement variables. You need to specify the value of the replacement variable before deduction. The system will automatically match replacement variables via conditional propositions; if undetermined, the player needs to enter the replacement content according to the prompt. The replacement content must be a legal expression. A legal expression can be a legal formula or a legal item.

### Well-Formed Formulas (WFF)
Well-formed formulas (WFF) are propositions whose truth can be determined. The simplest valid formulas (atomic formulas) are any words. Words must contain only lowercase letters, numbers, and `$`. Note that uppercase letters may be reserved by the system and are not recommended. 
WFFs can be combined into more complex WFFs using propositional logic connectives, such as `a > b`, `((1 @ 3) & ~a)`. Brackets are used to distinguish the priority of operators. See the symbol list below for details.

### Valid Terms
Valid terms represent concepts like sets, numbers, or set elements. words can be valid terms (atomic terms), but no word can be both a term and formula. Terms can be combined into complex terms using function symbols, such as `aU{b,c}`, `1+(2*(x+3))`; they can also form WFFs via predicate symbols, such as `1+1=2`, `x@{x,y}`.

### Common Symbol List  
|Input|Display|Usage|
|---|---|---|
|`>`|`→`|`$0 > $1`|
|`~`|`¬`|`~$0`|
|`\|`|`∨`|`$0 \| $1`|
|`&`|`∧`|`$0 & $1`|
|`<>`|`↔`|`$0 <> $1`|
|`V`|`∀`|`V$0:$1`|
|`E`|`∃`|`E$0:$1`|
|`@`|`∈`|`$0 @ $1`|
|`=`|`=`|`$0 = $1`|

### Quick Input
When the command input is waiting for a valid expression, hovering the mouse over propositions/rules in the table and clicking (or tapping on mobile) will automatically insert the highlighted content at the cursor. If text is selected in the command line, all instances of the selected text will be replaced with the highlighted content.

### Hypotheses and Macro Recording
Since propositions in the table are derived via deduction rules, it would be troublesome if many identical and complex deduction steps are involved. After unlocking the corresponding rule, you can click "Record Macro" to package all deduction steps in the proposition list into a single macro and add it to the \[D\] rule table for multiple use. It is recommended to use `$`-prefixed atomic expressions in propositions, which will upgrade specified words to replacement variables when recorded as deduction rules, allowing replacement with any expression.  

To record a macro with hypotheses, click the "Hypothesis" button to input hypotheses when the proposition list is empty, then proceed with deduction and macro recording.

### Metarules
Similar to rules deriving propositions, metarules derive deduction rules with similar operation methods. All metarules are provided by the system and unlocked gradually in-game; The specific usage of each metarule can be found in the in-game instructions. Many metarules have "[]" symbols in front of their names, and the letters in them can be used to quickly generate and use these meta-rules.

### Assertion Mechanism
In first-order logic, replacement variables often require restrictions like "free occurrence" or "substitutability". Since `$`-prefixed expressions may be arbitrarily replaced when recorded as macros, conditions like "free occurrence" or "substitutability" in the expressions are temporarily undetermined. The system uses assertion functions like `#nf` and `#rp` to mark them, with fuzzy logic processing. When `$`-prefixed expressions are later substituted with specific values, the system checks if these values satisfy the assertions. If assertions are successfully verified, the corresponding assertion functions will be removed.


## Type Layer Tutorial
The Type Layer lists known unlocked types and other expressions in the "Axiom Types" list. Unlike the Deduct Layer, these are not executable but for reference only. To derive propositions, directly input expressions in the proposition list; the system will automatically recognize and check the validity of your proof evidence. Note: in type layer, mechanism is completely different: 1. the Type Layer prohibits all undefined free variables(Also recommend to use lowercase letters for bound variables); 2. The universal matcher (`$`) mechanism is no longer available.

There is a special "defined equality" mechanism in the type layer, that is, if two expressions are defined to be equal, the system will not distinguish them anywhere. Another similar concept is propositional equality. Propositional equality (eq) is similar to the equality predicate in first-order logic, but is just a proposition.

### Common Symbol List  
|Input|Display|Usage|
|---|---|---|
|`->`|`→`|`x -> y`|
|`L`|`λ`|`Lx:a,b`|
|`P`|`Π`|`Px:a,b`|
|`S`|`Σ`|`Sx:a,b`|
|`X`|`×`|`aXb`|

## Proof Assistant
Manually constructing proof evidence (i.e., values of corresponding types) for complex propositions is challenging. The Proof Assistant can automate some tasks: First, enter the proposition to be proved in the proposition list, then click the plus button in proof strategies and select the proposition. The Proof Assistant will guide you to complete the construction of the value of the target type.
