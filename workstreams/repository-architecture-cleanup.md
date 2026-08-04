# Repository Architecture Cleanup - Deletion-First Plan - 2026-08-04

## Status and Authorization Boundary

This is an execution-ready plan, not authorization to execute it.

Planning and read-only verification are authorized. Production code, tests,
configuration, documentation, generated artifacts, Git worktrees, branches, and
tracked history must remain unchanged until Q explicitly authorizes execution.

The evaluation baseline observed before this plan was written:

- branch: `main`
- tracked worktree: clean
- untracked checkpoints: `notes-breakthrough.md`,
  `notes-breakthrough-interp.md`, and `notes-cleanup-evaluation.md`
- full suite: 1,220 passed in 99.91 seconds
- Ruff: clean
- Pyright: 0 errors and 0 warnings in `basic` mode

These are historical planning inputs, not current execution evidence. Re-run the
preflight at the start of implementation.

## Literal Outcome

Converge `cold_start` on explicit ownership boundaries without retaining the old
surfaces through wrappers, aliases, re-exports, compatibility modules, or dual
paths:

1. trusted syntax and proof classes own only intrinsic structure and checking
   semantics;
2. one untrusted codec owns all Hamblin serialization;
3. one small exact-dispatch, iterative emitter mechanism supports external text
   representations without adding `accept()` or presentation methods to core
   objects;
4. human notation and Lean remain separate language adapters;
5. the monolithic Lean module is replaced by real Lean sub-owners;
6. derived theorem builders are owned by their theories rather than a generic
   `proofs.py` bucket;
7. the verifier, mutation tool, local gate, CI, and expensive tests express and
   enforce their real contracts;
8. durable documentation has one current truth and process history does not
   masquerade as current architecture.

Completion means the forbidden production surfaces have zero search hits, all
callers use the target owners directly, the complete runtime gates pass, and no
old and new implementation paths coexist.

## Target Architecture

```text
cold_start/
|-- syntax.py                 canonical syntax and intrinsic structural semantics
|-- proof.py                  canonical proof terms and trusted rule semantics
|-- sequent.py                derived judgement and sort invariant
|-- checker.py                trusted orchestration and theory definitions
|-- codec.py                  untrusted Hamblin wire boundary
|-- emitter.py                untrusted exact dispatch and iterative text emission
|-- notation.py               human notation parser and emitter
|-- verify.py                 proof-verification CLI adapter
|-- lean/
|   |-- syntax.py             Lean statement rendering, parsing, and substitution
|   |-- proof.py              proof-term to Lean export
|   |-- corpus.py             corpus specification, generation, and checked path
|   `-- __main__.py           `python -m cold_start.lean`
|-- tactics.py                untrusted proof-producing tactics
|-- presburger_proofs.py      Presburger-derived theorem builders
|-- peano_proofs.py           Peano-derived theorem builders
`-- robinson_proofs.py        Robinson-derived theorem builders
```

Existing theory, interpretation, bridge, divisibility, algebra, and rigidity
modules remain in their current domain roles unless breakage review proves a
specific ownership violation.

### Trusted base

The documented trusted base is the exact-type gates and guarded structural,
derivation, and sort-checking behavior in:

- `syntax.py`
- `proof.py`
- `sequent.py`
- `checker.py`
- each selected theory's concrete axioms and induction data

`codec.py`, `emitter.py`, `notation.py`, `verify.py`, the Lean package, tactics,
theorem builders, tests, and generated artifacts remain untrusted. The checker
must reject bad decoded or generated data independently of those layers.

### Canonical type ownership

- `syntax.py` owns one immutable canonical syntax-type set used by its trust gate.
- `proof.py` owns one immutable canonical proof-type set used by its trust gate.
- The codec and external emitters read those owner sets for registry construction
  and exhaustiveness checks; they do not duplicate the lists by hand.
- Adding a canonical type must make every exhaustive external emitter either
  implement it or reject it explicitly.

### External emitter contract

`emitter.py` owns only:

- a `Visit[value, context]` work item;
- a `Piece = str | Visit[...]` representation;
- a `@case(...)` marker that records exact handled types without wrapping the
  method or mutating a global registry;
- class-creation construction of one immutable exact-type dispatch table;
- duplicate, missing, and unexpected-case validation against `covers=...`;
- an iterative emit-and-join loop.

Concrete emitter handlers return declarative pieces. They do not mutate a shared
output list or work stack. Dispatch is `type(value)` lookup, never MRO/subclass
dispatch.

The following are deliberately not part of this mechanism:

- `Node.accept(visitor)` or `Pf.accept(visitor)`;
- `functools.singledispatch` / `singledispatchmethod`;
- global mutable decorator registries;
- method-name conventions such as `visit_<ClassName>`;
- validation, derivation, rewriting, interpretation translation, or model
  evaluation;
- a universal visitor abstraction that hides different traversal semantics.

### Representation ownership

- `notation.py` owns human syntax, precedence, quoting, binder names, and parsing.
- `lean/syntax.py` owns Lean statement syntax and its intentionally narrower
  accepted fragment.
- `lean/proof.py` owns translation of proof rules to Lean proof terms.
- `lean/corpus.py` owns which proofs enter the generated corpus and when builders
  are invoked.
- Unsupported canonical cases receive explicit rejecting handlers; omission is
  not used to mean unsupported.

## Forbidden Surfaces

The completed architecture must not retain:

- `cold_start/lean.py` as a monolithic module;
- public re-exports from `cold_start.lean` that preserve the old import surface;
- the old notation and Lean `_push` / `_emit` worklist implementations;
- `_Export._handlers()` or any dispatch map rebuilt per visited proof node;
- handler association duplicated both in a decorator and a manual mapping;
- mutable binder-stack `pop` control actions where immutable visit context owns
  scope;
- Lean, notation, or external visitor methods on `Node`, `Term`, `Formula`, `Pf`,
  or their concrete subclasses;
- MRO/subclass-based external dispatch;
- `import hamblin` in `syntax.py` or `proof.py`;
- syntax/proof-owned `term_to_bytes`, `term_from_bytes`, `formula_to_bytes`,
  `formula_from_bytes`, `to_bytes`, or `from_bytes` compatibility paths;
- `cold_start/proofs.py` or imports from `cold_start.proofs`;
- theorem-builder re-export facades preserving the generic proof module;
- a mutation tool that rewrites a live checkout target;
- a gate that hides the pytest result or calls basic Pyright checking "strict";
- multiple durable files claiming conflicting current state;
- volatile test totals presented as timeless documentation;
- abandoned registered worktrees removed without a fresh inventory and explicit
  destructive authorization.

## Surfaces Explicitly Kept

- Intrinsic polymorphic methods on canonical syntax and proof classes.
- Exact-type trust gates in `syntax.py` and `proof.py`.
- `children`, `subnodes`, `map_children`, and scoped rebuilding for generic
  structural traversal.
- Structural `repr` behavior on syntax nodes; it is not human or Lean notation.
- Separate human and Lean parsers.
- The checked-in generated `lean_export/ColdStart.lean` corpus, provided its
  up-to-date and Lean-compilation gates continue to pass.
- Domain-specific modules whose current ownership is already correct.

## Global Search Gates

Run scoped gates after each relevant slice and all gates at fixed point:

```powershell
rg -n "import hamblin|from hamblin" cold_start\syntax.py cold_start\proof.py
rg -n "term_to_bytes|term_from_bytes|formula_to_bytes|formula_from_bytes|\bto_bytes\b|\bfrom_bytes\b" cold_start tests README.md ARCHITECTURE.md
rg -n "from cold_start\.proofs|from \.proofs|cold_start\.proofs" cold_start tests README.md ARCHITECTURE.md
rg -n "_handlers\(|def _push|def _emit\(" cold_start\notation.py cold_start\lean
rg -n "singledispatch|singledispatchmethod|def accept|\.accept\(" cold_start tests
rg -n "legacy|compat|fallback|shim|facade|re-export" cold_start tests README.md ARCHITECTURE.md
rg -n "cold_start[\\/]lean\.py|from cold_start\.lean import|from \.lean import" cold_start tests README.md ARCHITECTURE.md
```

Expected fixed-point results:

- Hamblin hits occur only in `codec.py`, dependency metadata, tests explicitly
  testing the codec, and accurate documentation.
- Old serialization names have zero hits unless the final codec API deliberately
  retains one of the names as its actual owner API; no old module owns them.
- Generic proof-module imports have zero hits.
- Old emitter loops and per-node handler-map reconstruction have zero hits.
- No compatibility or re-export surface preserves deleted ownership.
- All Lean imports name the real sub-owner modules.

## Global Runtime Gates

Use `uv` for all Python gates:

```powershell
uv run pytest
uv run ruff check .
uv run pyright
uv run python -m cold_start.lean
```

Then prove generated corpus stability and foreign-kernel acceptance through the
existing focused Lean tests. If the local Lean executable is unavailable, record
that environment limitation separately; do not call the foreign-kernel gate green.

The final test run must print its actual summary. Compare duration with the
99.91-second planning baseline, while treating correctness as mandatory and speed
as a measured improvement rather than a reason to remove coverage.

## Commit and Rollback Rules

- One bounded ownership reduction per commit.
- Every commit must be green under its focused gates before moving to another
  slice.
- Stage intended paths only; never use `git add -A`.
- Preserve unrelated and untracked user files.
- Do not keep a failing intermediate deletion merely to accumulate fixes across
  unrelated owners.
- If a slice cannot reach its stated search and runtime gates, restore only that
  slice through a new corrective patch or revert its atomic commit; never use
  destructive reset against unrelated work.
- Commit messages must state the governing ownership principle and name the old
  surface that no longer exists.

## Iteration 0 - Execution Preflight

### Slice

- repository and registered worktree state
- installed `uv`, Python, Lean, Ruff, Pyright, and Git tooling

### Actions

1. Read current `cold_start/CLAUDE.md`, this plan, and active checkpoint notes.
2. Run:

   ```powershell
   git status --short --branch
   git worktree list --porcelain
   git branch --show-current
   uv run pytest -o addopts= -q --durations=20
   uv run ruff check .
   uv run pyright
   ```

3. Inventory every registered secondary worktree and its dirty state.
4. Do not remove or alter a locked, live, dirty, or unexplained worktree.
5. Record the fresh baseline and any drift from the planning baseline.

### Completion gate

- Current state is understood and recorded.
- No unrelated tracked or untracked content is endangered.
- The implementation baseline is green or any pre-existing failure is isolated
  and explicitly accepted before cleanup begins.

## Iteration 1 - Tool and Gate Safety

### Owners after cleanup

- `tools/mutate.py`: mutation orchestration in a verified disposable worktree
- `tools/gate.ps1`: honest local full-gate orchestration

### Dispositions

- in-place mutation of a caller-supplied source path: **delete**
- automatic restoration as the sole safety mechanism: **delete**
- disposable-worktree creation, validation, mutation, and cleanup: **rewrite**
- duplicate pytest quiet flag: **delete**
- claim that basic Pyright mode is strict typing: **rewrite**
- explicit native-process exit-code handling: **keep**

### Required behavior

- Mutation refuses to target the primary or any non-disposable checkout.
- Every mutation runs against a validated temporary worktree/copy owned by that
  invocation.
- The tool reports the exact mutation target and never relies on a broad path or
  unresolved environment variable.
- The gate prints the pytest count, duration, Ruff result, Pyright mode/result,
  and final status.

### Focused gates

```powershell
uv run pytest tests\test_checker.py tests\test_quantifiers.py tests\test_logic.py tests\test_sorts.py tests\test_rings.py
uv run ruff check tools tests
uv run pyright
```

Add tests for mutation-target refusal and gate failure propagation where practical.

### Commit boundary

Commit tool safety independently of architectural production refactors.

## Iteration 2 - Exact Iterative Emitter

### Slice

- new `cold_start/emitter.py`
- `cold_start/notation.py`
- Lean statement emitter currently in `cold_start/lean.py`
- Lean proof emitter currently in `cold_start/lean.py`
- focused notation and Lean tests

### Delete first

Delete the old adapter-owned worklist loops and handler mapping from the active
slice before recreating their capabilities through the target emitter. Do not
leave both mechanisms callable.

### Owners and dispositions

- `Visit` and `Piece`: **create** in `emitter.py`
- `@case`: **create** as metadata-only decorator in `emitter.py`
- exact immutable case table: **create** in `emitter.py`
- iterative emit-and-join driver: **create** in `emitter.py`
- notation `_push`, `_emit`, and mutable `pop`: **delete/rewrite**
- Lean syntax `_push`, `_emit`, and local loop: **delete/rewrite**
- Lean proof `_handlers()`, `_emit_proof`, and local loop: **delete/rewrite**
- adapter-specific precedence, names, environments, and error policy: **keep** in
  their concrete owners

### Required invariants

- The decorator does not wrap handlers or register globally.
- Class construction rejects duplicate, missing, or unexpected cases.
- Exact `type(value)` dispatch rejects hostile or unknown subclasses.
- Every canonical type is handled or explicitly rejected.
- Handlers return pieces and do not receive the output list or work stack.
- Binder scope travels immutably in visit context.
- Rendering remains iterative and linear for deep inputs.

### Focused gates

```powershell
uv run pytest tests\test_notation.py tests\test_lean.py
uv run pytest tests\test_properties.py -k "deep or iterative or repr"
uv run ruff check cold_start\emitter.py cold_start\notation.py cold_start\lean.py tests\test_notation.py tests\test_lean.py
uv run pyright
```

Add direct tests for duplicate-case rejection, missing-case rejection, exact-type
dispatch, explicit unsupported cases, and deep iterative rendering.

### Search completion

- No old notation/Lean adapter `_push` or `_emit` implementation remains.
- No `_handlers()` dispatch map remains.
- No handler both carries `@case` metadata and appears in a manual registry.

### Commit boundary

Commit only when all three production emitters use the one mechanism and the old
mechanisms are gone.

## Iteration 3 - Lean Ownership Package

### Slice

- delete `cold_start/lean.py`
- create `cold_start/lean/syntax.py`
- create `cold_start/lean/proof.py`
- create `cold_start/lean/corpus.py`
- create `cold_start/lean/__main__.py`
- update all Lean callers, tests, commands, and documentation

### Ownership dispositions

- Lean names, reserved words, substitution, rendering, statement parsing, and
  universal closure: **move** to `lean/syntax.py`
- proof-rule export state and handlers: **move** to `lean/proof.py`
- corpus entries, Nat discharge data, generated headers, corpus generation, and
  output path: **move** to `lean/corpus.py`
- CLI printing/writing behavior: **move** to `lean/__main__.py`
- `cold_start/lean.py`: **delete**
- old module-level public re-export surface: **delete**

### Breakage review

For every old `from cold_start.lean import ...`:

- statement/parser callers import `cold_start.lean.syntax`;
- proof exporters import `cold_start.lean.proof`;
- corpus callers import `cold_start.lean.corpus`;
- CLI users keep the real command `python -m cold_start.lean` through
  `__main__.py`, not a forwarding function.

### Focused gates

```powershell
uv run pytest tests\test_lean.py
uv run python -m cold_start.lean
uv run ruff check cold_start\lean tests\test_lean.py
uv run pyright
```

### Search completion

- `cold_start/lean.py` does not exist.
- No caller imports the old combined surface.
- No package initializer re-exports old names.
- The generated corpus is byte-for-byte current and compiles under Lean.

## Iteration 4 - Codec Ownership

### Slice

- `cold_start/syntax.py`
- `cold_start/proof.py`
- new `cold_start/codec.py`
- `cold_start/verify.py`
- codec and property tests

### Delete first

Remove syntax/proof-owned encoding functions and Hamblin registries/imports, then
use the exposed breakage to migrate every real codec caller.

### Owners and dispositions

- canonical syntax-type set: **keep/consolidate** in `syntax.py`
- canonical proof-type set: **keep/consolidate** in `proof.py`
- Hamblin registry construction: **move** to `codec.py`
- term/formula/proof encode/decode entrypoints: **move/rename** to explicit codec
  owner APIs
- root-kind checks after decoding: **rewrite** with exact canonical types
- old syntax/proof serialization functions: **delete**
- Hamblin imports in trusted modules: **delete**

### Required invariants

- Decoded data remains untrusted and is fully validated before checking.
- Unknown opcodes, wrong root kinds, hostile field values, and deep payloads are
  rejected cleanly.
- Encoding remains deterministic and recursion-free.
- Core checking does not import the codec.
- The fresh-process verifier imports the codec and checker in the correct direction.

### Focused gates

```powershell
uv run pytest tests\test_checker.py tests\test_properties.py tests\test_relations.py tests\test_robinson_divisibility.py
uv run ruff check cold_start\codec.py cold_start\syntax.py cold_start\proof.py cold_start\verify.py tests
uv run pyright
```

### Search completion

- `syntax.py` and `proof.py` contain no Hamblin imports or codec functions.
- Old serializer imports and call sites have zero hits.
- No compatibility wrappers remain in the old owners.

## Iteration 5 - Theory-Owned Proof Libraries

### Slice

- delete `cold_start/proofs.py`
- create `cold_start/presburger_proofs.py`
- create `cold_start/peano_proofs.py`
- extend `cold_start/robinson_proofs.py`
- update all production/test/Lean callers

### Ownership classification

- Presburger numeral addition and addition-law builders: **move** to
  `presburger_proofs.py`
- Peano multiplication examples, laws, distributivity, associativity, and
  positive cancellation: **move** to `peano_proofs.py`
- Robinson numeral addition and bridge-derived results: **move/consolidate** in
  `robinson_proofs.py`
- generic `proofs.py`: **delete**
- re-export module or aliases preserving `cold_start.proofs`: **forbidden**

### Breakage review rule

Do not route imports based only on their old location. For every builder, identify
the theory whose axioms/checking contract it consumes and move it to that owner.
If a builder genuinely crosses theories, place it with the bridge/interpretation
owner rather than arbitrarily in one theorem library.

### Focused gates

```powershell
uv run pytest tests\test_presburger.py tests\test_mul_laws.py tests\test_robinson.py tests\test_tactics.py tests\test_model.py tests\test_sorts.py tests\test_lean.py
uv run ruff check cold_start tests
uv run pyright
```

### Search completion

- `cold_start/proofs.py` does not exist.
- `cold_start.proofs` imports have zero hits.
- No new generic theorem-builder bucket or re-export surface exists.

## Iteration 6 - Verifier CLI Contract

### Slice

- `cold_start/verify.py`
- verifier subprocess tests

### Dispositions

- manual index-based argument parsing: **delete**
- explicit one-path/optional-stdin and named-theory parser: **rewrite**
- mutable repeated theory loading: **consolidate** into one owned mapping
- unscoped `open(...).read()`: **rewrite** with a managed input boundary
- uncaught missing files and malformed CLI arguments: **rewrite** into stable
  nonzero CLI outcomes
- checker rejection semantics: **keep**

### Required cases

- stdin with default theory;
- file with explicit theory;
- unknown theory;
- missing `--theory` value;
- duplicate or unexpected positional paths;
- missing/unreadable file;
- malformed bytes;
- well-formed but invalid proof;
- successful Robinson and Presburger proofs.

### Focused gates

```powershell
uv run pytest tests\test_checker.py -k "cross_process or verify"
uv run ruff check cold_start\verify.py tests\test_checker.py
uv run pyright
```

## Iteration 7 - Test Runtime Without Coverage Loss

### Slice

- shared pytest fixtures/configuration
- expensive proof-builder, Lean-corpus, model, sort, and foreign-kernel tests

### Baseline

Planning observation: 1,220 tests in 99.91 seconds. Re-measure at execution
preflight with `--durations=20`.

### Allowed reductions

- session/module-scoped sharing of immutable proof terms;
- one generated Lean corpus fixture reused by independent assertions;
- one positive Lean compile and one corrupted-export rejection per necessary
  contract;
- removal of repeated construction that provides no distinct assertion.

### Forbidden reductions

- deleting model or sort soundness coverage;
- lowering Hypothesis examples merely to improve the headline duration;
- marking slow tests skipped or xfailed by default;
- replacing foreign-kernel execution with string-only assertions;
- sharing mutable state that couples test order;
- caching production results solely to speed tests without a production contract.

### Gates

```powershell
uv run pytest -o addopts= -q --durations=20
uv run ruff check tests
uv run pyright
```

Record before/after total duration and slowest tests. The suite must retain the
same behavioral contracts even if the speed improvement is smaller than expected.

## Iteration 8 - CI and Typing Truth

### Slice

- repository CI configuration
- `tools/gate.ps1`
- `pyrightconfig.json`
- relevant README instructions

### Dispositions

- no automated repository gate: **create** CI using the same owned commands
- ambiguous use of "strict": **delete/rewrite**
- Pyright `basic` mode represented as strict: **forbidden**
- immediate blind repository-wide strict-mode flip: **forbidden**

### Target

- CI runs tests, Ruff, Pyright in its declared mode, generated-corpus freshness,
  and Lean compilation when the runner installs/provides Lean.
- Local and CI commands do not drift.
- If strict typing is desired, enable it in bounded modules with explicit error
  counts and dedicated commits; do not mix the migration with architecture moves.

### Gates

- Validate workflow syntax using the repository's available tooling.
- Run `tools/gate.ps1` locally and capture its complete output.
- Confirm CI uses the lockfile and supported Python version.

## Iteration 9 - Documentation and Historical Hygiene

### Durable document owners

- `README.md`: purpose, supported usage, current high-level capabilities
- `ARCHITECTURE.md`: normative ownership and trust model
- `cold_start/CLAUDE.md`: repository working rules
- `papers/*/notes.md`: primary-source provenance and mathematical interpretation
- `reports/*`: reproducibility evidence and generated-artifact notes
- `workstreams/*`: plans or fixed-point records only while they remain useful

### Dispositions

- false dependency-free claim: **delete/rewrite**
- incomplete trusted-base statement: **rewrite**
- omission of `Rel`: **rewrite**
- volatile hard-coded test totals in durable docs: **delete**
- completed roadmap work still called pending: **rewrite/delete**
- stale `NOTES.md`: **delete after harvesting unique durable facts**
- chronological `notes-cold-start.md`: **delete after harvesting unique durable
  architectural rationale**
- completed workstream logs: **review individually; delete when Git history and
  durable architecture docs already own their useful content**
- generated Lean corpus: **keep and verify**
- live untracked campaign notes: **preserve unless their owner explicitly closes
  or archives them**

### Worktree hygiene

Inventory `.claude/worktrees` and registered Git worktrees again. Any deletion is
a separate destructive action requiring exact path validation and explicit user
authorization. Do not bundle worktree removal into documentation cleanup.

### Gates

```powershell
rg -n "dependency-free|pytest:|passed|Next step \(not started\)|Trust =|only trusted|Rel" README.md ARCHITECTURE.md NOTES.md cold_start\CLAUDE.md
rg -n "cold_start\.lean|cold_start\.proofs|to_bytes|from_bytes" README.md ARCHITECTURE.md cold_start\CLAUDE.md
uv run pytest
uv run ruff check .
uv run pyright
```

Documentation must describe the final code, not an intended intermediate state.

## Final Fixed-Point Audit

1. Read every production file touched by the workstream in full.
2. Classify every remaining public class, function, registry, codec entrypoint,
   emitter case, CLI, theorem builder, and compatibility-looking surface as keep,
   delete, move, consolidate, or rewrite.
3. Run all global search gates.
4. Run all global runtime gates and Lean compilation.
5. Confirm generated corpus equality.
6. Confirm the current branch and exact intended diff.
7. Confirm untracked campaign notes and unrelated files are preserved.
8. Record every atomic commit and gate result in this file or a successor
   fixed-point log.

The workstream reaches fixed point only when:

- the old monolithic Lean module is absent;
- old emitter loops and handler maps are absent;
- core classes contain no external representation behavior;
- codec ownership is singular and the trusted core does not import it;
- generic theorem-builder ownership is absent;
- verifier/tool failure paths are explicit and tested;
- test coverage is preserved and runtime is remeasured;
- local/CI/type-checking claims are accurate;
- durable documentation agrees with current code;
- no wrapper, alias, facade, fallback, or re-export keeps a forbidden surface
  alive under another spelling.

## Next Action

Execution was authorized by Q on 2026-08-04. Begin Iteration 1 from the completed
preflight record below.

## Execution Record

### Iteration 0 - Preflight - Complete

State read:

- `main` at `82ce128`
- tracked worktree clean before this plan was added
- preserved untracked checkpoints: `notes-breakthrough.md`,
  `notes-breakthrough-interp.md`, and `notes-cleanup-evaluation.md`
- two registered secondary worktrees on their existing branches and commits;
  both clean, neither modified or removed

Gate results:

- Pass: `uv run pytest -o addopts= -q --durations=20`
  - 1,242 passed in 103.39 seconds
- Pass: `uv run ruff check .`
  - all checks passed
- Pass: `uv run pyright`
  - 0 errors, 0 warnings, 0 informations in configured `basic` mode

Baseline drift:

- The suite grew from the planning observation of 1,220 tests to 1,242 after
  recent merged divisibility work.
- The execution performance baseline is 103.39 seconds, not the older 99.91
  seconds.

Commit:

- `f37d8b0 plan: record repository cleanup preflight`

Next slice:

- Iteration 1 - tool and gate safety

### Iteration 1 - Tool and Gate Safety - Complete

Surfaces:

- caller-supplied in-place mutation target
  - Disposition: delete
  - Owner after cleanup: disposable detached Git worktree created by
    `tools/mutate.py`
  - Action: source arguments are validated as tracked repository-relative files;
    all writes occur only at the corresponding path in the temporary worktree.
- mutation cleanup
  - Disposition: rewrite
  - Owner after cleanup: verified Git worktree lifecycle
  - Action: create and verify a detached worktree, remove it with Git, require the
    directory to be absent, then remove only the known-empty temporary parent.
- double-quiet pytest gate
  - Disposition: delete
  - Owner after cleanup: `pyproject.toml` supplies the single quiet setting.
- ambiguous strict Pyright label
  - Disposition: rewrite
  - Owner after cleanup: `tools/gate.ps1` reports `pyright (basic)`.

Red evidence:

- Fail: `uv run pytest -o addopts= -q tests\test_tools.py`
  - 3 failed: safe resolver absent, absolute mutation path accepted, gate still
    double-quieted pytest and did not name basic mode.

Green evidence:

- Pass: `uv run pytest -o addopts= -q tests\test_tools.py`
  - 3 passed in 0.20 seconds
- Pass: focused checker/quantifier/logic/sort/ring/tool group
  - 75 passed in 30.62 seconds
- Pass: `uv run ruff check tools tests`
  - all checks passed after mechanical import sorting
- Pass: `uv run pyright`
  - 0 errors, 0 warnings, 0 informations
- Pass: `uv run python tools\mutate.py cold_start\peano.py`
  - disposable worktree created, verified, and removed; 0 mutation sites; registered
    worktree inventory returned exactly to its pre-run set.

Commit:

- `6e6d542 tools: isolate mutation and report honest gates`

Next slice:

- Iteration 2 - exact iterative emitter

### Iteration 2 - Exact Iterative Emitter - Complete

Surfaces:

- repeated adapter worklist loops
  - Disposition: consolidate
  - Owner after cleanup: `cold_start/emitter.py`
  - Action: `Visit`, metadata-only `@case`, immutable class-built exact dispatch,
    tuple-piece validation, and iterative emit-and-join now form the only external
    text-emission machine.
- notation type switch, mutable binder scope, and `pop` action
  - Disposition: delete/rewrite
  - Owner after cleanup: notation-owned decorated cases with immutable scope in
    `_FormatContext`.
- Lean syntax type switch
  - Disposition: delete/rewrite
  - Owner after cleanup: decorated Lean syntax cases; `Rel` is an explicit rejection.
- Lean proof `_handlers()` and mutable output/worklist handlers
  - Disposition: delete/rewrite
  - Owner after cleanup: all canonical proof rules are decorated cases returning
    pieces with `_ProofContext` carrying substitutions and hypotheses.
- canonical type metadata
  - Disposition: consolidate/keep
  - Owner after cleanup: `CANONICAL_NODE_TYPES` in `syntax.py` and
    `CANONICAL_PROOF_TYPES` in `proof.py`.

Red evidence:

- Error: `uv run pytest -o addopts= -q tests\test_emitter.py`
  - collection failed because `cold_start.emitter` did not exist.

Green evidence:

- Pass: direct emitter contract tests
  - 6 passed in 0.04 seconds
- Pass: emitter, notation, and complete Lean test files
  - 63 passed in 17.78 seconds
- Pass: deep/iterative/repr property slice
  - 22 passed, 2 deselected in 18.72 seconds
- Pass: scoped Ruff
  - all checks passed
- Pass: `uv run pyright`
  - 0 errors, 0 warnings, 0 informations
- Pass: old surface search
  - zero `_handlers(`, `def _push`, or `def _emit(` hits in notation/Lean production
- Reviewed: remaining `accept` hits are the notation parser's token-consumption
  method and `Theory.accepts`, not object visitor dispatch; parsers were explicitly
  outside the emitter replacement.

Commit:

- `be1fdca refactor: unify external text emitters`

Next slice:

- Iteration 3 - Lean ownership package

### Iteration 3 - Lean Ownership Package - Complete

Surfaces:

- combined `cold_start/lean.py` ownership
  - Disposition: delete/split
  - Owners after cleanup: statement syntax in `lean/syntax.py`, checked proof
    export in `lean/proof.py`, generated corpus in `lean/corpus.py`, and the real
    command entry point in `lean/__main__.py`.
- old module-level public re-export surface
  - Disposition: delete
  - Action: callers import their concrete owner; no package `__init__.py` facade
    or compatibility forwarding surface exists.
- Nat discharge knowledge used during theorem application
  - Disposition: move/inject
  - Owner after cleanup: `lean/corpus.py` owns the data and passes it explicitly
    into proof rendering, avoiding a proof-to-corpus dependency cycle.
- checked-in Lean output path
  - Disposition: keep/rebase
  - Owner after cleanup: `lean/corpus.py` resolves the repository-level
    `lean_export/ColdStart.lean` path from the deeper package location.

Red evidence:

- Error: `uv run pytest -o addopts= -q tests\test_lean.py`
  - collection failed because `cold_start.lean` was still a module, so
    `cold_start.lean.corpus` did not exist.

Green evidence:

- Pass: complete Lean suite after the ownership split
  - 43 passed in 16.44 seconds, including foreign-kernel compilation.
- Pass: `uv run python -m cold_start.lean`
  - wrote the canonical corpus path; the checked-in generated file has no diff.
- Pass: scoped Ruff
  - all checks passed after mechanical import sorting and formatting.
- Pass: scoped Pyright
  - 0 errors, 0 warnings, 0 informations.
- Pass: ownership searches
  - `cold_start/lean.py` and `cold_start/lean/__init__.py` are both absent;
    no old combined-surface imports remain in production or tests.

Commit:

- `244e814 refactor: split Lean representation owners`

Next slice:

- Iteration 4 - general codec owner

### Iteration 4 - Codec Ownership - Complete

Surfaces:

- Hamblin imports and registries in trusted data owners
  - Disposition: delete/move
  - Owner after cleanup: `cold_start/codec.py` builds syntax and proof registries
    from the canonical type sets.
- syntax/proof-owned byte entrypoints
  - Disposition: delete/rename
  - Owner after cleanup: explicit `encode_term`/`decode_term`,
    `encode_formula`/`decode_formula`, and `encode_proof`/`decode_proof` APIs in
    `codec.py`.
- root and structural validation
  - Disposition: strengthen
  - Action: encoders and decoders require exact canonical roots and validate the
    complete structure; standalone open term fragments are validated at the
    minimum binder depth required by their bound-variable indices.
- fresh-process verifier wire input
  - Disposition: migrate
  - Owner after cleanup: `verify.py` imports `decode_proof` from the codec, then
    passes its validated result to the independently validating checker.

Red evidence:

- Error: `uv run pytest -o addopts= -q tests\test_codec.py`
  - collection failed because `cold_start.codec` did not exist.
- Fail: first focused property run
  - 1 failed, 73 passed because eager depth-zero term validation rejected the
    existing valid open-fragment round trip for `BVar(0)`.
  - Resolution: term validation computes the minimum closing depth iteratively;
    formula and proof roots remain locally closed at depth zero.

Green evidence:

- Pass: direct codec contract tests
  - 6 passed in 0.05 seconds.
- Pass: codec/checker/property/relation/divisibility slice
  - 74 passed in 20.16 seconds, including 50,000-node recursion-free round trips
    and fresh-process verifier tests.
- Pass: scoped Ruff
  - all checks passed after mechanical import sorting and formatting.
- Pass: full configured Pyright
  - 0 errors, 0 warnings, 0 informations.
- Pass: ownership searches
  - old public serializer names have zero Python hits; Hamblin imports occur only
    in `codec.py` and its direct adversarial test; trusted core modules do not
    import the codec.

Commit:

- `2ea3473 refactor: centralize untrusted wire codec`

Next slice:

- Iteration 5 - theory-owned proof libraries

### Iteration 5 - Theory-Owned Proof Libraries - Complete

Surfaces:

- generic `cold_start/proofs.py` theorem bucket
  - Disposition: delete/split
  - Owners after cleanup: Presburger builders in `presburger_proofs.py`, Peano
    builders in `peano_proofs.py`, and Robinson-specific builders consolidated in
    `robinson_proofs.py`.
- addition/induction/cancellation and zero-case lemmas
  - Disposition: move
  - Owner after cleanup: `presburger_proofs.py`, matching the smallest complete
    theory under which every recipe checks.
- multiplication laws, distributivity, associativity, and positive cancellation
  - Disposition: move
  - Owner after cleanup: `peano_proofs.py`, importing the proved Presburger kit
    it genuinely depends on.
- Robinson numeral addition recipe
  - Disposition: move/consolidate
  - Owner after cleanup: `robinson_proofs.py` beside the bridge-derived results.
- production, test, and Lean corpus imports
  - Disposition: rewrite directly
  - Action: each caller imports the theory owner that supplies the builder; no
    generic facade or aliases preserve `cold_start.proofs`.

Red evidence:

- Error: owner-focused test collection
  - `peano_proofs` and `presburger_proofs` did not exist, and
    `robinson_proofs` did not yet expose `robinson_add_proof`.
- Error: first post-split collection
  - Peano theorem constants referenced `_n` from the old shared module.
  - Resolution: the Peano owner defines its own private theorem variables.
- Fail: first broader gate
  - 1 failed, 322 passed because an architecture test still opened deleted
    `proofs.py` to prove its import scanner was non-vacuous.
  - Resolution: the scanner now proves both concrete theory libraries import the
    untrusted tactics while the trusted core does not.

Green evidence:

- Pass: primary Presburger/Peano/Robinson files
  - 321 passed in 5.92 seconds.
- Pass: complete planned theory/tactic/model/sort/Lean slice
  - 464 passed in 47.19 seconds, including generated-corpus foreign-kernel
    compilation.
- Pass: `uv run python -m cold_start.lean`
  - generated the canonical corpus with no checked-in file diff.
- Pass: full scoped Ruff and configured Pyright
  - Ruff all checks passed; Pyright 0 errors, 0 warnings, 0 informations.
- Pass: ownership searches
  - `cold_start/proofs.py` is absent and old generic imports have zero Python
    hits.

Commit:

- `0aae508 refactor: assign proof builders to theories`

Next slice:

- Iteration 6 - verifier CLI contract

### Iteration 6 - Verifier CLI Contract - Complete

Surfaces:

- manual index-based argument parsing
  - Disposition: delete/rewrite
  - Owner after cleanup: one `argparse.ArgumentParser` defines an optional proof
    path and named theory option, rejecting missing values and extra paths with
    standard exit code 2.
- repeated mutable theory loading
  - Disposition: delete/consolidate
  - Owner after cleanup: one immutable `MappingProxyType` mapping of the three
    supported theories.
- unscoped file reading and uncaught input errors
  - Disposition: rewrite
  - Owner after cleanup: `_read_input` uses a managed `Path.open` boundary or
    stdin and maps `OSError` to a stable diagnostic and exit code 2.
- checker rejection behavior
  - Disposition: keep
  - Action: malformed or invalid proof data remains `REJECTED` with exit code 1;
    verified sequents remain exit code 0.

Red evidence:

- Fail: initial verifier subprocess contract
  - 4 failed, 7 passed, 23 deselected.
  - Missing `--theory` raised `IndexError`; duplicate paths silently selected the
    last path; missing files and directory paths leaked uncaught I/O tracebacks.

Green evidence:

- Pass: all verifier/cross-process cases
  - 11 passed, 23 deselected in 1.31 seconds.
- Pass: complete checker test file
  - 34 passed in 1.31 seconds.
- Pass: scoped Ruff and configured Pyright
  - Ruff all checks passed; Pyright 0 errors, 0 warnings, 0 informations.
- Pass: old path search
  - no manual argument loop, mutable loader, or unscoped `open(path)` remains.

Commit:

- `170c11c refactor: make verifier CLI failures explicit`

Next slice:

- Iteration 7 - test runtime without coverage loss

### Iteration 7 - Test Runtime Without Coverage Loss - Complete

Surfaces:

- repeated construction of identical immutable Lean proof examples
  - Disposition: consolidate
  - Owner after cleanup: module constants are built once and reused by independent
    export assertions.
- repeated generated corpus construction
  - Disposition: consolidate
  - Owner after cleanup: one module-scoped `corpus_text` fixture supplies corpus
    content assertions and both foreign-kernel inputs; `write_corpus` still has
    its own independent write-contract test.
- repeated Lean toolchain discovery
  - Disposition: consolidate
  - Owner after cleanup: one module-scoped `lean4` fixture probes the toolchain
    once and supplies both the positive compile and corrupted-export rejection.
- model, sort, property, and foreign-kernel behavioral coverage
  - Disposition: keep
  - Action: Hypothesis counts, soundness checks, the positive Lean run, and the
    negative Lean run are unchanged.

Measured evidence:

- Before this slice: 1,263 passed in 117.14 seconds.
  - Slow Lean calls included corrupted export at 8.41 seconds, positive corpus
    compile at 5.63 seconds, corpus write at 2.26 seconds, and repeated corpus
    construction assertions around 1.04 seconds each.
- Focused Lean file after fixture sharing:
  - 43 passed in 10.08 seconds; both kernel calls remained and each took about
    3.6 seconds.
- After this slice: 1,263 passed in 98.48 seconds.
  - Improvement: 18.66 seconds (15.9 percent) against the same expanded suite.
  - This is also 4.91 seconds faster than the 103.39-second execution preflight,
    despite the suite growing from 1,242 to 1,263 tests.
- Pass: scoped Ruff and configured Pyright
  - Ruff all checks passed; Pyright 0 errors, 0 warnings, 0 informations.

Commit:

- pending Iteration 7 commit

Next slice:

- Iteration 8 - CI and typing truth
