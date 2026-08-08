# Certified Algebra Phase 1 Evidence

Date: 2026-08-08

Status: implemented and verified.

## Red contracts

The focused pre-implementation run failed five targeted contracts:

```text
cycle: exact canonical graph timed out after 3 seconds
sharing: shared Refl validated 4 times and derived 2 times
Lean coverage: shared proof identity visited 2 times
Lean model discovery: shared syntax identity visited 4 times
Lean emission: LeanLimits and LeanLimitError absent
```

The companion sharing-equivalence contract already passed: identity sharing did
not change a valid sequent or the rejection of mismatched transitivity premises.
The existing checker inventory test continued to prove exact independent
handling of all sixteen canonical proof types.

## Implementation

`checker.py` now owns one iterative tri-color traversal. Exact local validation
happens when an identity changes from unseen to active. An edge to active raises
a cycle error; an edge to complete is sharing and is not expanded. The resulting
unique postorder is passed directly to derivation, which constructs one sequent
per proof identity. Validation and derivation therefore cannot disagree about
the graph shape.

The checker documents the admission invariant that every rule derives only from
its immutable fields, already-derived child sequents, and the selected theory.
No proof constructor, logical rule, or accepted sequent changed.

Lean symbol, name, feature, coverage, and model inspection now visits each object
identity once, including cyclic hostile graphs. Tree-shaped proof presentation
is intentionally unchanged. `LeanLimits` bounds both Visit expansions and UTF-8
output bytes; limit failure raises before returning any partial theorem text.
The generic iterative emitter owns the counting mechanism, while the Lean
adapter owns its default policy and diagnostic type.

## Measurements

The Jacobian proof suite retained exactly the same statement/toll report:

```text
collisions (9)               toll     1,261
derivative lemmas (9)        toll    25,281
det J = 1                    toll    47,147
D(0) = 0 (3)                 toll        45
D(1) = 0 (3)                 toll        69
non-injectivity (closed)     toll       936
TOTAL                        toll    74,739
```

Its end-to-end command time fell from the Phase 0 baseline of 18.407 seconds to
9.793 seconds. The determinant graph itself remains 47,147 tree occurrences and
13,682 unique proof objects; Phase 1 changes trusted traversal work, not proof
construction or external bytes.

## Verification

The targeted red contracts all turned green. The broader checker,
kernel-boundary, quantifier, quantifier-soundness, sort, property, Lean, and Lean
model suites passed. Focused Ruff and repository Pyright reported no findings.

The forced full gate completed in 1,055.392 seconds:

```text
1420 passed in 521.56s (0:08:41)
Ruff: all checks passed
Pyright strict: 0 errors, 0 warnings, 0 informations
Lean coverage: 16 proof rules, 16 feature families, 15 official theories
Lean corpus freshness: clean
Lean 4 compilation: passed
GATE GREEN
```

The forced trusted-base campaign was then run from the committed Phase 1 tree,
so its disposable worktrees contained the new graph traversal:

```text
checker.py: 77/77 killed, 0 survived
proof.py: 0 mutation sites
sequent.py: 3/3 killed, 0 survived
syntax.py: 56/56 killed, 0 survived
theory.py: 44/44 killed, 0 survived
total: 180/180 killed, 0 survived
elapsed: 480.816 seconds
```

Existing unrelated modifications to `cold_start/verify.py`, new groupring files,
the package-smoke directory, and all untracked notes were excluded from the
Phase 1 commit.
