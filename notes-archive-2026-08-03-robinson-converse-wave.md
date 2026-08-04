# Archived campaign checkpoint — Robinson converse wave (completed 2026-08-03)

Preserved verbatim from `notes-breakthrough.md` before the next wave reused the
live checkpoint file. All findings below are also recorded permanently in the
commit range `91a21a2..994c9b9` and the docs they updated.

---

# Active mathematics breakthrough campaign

## Current findings

- The strongest concrete target is the open Robinson converse already named in
  `ARCHITECTURE.md` and the Robinson paper notes:
  `bridge(a,b,S(c)) -> a+b=S(c)`.
- Normalizing a bridge hypothesis with `poly_kit()` produces exactly
  `S(ac + (bc + abc^2)) = S(c^2 + abc^2)`.
- Therefore successor injectivity and additive cancellation reduce it to
  `(a+b)c=c^2`; cancellation by the positive factor `S(c)` then finishes.
- Positive multiplication cancellation is derivable without a new axiom.  Use
  an outer induction on `x` over the explicitly quantified predicate
  `forall y, x*S(z)=y*S(z) -> x=y`, and a nested induction on `y`.  Explicit
  `Forall` is essential because a free `y` in the induction hypothesis cannot
  be instantiated while it remains a hypothesis.

## State

- Commit `91a21a2` adds `tactics.normalize_equality`, which transports a proved
  equality to the equality of its normal forms while leaving authority with the
  checker.  Focused tactic tests, Ruff, and Pyright passed.
- Red tests for left and right additive cancellation have been added to
  `tests/test_presburger.py`; production theorem builders are next.
- Commit `e94364a` derives both left and right additive cancellation in
  Presburger.
- Commit `1d7132c` derives
  `x*S(z)=y*S(z) -> x=y` in Peano using the planned explicit-`Forall`, nested
  induction proof.  The checker reports the theorem with no hypotheses.
- Commit `9e10a34` derives two new Peano theorems:
  `bridge(a,b,c) -> (a+b)c=c^2` and
  `bridge(a,b,S(c)) -> a+b=S(c)`.  The focused Robinson suite passes all 282
  cases, and Ruff/Pyright are clean.
- A PowerShell gate using only `$ErrorActionPreference='Stop'` continued after
  Ruff returned nonzero.  The commit was immediately amended after Ruff fixed
  the unused/unsorted import.  Future compound gates must explicitly test
  `$LASTEXITCODE` after every native command.
- Commit `67a8c66` packages the other graph direction and derives A5' under the
  exact positivity guard. Commit `945000d` adds the positive cancellation and
  converse terms to the generated Lean corpus; Lean 4.32.2 accepts it, while
  the deliberate corrupted-export control is rejected.
- Full current gate: 1164 tests collected and passed, Ruff clean, Pyright 0
  errors and 0 warnings. Documentation is being aligned before its commit.
- This note is a required live checkpoint and must remain uncommitted.

## Blockers

- None.  The remaining risk is proof-term shape/eigenvariable correctness in
  the nested induction; the checker will adjudicate it.

## Next action

1. Finish and commit the architecture, README, paper-note, and current-state
   updates without staging this live checkpoint note.
2. Audit the resulting commit range and rerun the full gate if documentation
   edits touched executable examples.
3. Choose the next high-leverage mathematical target; likely formal ordering
   and divisibility as prerequisites for Robinson's Theorem 1.2 over `(S, |)`.
