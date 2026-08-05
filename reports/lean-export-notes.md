# Lean export reproducibility report

## Current owners

The Lean adapter is deliberately split by responsibility:

- `cold_start/lean/syntax.py` owns Lean names, substitution, statement rendering,
  parsing, and universal closure.
- `cold_start/lean/proof.py` owns checked proof-term rendering.
- `cold_start/lean/models.py` owns exact-theory semantic model registrations,
  including operation interpretations, axiom payments, and induction.
- `cold_start/lean/corpus.py` owns corpus entries, generated headers, registry
  lookup, and `lean_export/ColdStart.lean`.
- `cold_start/lean/__main__.py` owns `python -m cold_start.lean`.

There is no `cold_start/lean.py` compatibility module and no package initializer
that re-exports the deleted combined surface.

## Soundness contract

Every emitted theorem is conditional. Object-language function symbols, theory
axioms, and (when used) induction are Lean theorem parameters; the exporter never
creates a Lean `axiom`, `sorry`, or tactic escape. The Presburger and Peano
epilogue looks up the theorem's exact `Theory` object in the fail-closed model
registry. PRESBURGER and PEANO instantiate at Lean's `Nat` using core lemmas;
an equal but unregistered theory does not inherit that authority. Robinson
remains conditional because its positive-integer axiom
`succ a != 1` is false in `Nat` at `a = 0`.

Proof instantiation is rendered through a substitution environment, so axiom
arguments follow the statement closure order independently of the nesting order of
`Inst` nodes. Congruence, implication, quantifiers, classical rules, and induction
map to explicit Lean proof terms.

## Reproduce

The repository pins Lean in `lean-toolchain`. Regenerate and compare the corpus:

```powershell
uv run python -m cold_start.lean
git diff --exit-code -- lean_export/ColdStart.lean
```

Compile it with the selected Lean 4 toolchain:

```powershell
lean lean_export/ColdStart.lean
```

The repository gate runs all Python tests, Ruff, and Pyright basic:

```powershell
pwsh -File tools/gate.ps1
```

CI performs the same lockfile-backed gate, regenerates and diffs the corpus, and
compiles it with the pinned Lean release.

## Failure shields

`tests/test_lean.py` keeps both required foreign-kernel executions:

1. the complete generated corpus must compile;
2. a deliberately corrupted induction base must be rejected.

The same file checks byte-for-byte corpus freshness, absence of asserted axioms and
placeholders, statement round-trips, exact theorem parameters, Nat instantiation,
and conditional Robinson export. Immutable proof/corpus setup is shared across
assertions, but neither kernel execution is skipped or replaced by string checks.

## Verified execution

On 2026-08-05, after the exact semantic-model registry landed:

- the full owned gate passed 1,330 tests with zero skips;
- Ruff passed;
- Pyright basic reported 0 errors and 0 warnings;
- corpus regeneration matched the committed generated form;
- the generated corpus compiled and the corrupted negative control was rejected;
- focused model tests proved that structurally equal and unregistered theories
  do not inherit `Nat` cash-out.

On 2026-08-04, after the repository architecture cleanup:

- the full owned gate passed 1,266 tests in 97.27 seconds with zero skips;
- Ruff passed;
- Pyright basic reported 0 errors and 0 warnings;
- corpus regeneration produced no Git diff;
- Lean 4.32.2 compiled `lean_export/ColdStart.lean` with exit code 0.

Historical development chronology remains available in Git history; this report owns
only the current reproducibility contract and evidence.
