# Certified Algebra Phase 2 Evidence

Date: 2026-08-08

Status: implemented; full repository gate green.

## Red contracts

`uv run pytest -q tests/test_ring_nf.py` failed during collection because neither
`cold_start.ring_nf` nor `cold_start.diffring2_proofs` existed.

The new contracts require checked proofs for basic F2 identities,
characteristic-2 duplicate cancellation, and distributivity; preserve `x*x` as
a genuine power distinct from `x`; reject unequal polynomials and unsupported
derivative/binder/relation inputs; and demonstrate that an F2 context cannot
smuggle `CHAR2` into Peano.

## Implementation

`ring_nf.py` is the one sparse polynomial owner. Its iterative tri-color term
fold reifies variables and declared nullary generators, computes a canonical
sorted monomial map, quotes one exact right-associated term, and emits an
ordinary equality proof at every addition or multiplication fold. The sparse IR
never reaches the checker or certificate boundary.

The coefficient domain in this vertical slice is exactly mod 2. Addition uses
coefficient parity; multiplication adds monomial exponents. In particular,
`x*x` quotes as exponent two and is not reduced to `x`. Unsupported functions,
relations, and binders fail at reification before a candidate proof is returned.

`diffring2_proofs.py` now owns the derived zero/identity/AC/cancellation facts,
derivation-at-zero/one theorems, and `DIFF_RING_2_CONTEXT`. Its private rewrite
recipes justify only sparse fold merge steps. Context recipes are not semantic
authority: the wrong-theory test builds an F2 proof recipe and confirms ordinary
`check(_, PEANO)` rejects its `CHAR2` axiom use.

`jacobian2_proofs.py` retains only the map, derivative statements, determinant,
collisions, non-injectivity statement, and uses of generic certified algebra.
Derivative axioms are first replayed until no `DX`/`DY`/`DZ` remains, then
`ring_eq` closes the polynomial equality. The determinant rewrites its nine
already-proved entries and delegates the remaining identity to `ring_eq`.
Collisions normalize directly through the same sparse owner.

The former public `normal_form_rules` schedule and the Jacobian-owned generic
ring helpers were deleted. Production searches have zero hits for the old
normalizer or imports of those helpers from `jacobian2_proofs`.

## Measurements

All Jacobian statements are unchanged. The exact independent F2 polynomial
model tests, ordinary checker tests, and fresh-process collision verification
remain green. Proof toll changed as follows:

| Group | Phase 1 | Phase 2 |
|---|---:|---:|
| collisions (9) | 1,261 | 2,522 |
| derivative lemmas (9) | 25,281 | 8,286 |
| det J = 1 | 47,147 | 12,019 |
| D(0) = 0 (3) | 45 | 45 |
| D(1) = 0 (3) | 69 | 69 |
| non-injectivity | 936 | 2,161 |
| total | 74,739 | 25,102 |

The small collision/non-injectivity proofs grow because each sparse fold carries
explicit canonical merge certificates. The dominant derivative and determinant
proofs shrink enough to reduce the total by 66.4%. The full Jacobian command
fell from 9.793 seconds after Phase 1 to 2.785 seconds after Phase 2 (84.9% below
the original 18.407-second Phase 0 baseline).

## Verification

Focused `test_ring_nf.py` and `test_jacobian2.py` pass. Focused Ruff is clean and
repository Pyright reports 0 errors, 0 warnings, and 0 informations.

```text
1424 passed in 510.29s (0:08:30)
Ruff: all checks passed
Pyright strict: 0 errors, 0 warnings, 0 informations
Lean coverage: 16 proof rules, 16 feature families, 15 official theories
Lean corpus freshness: clean
Lean 4 compilation: passed
trusted-base mutation: correctly skipped; Phase 2 is outside the trusted base
GATE GREEN
elapsed: 524.476 seconds
```

The unrelated package-smoke directory and all untracked notes remain excluded.
