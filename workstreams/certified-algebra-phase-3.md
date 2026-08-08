# Certified Algebra Phase 3 Evidence

Date: 2026-08-08

Status: implemented; full repository gate green.

## Red contracts

`uv run pytest -q tests/test_groebner2.py` initially failed during collection
because `cold_start.groebner2` did not exist. The new contracts require a
two-generator membership whose successful proof needs a nontrivial S-pair,
reject a corrupted all-zero cofactor vector before returning a proof, distinguish
a completed non-member from exhausted search, and reject Boolean idempotence as
a consequence of characteristic two alone.

## Implementation

`groebner2.py` implements deterministic bounded Buchberger search over sparse F2
polynomials. It fixes graded lexicographic order over the structural order of
the problem atoms, processes critical pairs deterministically, and carries every
basis element as a vector of polynomial cofactors over the original generators.
Reduction therefore returns either an explicit original-generator
representation, a completed nonzero remainder, or named budget exhaustion.

Step, degree, monomial-count, basis-size, and cofactor-size limits are exact
positive integers. `NotMember` and `SearchExhausted` contain no proof. A zero
remainder alone is also insufficient: only `MembershipWitness` carries the
cofactor vector needed for elaboration.

`ring_nf.elaborate_ideal_membership` quotes each nonzero cofactor, scales its
checked or assumed source equality with ordinary `Cong('*', ...)`, combines the
scaled equations with `Cong('+', ...)`, and uses the existing F2 normalizer for
the cross-sum and cancellation identities. The checker receives only existing
proof constructors. Searches of `checker.py` and `proof.py` have zero
CAS-specific rule or constructor hits.

The first proof is a small conditional two-generator example requiring a
nontrivial S-polynomial. Ordinary `check()` accepts its result under
`DIFF_RING_2` with exactly the two source equations as hypotheses. The second
application uses the actual Jacobian map: assuming its first component is one
and second component is zero at the generic point, ideal membership proves that
their sum is one. Its checked sequent contains exactly those two hypotheses.

## Measurements

`uv run python -m cold_start.jacobian2_proofs` reports:

```text
collisions (9)               toll     2,522
derivative lemmas (9)        toll     8,286
det J = 1                    toll    12,019
D(0) = 0 (3)                 toll        45
D(1) = 0 (3)                 toll        69
non-injectivity (closed)     toll     2,161
ideal consequence            toll    13,494
TOTAL                        toll    38,596
ideal search                 steps 279, degree 20, basis 10, cofactors 60,
                             construction 1.013890s
```

The construction time is an observed wall measurement rather than a
deterministic contract. Search steps, maximum degree, basis size, and cofactor
size are deterministic work measurements asserted through the result surface.

## Verification

Focused Gröbner and Jacobian tests pass (17 tests). Focused Ruff and strict
Pyright are clean. The complete gate from this worktree passed:

```text
1429 tests collected; pytest passed
Ruff: all checks passed
Pyright strict: 0 errors, 0 warnings, 0 informations
Lean corpus generation: passed
Lean corpus freshness: clean
Lean 4 compilation: passed
trusted-base mutation: skipped; Phase 3 is outside the trusted base
GATE GREEN
elapsed: 637.6727071 seconds
```

The unrelated package-smoke directory and all untracked notes remain excluded.
