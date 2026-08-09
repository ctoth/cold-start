# Certified Algebra Phase 6 Evidence

Date: 2026-08-08

Status: implemented; focused verification and the mutation-free full repository
gate are green.

## Red contracts

Natural-semiring, signed-ring, and coefficient-policy separation contracts were
added to `tests/test_ring_nf.py` before implementation. The first focused run
failed during collection because the independent `algebra_proofs` owner and its
commutative-ring context did not exist.

The contracts require a natural-coefficient PEANO binomial identity, an
integer-coefficient signed multiplication identity under `COMM_RING`, and
structural rejection of an F2 policy carrying the natural cancellation recipe.
The combination suite also covers natural scaled/unscaled hypotheses, loud
failure for a bad orientation, and signed conditional cancellation.

## One polynomial owner

`ring_nf.AlgebraContext` now carries closed zero and one `Term` values rather
than assuming both are nullary symbols. Its coefficient domain is the exhaustive
`natural | integer | mod2` union. Integer contexts require explicit negation;
natural contexts may supply successor expansion; natural and integer contexts
require a proved right-cancellation recipe; and an F2 context rejects that
natural cancellation hook.

Sparse addition, multiplication, negation, coefficient canonicalization, and
quotation are domain-aware. Natural coefficients quote repeated monomials,
integer coefficients quote negative monomials with the context's negation, and
mod-2 coefficients alone reduce parity. PEANO's one is represented honestly as
`S(0)`, with nonconstant `S(x)` expanded as `x + 1`. F2 retains genuine powers
and the ideal-membership elaborator now rejects every non-mod-2 context.

`algebra_proofs.COMM_RING_CONTEXT` derives signed merge and cancellation recipes
from ordinary commutative-ring axioms. `peano_proofs.PEANO_SEMIRING_CONTEXT`
packages the already-proved PEANO semiring recipes. Both remain untrusted proof
producers: every result is accepted only when the ordinary checker re-derives it
under the caller's theory.

## Combination consolidation and deletion

`ring_nf.elaborate_combination` owns the checked scaled-sum, sparse cross-sum,
and right-cancellation path. `integer_pairs.py`, `ring_z.py`, and their tests now
consume it directly through the exact `CombinationSource` type.

Primitive squaring remains deliberately outside the polynomial atom language.
Its two recurrence proofs use `ring_nf.elaborate_rewrite_combination`, the narrow
rewrite-backed form of the same scaled-sum/cancellation operation, with square
recursion rules supplied explicitly. No `sq(...)` or derivative
application became an opaque polynomial atom.

`cold_start/combination.py` is deleted. Current source and current-facing
documentation have zero hits for `by_combination`, `ring_kit`, or imports of the
deleted module. The Phase 0 evidence retains those names only as a historical
inventory of the pre-program repository.

## Interpretation parity and tolls

Both interpretations reverify every obligation with unchanged bridge sizes and
empty open sets:

```text
integers-into-presburger-pairs: bridge 28; toll 148,761; open ()
ring-of-integers-into-peano: bridge 51; toll 1,331,516; open ()
```

The integer toll fell from the documented 155,545. The ring toll rose from
876,035 because the sparse fold emits explicit proofs for each recursive
normalization and merge instead of reusing one global rewrite normalization per
side. These are proof-representation costs; obligations, checked conclusions,
and completeness are unchanged.

## Verification

Focused verification is green:

```text
39 tests passed across ring normalization, combinations, integer pairs,
ring-of-integers payments, and squaring payments
Ruff: all checks passed
Pyright strict: 0 errors, 0 warnings, 0 informations
```

Routine `tools/gate.ps1` remains mutation-free. Phase 6 changes only untrusted
proof-production modules, outside the separately declared logical-kernel and
portable-verifier mutation source boundaries; those explicit CI campaigns remain
unchanged.

The final repository gate passed:

```text
1,496 tests passed in 56.18 seconds
Ruff: all checks passed
Pyright strict: 0 errors, 0 warnings, 0 informations
Lean coverage: 16 proof rules, 16 feature families, 15 official theories
generated Lean corpus freshness: clean
Lean 4 compilation: passed
GATE GREEN
elapsed: 71.4619300 seconds
```
