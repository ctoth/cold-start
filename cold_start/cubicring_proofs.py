"""The norm factorization d * e = N in Z[theta | theta^3 = 2], checked.

The identity is not a plain polynomial identity — it needs the cube
relation — and its whole point is conjugate cancellation, so the raw form
`d * e = N` cannot pass through the sparse normalizer's merge recipes
(expanding d * e makes the theta^2 coefficient vanish identically, a
cancellation the ordered rule kit cannot justify). Both obstacles dissolve
in the subtraction-free arrangement

    d*e+ + N-  =  N+ + d*e-        (statement; e = e+ - e-, N = N+ - N-)

proved by `elaborate_combination` from two positively-scaled uses of the
cube axiom:

    (theta^3 = 2) * g+   and   (2 = theta^3) * g-,

whose shuffled goal is an identity with only natural coefficients on both
sides — every normalizer merge is cancellation-free — while the one real
cancellation happens in the trusted right-cancellation implication. The
model tests in `tests/test_cubicring.py` pin that the arrangement denotes
exactly d * e = N for the paper's polynomials.
"""

from __future__ import annotations

from dataclasses import replace

from .algebra_proofs import COMM_RING_CONTEXT
from .checker import check
from .cubicring import (
    CUBE,
    CUBIC_RING,
    GEN_K,
    GEN_M,
    GEN_N,
    GEN_TH,
    TWO,
    cofactor_minus_term,
    cofactor_plus_term,
    element_term,
    norm_minus_term,
    norm_plus_term,
    residue_minus_term,
    residue_plus_term,
)
from .proof import Pf, Sym, proof_size
from .ring_nf import elaborate_combination
from .syntax import Eq, Formula
from .tactics import axiom_rule
from .vocabulary import add, mul

CUBIC_RING_CONTEXT = replace(
    COMM_RING_CONTEXT,
    atoms=frozenset({GEN_TH, GEN_K, GEN_M, GEN_N}),
)


def factorization_statement() -> Formula:
    """d*e+ + N- = N+ + d*e-: the norm factorization, subtraction-free."""
    d = element_term()
    return Eq(
        add(mul(d, cofactor_plus_term()), norm_minus_term()),
        add(norm_plus_term(), mul(d, cofactor_minus_term())),
    )


def factorization_proof() -> Pf:
    cube_pf = axiom_rule(CUBE).instance({})
    cube_flipped = Eq(TWO, mul(GEN_TH, mul(GEN_TH, GEN_TH)))
    sources = (
        (CUBE, cube_pf, residue_plus_term()),
        (cube_flipped, Sym(cube_pf), residue_minus_term()),
    )
    return elaborate_combination(
        factorization_statement(), sources, CUBIC_RING_CONTEXT
    )


def main() -> None:
    proof = factorization_proof()
    sequent = check(proof, CUBIC_RING)
    print(f"norm factorization (subtraction-free): {proof_size(proof):,} proof nodes")
    print(f"checked: {sequent!r}")


if __name__ == "__main__":
    main()


__all__ = [
    "factorization_proof",
    "factorization_statement",
]
