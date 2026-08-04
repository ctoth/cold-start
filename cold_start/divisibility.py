"""Divisibility foundations proved in PEANO.

The atomic ``|`` relation is the vocabulary of Robinson's Theorem 1.2.  Here we
give its ordinary multiplication interpretation, ``a | b := exists k, a*k=b``,
and derive the first reusable laws as proof terms.  This module is untrusted:
the returned recipes become theorems only when ``checker.check`` accepts them in
PEANO.
"""

from __future__ import annotations

from .peano import mul
from .presburger import ZERO, S
from .proof import Assume, Cong, ExistsElim, ExistsIntro, ImpIntro, Pf, Refl, Sym, Trans
from .proofs import (
    ADD_RULES,
    LEFT_IDENTITY,
    MUL_ASSOC,
    MUL_COMM,
    MUL_RULES,
    left_identity,
    mul_assoc,
    mul_comm,
)
from .syntax import Eq, Formula, Implies, Term, Var, exists, instantiate
from .tactics import lemma_rule, prove_eq

ONE = S(ZERO)


def _fresh(stem: str, *terms: Term) -> str:
    used = set().union(*(term.free_vars() for term in terms))
    if stem not in used:
        return stem
    index = 0
    while f"{stem}{index}" in used:
        index += 1
    return f"{stem}{index}"


def peano_divides(a: Term, b: Term) -> Formula:
    """``a | b`` interpreted in PEANO as ``exists k, a*k=b``."""
    witness_name = _fresh("k", a, b)
    witness = Var(witness_name)
    return exists(witness_name, "", Eq(mul(a, witness), b))


_a, _b, _c = Var("a"), Var("b"), Var("c")

DIVIDES_REFL: Formula = peano_divides(_a, _a)
DIVIDES_FACTOR: Formula = peano_divides(_a, mul(_a, _b))
DIVIDES_ZERO: Formula = peano_divides(_a, ZERO)
ONE_DIVIDES: Formula = peano_divides(ONE, _a)
DIVIDES_TRANS: Formula = Implies(
    peano_divides(_a, _b),
    Implies(peano_divides(_b, _c), peano_divides(_a, _c)),
)


def _mul_one(term: Term) -> Pf:
    return prove_eq(
        Eq(mul(term, ONE), term),
        (*ADD_RULES, *MUL_RULES, lemma_rule(LEFT_IDENTITY, left_identity())),
    )


def divides_refl() -> Pf:
    """PEANO proves ``a | a``; the witness is 1."""
    return ExistsIntro(DIVIDES_REFL, ONE, _mul_one(_a))


def divides_factor() -> Pf:
    """PEANO proves ``a | a*b``; the witness is ``b``."""
    return ExistsIntro(DIVIDES_FACTOR, _b, Refl(mul(_a, _b)))


def divides_zero() -> Pf:
    """PEANO proves ``a | 0``; the witness is 0."""
    zero_product = prove_eq(Eq(mul(_a, ZERO), ZERO), MUL_RULES)
    return ExistsIntro(DIVIDES_ZERO, ZERO, zero_product)


def one_divides() -> Pf:
    """PEANO proves ``1 | a``; the witness is ``a``."""
    one_times_a = Trans(
        lemma_rule(MUL_COMM, mul_comm()).instance({"x": ONE, "y": _a}),
        _mul_one(_a),
    )
    return ExistsIntro(ONE_DIVIDES, _a, one_times_a)


def divides_trans() -> Pf:
    """PEANO proves transitivity of divisibility.

    From witnesses ``a*k=b`` and ``b*l=c``, associativity certifies
    ``a*(k*l)=(a*k)*l=b*l=c``; ``k*l`` is the composite witness.
    """
    ab, bc, ac = peano_divides(_a, _b), peano_divides(_b, _c), peano_divides(_a, _c)
    k, ell = Var("k!"), Var("l!")
    ab_instance = instantiate(ab, k)
    bc_instance = instantiate(bc, ell)

    assoc = lemma_rule(MUL_ASSOC, mul_assoc()).instance({"x": _a, "y": k, "z": ell})
    multiply_ab = Cong("*", (Assume(ab_instance), Refl(ell)))
    product_eq_c = Trans(Sym(assoc), Trans(multiply_ab, Assume(bc_instance)))
    packed = ExistsIntro(ac, mul(k, ell), product_eq_c)

    use_bc = ExistsElim("l!", Assume(bc), packed)
    use_ab = ExistsElim("k!", Assume(ab), use_bc)
    return ImpIntro(ab, ImpIntro(bc, use_ab))


__all__ = [
    "DIVIDES_FACTOR",
    "DIVIDES_REFL",
    "DIVIDES_TRANS",
    "DIVIDES_ZERO",
    "ONE_DIVIDES",
    "divides_factor",
    "divides_refl",
    "divides_trans",
    "divides_zero",
    "one_divides",
    "peano_divides",
]
