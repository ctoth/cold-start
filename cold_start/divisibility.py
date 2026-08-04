"""Divisibility foundations proved in PEANO.

The atomic ``|`` relation is the vocabulary of Robinson's Theorem 1.2.  Here we
give its ordinary multiplication interpretation, ``a | b := exists k, a*k=b``,
and derive the first reusable laws as proof terms.  This module is untrusted:
the returned recipes become theorems only when ``checker.check`` accepts them in
PEANO.
"""

from __future__ import annotations

from .peano import mul
from .presburger import ZERO, S, add
from .proof import MP, Assume, Cong, ExistsElim, ExistsIntro, ImpIntro, Inst, Pf, Refl, Sym, Trans
from .proofs import (
    ADD_RULES,
    DISTRIB_LEFT,
    LEFT_IDENTITY,
    MUL_ASSOC,
    MUL_COMM,
    MUL_RULES,
    distrib_left,
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
DIVIDES_PRODUCT_RIGHT: Formula = peano_divides(_b, mul(_a, _b))
DIVIDES_ZERO: Formula = peano_divides(_a, ZERO)
ONE_DIVIDES: Formula = peano_divides(ONE, _a)
DIVIDES_TRANS: Formula = Implies(
    peano_divides(_a, _b),
    Implies(peano_divides(_b, _c), peano_divides(_a, _c)),
)
DIVIDES_PRODUCT: Formula = Implies(
    peano_divides(_a, _b),
    peano_divides(_a, mul(_b, _c)),
)
DIVIDES_ADD: Formula = Implies(
    peano_divides(_a, _b),
    Implies(peano_divides(_a, _c), peano_divides(_a, add(_b, _c))),
)
DIVIDES_MUL_LEFT: Formula = Implies(
    peano_divides(_a, _b),
    peano_divides(mul(_c, _a), mul(_c, _b)),
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


def divides_product_right() -> Pf:
    """PEANO proves ``b | a*b`` by commuting the product; witness ``a``."""
    commute = lemma_rule(MUL_COMM, mul_comm()).instance({"x": _b, "y": _a})
    return ExistsIntro(DIVIDES_PRODUCT_RIGHT, _a, commute)


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


def divides_product() -> Pf:
    """PEANO proves ``a|b -> a|b*c`` by transitivity through ``b|b*c``."""
    ab = peano_divides(_a, _b)
    transitive = Inst(
        Inst(Inst(divides_trans(), "a", _a), "b", _b),
        "c",
        mul(_b, _c),
    )
    # Substitute the original ``b`` first: replacing ``a`` by the term named
    # ``b`` and then substituting ``b`` would also rewrite that replacement.
    factor = Inst(Inst(divides_factor(), "b", _c), "a", _b)
    return ImpIntro(ab, MP(MP(transitive, Assume(ab)), factor))


def divides_add() -> Pf:
    """PEANO proves ``a|b -> a|c -> a|(b+c)``.

    From witnesses ``a*k=b`` and ``a*l=c``, distributivity certifies
    ``a*(k+l) = a*k + a*l = b + c``; ``k+l`` is the composite witness.
    """
    ab, ac = peano_divides(_a, _b), peano_divides(_a, _c)
    goal = peano_divides(_a, add(_b, _c))
    k, ell = Var("k!"), Var("l!")
    ab_instance = instantiate(ab, k)
    ac_instance = instantiate(ac, ell)

    distribute = lemma_rule(DISTRIB_LEFT, distrib_left()).instance({"x": _a, "y": k, "z": ell})
    sum_of_witnesses = Cong("+", (Assume(ab_instance), Assume(ac_instance)))
    product_eq_sum = Trans(distribute, sum_of_witnesses)
    packed = ExistsIntro(goal, add(k, ell), product_eq_sum)

    use_ac = ExistsElim("l!", Assume(ac), packed)
    use_ab = ExistsElim("k!", Assume(ab), use_ac)
    return ImpIntro(ab, ImpIntro(ac, use_ab))


def divides_mul_left() -> Pf:
    """PEANO proves ``a|b -> c*a|c*b``: a common left factor is harmless.

    From the witness ``a*k=b``, associativity certifies
    ``(c*a)*k = c*(a*k) = c*b``; the witness survives unchanged.
    """
    ab = peano_divides(_a, _b)
    goal = peano_divides(mul(_c, _a), mul(_c, _b))
    k = Var("k!")
    ab_instance = instantiate(ab, k)

    assoc = lemma_rule(MUL_ASSOC, mul_assoc()).instance({"x": _c, "y": _a, "z": k})
    scale = Cong("*", (Refl(_c), Assume(ab_instance)))
    packed = ExistsIntro(goal, k, Trans(assoc, scale))

    return ImpIntro(ab, ExistsElim("k!", Assume(ab), packed))


__all__ = [
    "DIVIDES_ADD",
    "DIVIDES_FACTOR",
    "DIVIDES_MUL_LEFT",
    "DIVIDES_PRODUCT",
    "DIVIDES_PRODUCT_RIGHT",
    "DIVIDES_REFL",
    "DIVIDES_TRANS",
    "DIVIDES_ZERO",
    "ONE_DIVIDES",
    "divides_add",
    "divides_factor",
    "divides_mul_left",
    "divides_product",
    "divides_product_right",
    "divides_refl",
    "divides_trans",
    "divides_zero",
    "one_divides",
    "peano_divides",
]
