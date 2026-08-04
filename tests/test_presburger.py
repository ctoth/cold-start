"""Presburger vs Peano, as a theory extension.

The addition-only fragment -- 0, S, +, with induction -- is **Presburger
arithmetic**: complete and decidable, Goedel does not bite. Add multiplication
(the two recursion axioms x*0 = 0 and x*S(y) = x*y + x) and you get real Peano,
where incompleteness begins. We model that exactly: PEANO is PRESBURGER plus the
two multiplication axioms, nothing else changed.
"""

from __future__ import annotations

import pytest

import cold_start.proof as P
from cold_start.checker import check
from cold_start.peano import MUL_SUCC_F, MUL_ZERO_F, PEANO, mul
from cold_start.peano_proofs import mul_proof
from cold_start.presburger import PRESBURGER, ZERO, S, add, numeral
from cold_start.presburger_proofs import (
    ADD_CANCEL_LEFT,
    ADD_CANCEL_RIGHT,
    ADD_EQ_ZERO,
    ZERO_OR_SUCC,
    add_cancel_left,
    add_cancel_right,
    add_eq_zero,
    left_identity_proof,
    zero_or_succ,
)
from cold_start.prop import And, Or
from cold_start.syntax import Eq, Implies, Var, exists


def test_peano_is_presburger_plus_multiplication():
    assert PRESBURGER.axioms < PEANO.axioms  # strict superset
    assert PEANO.axioms - PRESBURGER.axioms == frozenset({MUL_ZERO_F, MUL_SUCC_F})
    # the induction structure (zero/successor) is inherited unchanged
    assert PEANO.zero == PRESBURGER.zero
    assert PEANO.succ == PRESBURGER.succ


def test_presburger_proves_left_identity():
    # 0 + n = n by induction -- a theorem of the addition fragment alone.
    seq = check(left_identity_proof(), PRESBURGER)
    n = Var("n")
    assert seq.concl == Eq(add(ZERO, n), n)
    assert seq.hyps == frozenset()


@pytest.mark.parametrize(
    ("claim", "build"),
    [
        (ADD_CANCEL_RIGHT, add_cancel_right),
        (ADD_CANCEL_LEFT, add_cancel_left),
    ],
    ids=["right", "left"],
)
def test_presburger_proves_additive_cancellation(claim, build):
    seq = check(build(), PRESBURGER)

    assert seq.concl == claim
    assert seq.hyps == frozenset()
    assert type(claim) is Implies


def test_presburger_proves_a_zero_sum_has_zero_summands():
    seq = check(add_eq_zero(), PRESBURGER)
    x, y = Var("x"), Var("y")

    assert seq.hyps == frozenset()
    assert seq.concl == ADD_EQ_ZERO
    assert ADD_EQ_ZERO == Implies(
        Eq(add(x, y), ZERO),
        And(Eq(x, ZERO), Eq(y, ZERO)),
    )


def test_presburger_proves_every_number_is_zero_or_a_successor():
    seq = check(zero_or_succ(), PRESBURGER)
    n = Var("n")

    assert seq.hyps == frozenset()
    assert seq.concl == ZERO_OR_SUCC
    assert ZERO_OR_SUCC == Or(
        Eq(n, ZERO),
        exists("m", "", Eq(n, S(Var("m")))),
    )


def test_peano_proves_a_multiplication_axiom_instance():
    # 2 * 0 = 0, one instance of the multiplication base axiom.
    pf = P.Inst(P.Axiom(MUL_ZERO_F), "x", numeral(2))
    assert check(pf, PEANO).concl == Eq(mul(numeral(2), ZERO), ZERO)


def test_presburger_cannot_multiply():
    # The same proof is rejected by Presburger: it has no multiplication axiom.
    pf = P.Inst(P.Axiom(MUL_ZERO_F), "x", numeral(2))
    with pytest.raises(ValueError):
        check(pf, PRESBURGER)


@pytest.mark.parametrize(("a", "b"), [(0, 0), (2, 3), (4, 1), (1, 5), (3, 3)])
def test_peano_multiplication_computes(a, b):
    # A genuine worked computation, not just an axiom citation.
    seq = check(mul_proof(a, b), PEANO)
    assert seq.concl == Eq(mul(numeral(a), numeral(b)), numeral(a * b))
    assert seq.hyps == frozenset()
