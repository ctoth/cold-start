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
from cold_start.presburger import PRESBURGER, ZERO, add, numeral
from cold_start.proofs import left_identity_proof, mul_proof
from cold_start.syntax import Eq, Var


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
