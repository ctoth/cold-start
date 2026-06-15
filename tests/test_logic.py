"""Classical negation: Bottom, Not (= Implies(., Bottom)), ex falso, reductio.

Negation introduction is just ImpIntro (assume A, derive Bottom, discharge) and
negation elimination is just MP. The only new primitives are ex falso and the
classical reductio rule. Disequality finally lets Peano prove distinct numerals
unequal, instead of leaning on a model witness.
"""

from __future__ import annotations

from hypothesis import given, settings
from hypothesis import strategies as st
from semantics import evaluate
from test_model import N

import cold_start.proof as P
from cold_start.checker import check
from cold_start.peano import PEANO
from cold_start.presburger import SUCC_INJ, SUCC_NEQ_ZERO, ZERO, S, numeral
from cold_start.syntax import Bottom, Eq, Implies, Not, Var

ENV = st.fixed_dictionaries({n: st.integers(0, 8) for n in ["x", "y", "z", "n", "m"]})


# --- the two new primitive rules ------------------------------------------


def test_ex_falso_derives_anything():
    # |- Bottom -> (0 = 1):  assume Bottom, conclude anything, discharge.
    target = Eq(ZERO, S(ZERO))
    pf = P.ImpIntro(Bottom(), P.ExFalso(P.Assume(Bottom()), target))
    seq = check(pf, PEANO)
    assert seq.concl == Implies(Bottom(), target)
    assert seq.hyps == frozenset()


def test_reductio_proves_double_negation_elimination():
    # |- ~~A -> A, the classical hallmark, via reductio.
    a = Eq(Var("x"), Var("x"))
    nnA = Not(Not(a))  # (A -> Bottom) -> Bottom
    contradiction = P.MP(P.Assume(nnA), P.Assume(Not(a)))  # {~~A, ~A} |- Bottom
    pf = P.ImpIntro(nnA, P.RAA(a, contradiction))  # discharge ~A via reductio, then ~~A
    seq = check(pf, PEANO)
    assert seq.concl == Implies(nnA, a)
    assert seq.hyps == frozenset()


def test_reductio_needs_a_proof_of_bottom():
    # RAA whose sub-proof concludes something other than Bottom must be rejected.
    bad = P.RAA(Eq(ZERO, ZERO), P.Refl(ZERO))  # Refl concludes 0=0, not Bottom
    try:
        check(bad, PEANO)
    except ValueError:
        return
    raise AssertionError("reductio accepted a sub-proof that was not Bottom")


# --- Peano disequality ----------------------------------------------------


def test_one_is_not_zero():
    # 1 != 0 is just the disequality axiom instantiated at x := 0.
    seq = check(P.Inst(P.Axiom(SUCC_NEQ_ZERO), "x", ZERO), PEANO)
    assert seq.concl == Not(Eq(numeral(1), ZERO))
    assert seq.hyps == frozenset()


def test_two_is_not_one():
    # 2 != 1, by injectivity + (1 != 0): assume 2=1, get 1=0 by injectivity,
    # contradict S0 != 0, discharge.
    eq21 = Eq(numeral(2), numeral(1))  # S1 = S0
    inj = P.Inst(P.Inst(P.Axiom(SUCC_INJ), "x", numeral(1)), "y", ZERO)  # S1=S0 -> 1=0
    one_ne_zero = P.Inst(P.Axiom(SUCC_NEQ_ZERO), "x", ZERO)  # S0=0 -> Bottom
    one_eq_zero = P.MP(inj, P.Assume(eq21))  # {2=1} |- 1=0
    boom = P.MP(one_ne_zero, one_eq_zero)  # {2=1} |- Bottom
    seq = check(P.ImpIntro(eq21, boom), PEANO)  # |- 2 != 1
    assert seq.concl == Not(eq21)
    assert seq.hyps == frozenset()


# --- negation stays sound in the standard model ---------------------------


@given(ENV)
@settings(max_examples=200)
def test_negation_axioms_true_in_N(env):
    assert evaluate(SUCC_NEQ_ZERO, N, env)  # x+1 != 0 for all x in N
    assert evaluate(SUCC_INJ, N, env)  # x+1 = y+1 -> x = y


def test_proved_disequalities_hold_in_N():
    for pf, claim in (
        (P.Inst(P.Axiom(SUCC_NEQ_ZERO), "x", ZERO), Not(Eq(numeral(1), ZERO))),
        (P.Inst(P.Axiom(SUCC_NEQ_ZERO), "x", numeral(1)), Not(Eq(numeral(2), ZERO))),
    ):
        seq = check(pf, PEANO)
        assert seq.concl == claim
        assert evaluate(seq.concl, N, {})  # the disequality is true in N
