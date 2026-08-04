"""The order kit: <= as a witnessed sum, transport, and strong induction.

`le(a, b) := exists w, a + w = b` plus the lemmas that make it usable
(reflexivity, the zero case, the successor split, doubling bounds), the
`transport` tactic that rewrites a whole FORMULA along a proved equality,
and `course_of_values` -- strong induction compiled down to the structural
`Induct` rule through the reach predicate `forall z (z <= n -> P(z))`.

This is the frontier kit: the Skolem bridge's product closure and the
formula (2) bounding argument both wait on exactly these pieces."""

from __future__ import annotations

from cold_start.checker import check
from cold_start.divisibility import peano_divides
from cold_start.order import (
    LE_DOUBLE,
    LE_SUCC_SPLIT,
    LE_ZERO,
    course_of_values,
    le,
    le_double,
    le_refl,
    le_succ_split,
    le_zero,
    pos_half_le,
    reach,
)
from cold_start.parity import TWO
from cold_start.peano import PEANO, mul
from cold_start.presburger import ZERO, S, add
from cold_start.presburger_proofs import ZERO_OR_SUCC
from cold_start.proof import ExistsIntro, Inst, Refl
from cold_start.prop import or_left, or_right
from cold_start.syntax import Eq, Implies, Var, exists
from cold_start.tactics import transport

_a, _n = Var("a"), Var("n")


def _theorem(pf, expected):
    seq = check(pf, PEANO)
    assert not seq.hyps
    assert seq.concl == expected


def test_le_is_a_witnessed_sum():
    w = Var("w")
    assert le(_a, _n) == exists("w", "", Eq(add(_a, w), _n))


def test_le_refl_checks():
    _theorem(le_refl(), le(_a, _a))


def test_le_zero_checks():
    assert LE_ZERO == Implies(le(_a, ZERO), Eq(_a, ZERO))
    _theorem(le_zero(), LE_ZERO)


def test_le_succ_split_checks():
    _theorem(le_succ_split(), LE_SUCC_SPLIT)


def test_le_double_checks():
    assert LE_DOUBLE == le(_a, mul(_a, TWO))
    _theorem(le_double(), LE_DOUBLE)


def test_pos_half_le_checks():
    m = Var("m")
    expected = Implies(
        Eq(_a, S(m)),
        Implies(Eq(mul(_a, TWO), S(_n)), le(_a, _n)),
    )
    _theorem(pos_half_le(), expected)


def test_transport_rewrites_an_existential():
    """pd(1*1, 1*1) becomes pd(1, 1) along the proved 1*1 = 1."""
    from cold_start.divisibility import divides_refl
    from cold_start.peano_proofs import MUL_RULES
    from cold_start.presburger_proofs import ADD_RULES
    from cold_start.tactics import prove_eq

    one = S(ZERO)
    square = mul(one, one)
    hole = Var("t!")
    pattern = peano_divides(hole, hole)
    eq = Eq(square, one)
    eq_pf = prove_eq(eq, (*ADD_RULES, *MUL_RULES))
    moved = transport(pattern, "t!", eq, eq_pf, Inst(divides_refl(), "a", square))
    seq = check(moved, PEANO)
    assert not seq.hyps
    assert seq.concl == peano_divides(one, one)


def test_transport_rewrites_under_a_universal():
    """A forall-formula follows its subject through an equality."""
    from cold_start.peano_proofs import MUL_RULES
    from cold_start.presburger_proofs import ADD_RULES
    from cold_start.proof import Assume, ForallIntro, ImpIntro, Sym
    from cold_start.syntax import forall
    from cold_start.tactics import prove_eq

    one = S(ZERO)
    square = mul(one, one)
    hole, w = Var("t!"), Var("w")
    pattern = forall("w", "", Implies(Eq(w, hole), Eq(hole, w)))
    at_square = ForallIntro("w", "", ImpIntro(Eq(w, square), Sym(Assume(Eq(w, square)))))
    eq = Eq(square, one)
    eq_pf = prove_eq(eq, (*ADD_RULES, *MUL_RULES))
    moved = transport(pattern, "t!", eq, eq_pf, at_square)
    seq = check(moved, PEANO)
    assert not seq.hyps
    assert seq.concl == forall("w", "", Implies(Eq(w, one), Eq(one, w)))


def test_course_of_values_smoke():
    """Strong induction re-derives the zero-or-successor split: neither case
    needs the reach hypothesis, so this exercises only the scaffold."""
    n_bound = Var("n!")
    pred = ZERO_OR_SUCC
    ex_zero = exists("m", "", Eq(ZERO, S(Var("m"))))
    base = or_left(Eq(ZERO, ZERO), ex_zero, Refl(ZERO))
    ex_succ = exists("m", "", Eq(S(n_bound), S(Var("m"))))
    witness = ExistsIntro(ex_succ, n_bound, Refl(S(n_bound)))
    step = or_right(Eq(S(n_bound), ZERO), ex_succ, witness)
    pf = course_of_values("n", pred, "n!", base, step)
    seq = check(pf, PEANO)
    assert not seq.hyps
    assert seq.concl == ZERO_OR_SUCC


def test_reach_shape():
    pred = Eq(_a, _a)
    z = Var("z!")
    got = reach("a", pred, _n)
    from cold_start.syntax import forall

    assert got == forall("z!", "", Implies(le(z, _n), Eq(z, z)))
