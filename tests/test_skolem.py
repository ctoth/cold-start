"""The Skolem shore: Presburger addition interpreted into multiplication.

The artifact translates the WHOLE additive signature away -- 0 becomes 1, the
successor becomes doubling, addition becomes multiplication -- and lands on
the powers of two inside PEANO, the domain carved out by divisibility alone.
Ten of its eleven obligations must be checker-paid; the single open debt is
`totality:+` (closure of the powers of two under multiplication), which needs
strong induction the repo does not yet own, and the report must say so."""

from __future__ import annotations

from semantics import Model, evaluate

from cold_start.checker import check
from cold_start.interp import verify
from cold_start.parity import TWO
from cold_start.peano import PEANO, mul
from cold_start.presburger import PRESBURGER, ZERO, S
from cold_start.skolem import (
    POW2_DOUBLE,
    pow2,
    pow2_double,
    pow2_one,
    skolem_interpretation,
)
from cold_start.syntax import Var

ONE = S(ZERO)


def test_pow2_one_checks():
    seq = check(pow2_one(), PEANO)
    assert not seq.hyps
    assert seq.concl == pow2(ONE)


def test_pow2_double_checks():
    seq = check(pow2_double(), PEANO)
    assert not seq.hyps
    assert seq.concl == POW2_DOUBLE


def test_pow2_means_power_of_two():
    """In a bounded standard model, the domain formula holds exactly at the
    powers of two -- zero, in particular, is excluded."""
    limit = 33
    model = Model(
        "bounded-naturals",
        {"0": lambda: 0, "S": lambda n: n + 1, "*": lambda a, b: a * b, "+": lambda a, b: a + b},
        carriers={"": tuple(range(limit))},
    )
    powers = {1, 2, 4, 8, 16}
    for n in range(limit // 2):
        value = evaluate(pow2(Var("x")), model, {"x": n})
        assert value == (n in powers), n


def test_not_pow2_zero_checks():
    from cold_start.skolem import NOT_POW2_ZERO, not_pow2_zero

    seq = check(not_pow2_zero(), PEANO)
    assert not seq.hyps
    assert seq.concl == NOT_POW2_ZERO


def test_pow2_half_checks():
    from cold_start.skolem import POW2_HALF, pow2_half

    seq = check(pow2_half(), PEANO)
    assert not seq.hyps
    assert seq.concl == POW2_HALF


def test_pow2_mul_checks():
    """Product closure of the powers of two -- by strong induction, descending
    through the dyadic layers with Euclid's lemma at 2."""
    from cold_start.skolem import POW2_MUL, pow2_mul

    seq = check(pow2_mul(), PEANO)
    assert not seq.hyps
    assert seq.concl == POW2_MUL


def test_skolem_bridge_report():
    """Every obligation is paid: the bridge is a theorem, not a conjecture."""
    report = verify(skolem_interpretation())
    assert report.name == "presburger-into-skolem-powers-of-two"
    assert report.open_labels() == ()
    assert report.complete
    paid = [s for s in report.statuses if s.paid]
    assert len(paid) == 11
    assert all(s.toll > 0 for s in paid)
    assert report.bridge_size == 16


def test_skolem_bridge_endpoints():
    interp = skolem_interpretation()
    assert interp.source is PRESBURGER
    assert interp.target is PEANO
    assert interp.domain is pow2
    assert interp.retained_funs == ()
    assert interp.retained_consts == ()
    graphs = {s.fun: s for s in interp.symbols}
    assert set(graphs) == {"0", "S", "+"}
    x, c = Var("x"), Var("c")
    from cold_start.syntax import Eq

    assert graphs["0"].graph((), c) == Eq(c, ONE)
    assert graphs["S"].graph((x,), c) == Eq(mul(x, TWO), c)
    assert graphs["+"].graph((x, Var("y")), c) == Eq(mul(x, Var("y")), c)
