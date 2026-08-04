"""Divisibility unfolded into multiplication, with PEANO proof certificates."""

from __future__ import annotations

from semantics import Model, evaluate

from cold_start.checker import check
from cold_start.divisibility import (
    DIVIDES_ADD,
    DIVIDES_FACTOR,
    DIVIDES_MUL_LEFT,
    DIVIDES_PRODUCT,
    DIVIDES_PRODUCT_RIGHT,
    DIVIDES_REFL,
    DIVIDES_TRANS,
    DIVIDES_ZERO,
    ONE_DIVIDES,
    divides_add,
    divides_factor,
    divides_mul_left,
    divides_product,
    divides_product_right,
    divides_refl,
    divides_trans,
    divides_zero,
    one_divides,
    peano_divides,
)
from cold_start.peano import PEANO, mul
from cold_start.presburger import ZERO, S, add
from cold_start.syntax import Eq, Implies, Var, exists

ONE = S(ZERO)


def test_peano_divisibility_is_a_hygienic_existential_graph():
    a, b, k = Var("a"), Var("b"), Var("k")

    assert peano_divides(a, b) == exists("k", "", Eq(mul(a, k), b))
    assert peano_divides(k, b).free_vars() == frozenset({"k", "b"})


def test_every_number_divides_itself_is_checked_in_peano():
    seq = check(divides_refl(), PEANO)

    assert not seq.hyps
    assert seq.concl == DIVIDES_REFL


def test_a_factor_divides_its_product_is_checked_in_peano():
    seq = check(divides_factor(), PEANO)

    assert not seq.hyps
    assert seq.concl == DIVIDES_FACTOR


def test_divisibility_transitivity_is_checked_in_peano():
    seq = check(divides_trans(), PEANO)

    assert not seq.hyps
    assert seq.concl == DIVIDES_TRANS


def test_every_number_divides_zero_is_checked_in_peano():
    seq = check(divides_zero(), PEANO)

    assert not seq.hyps
    assert seq.concl == DIVIDES_ZERO


def test_one_divides_every_number_is_checked_in_peano():
    seq = check(one_divides(), PEANO)

    assert not seq.hyps
    assert seq.concl == ONE_DIVIDES


def test_both_factors_divide_a_product_in_peano():
    left = check(divides_factor(), PEANO)
    right = check(divides_product_right(), PEANO)

    assert left.concl == DIVIDES_FACTOR
    assert right.concl == DIVIDES_PRODUCT_RIGHT
    assert not left.hyps and not right.hyps


def test_a_divisor_still_divides_after_multiplication():
    seq = check(divides_product(), PEANO)

    assert not seq.hyps
    assert seq.concl == DIVIDES_PRODUCT


def test_a_common_divisor_divides_a_sum_in_peano():
    a, b, c = Var("a"), Var("b"), Var("c")
    seq = check(divides_add(), PEANO)

    assert not seq.hyps
    assert seq.concl == DIVIDES_ADD
    assert DIVIDES_ADD == Implies(
        peano_divides(a, b),
        Implies(peano_divides(a, c), peano_divides(a, add(b, c))),
    )


def test_divisibility_is_preserved_by_a_common_left_factor_in_peano():
    a, b, c = Var("a"), Var("b"), Var("c")
    seq = check(divides_mul_left(), PEANO)

    assert not seq.hyps
    assert seq.concl == DIVIDES_MUL_LEFT
    assert DIVIDES_MUL_LEFT == Implies(
        peano_divides(a, b),
        peano_divides(mul(c, a), mul(c, b)),
    )


def test_transitivity_formula_has_the_expected_mathematical_shape():
    a, b, c = Var("a"), Var("b"), Var("c")

    assert DIVIDES_TRANS == Implies(
        peano_divides(a, b),
        Implies(peano_divides(b, c), peano_divides(a, c)),
    )


def test_checked_divisibility_claims_hold_in_bounded_standard_arithmetic():
    model = Model(
        "bounded N",
        interp={
            "0": lambda: 0,
            "S": lambda x: x + 1,
            "+": lambda a, b: a + b,
            "*": lambda a, b: a * b,
        },
        carriers={"": tuple(range(31))},
    )

    for value in range(10):
        assert evaluate(DIVIDES_REFL, model, {"a": value})
    for a in range(6):
        for b in range(6):
            assert evaluate(DIVIDES_FACTOR, model, {"a": a, "b": b})
