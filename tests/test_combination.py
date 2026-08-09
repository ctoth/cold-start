"""Shared sparse semiring normalization and linear combinations.

The PEANO context supplies proved merge and cancellation recipes to the one
sparse normalizer. ``elaborate_combination`` proves an equation from equational
hypotheses summed with optional term coefficients.
"""

from __future__ import annotations

import pytest

from cold_start.algebra import COMM_RING
from cold_start.algebra_proofs import COMM_RING_CONTEXT
from cold_start.checker import check
from cold_start.peano import PEANO
from cold_start.peano_proofs import PEANO_SEMIRING_CONTEXT
from cold_start.proof import Assume
from cold_start.ring_nf import elaborate_combination, ring_eq
from cold_start.syntax import Eq, Var
from cold_start.tactics import TacticError
from cold_start.vocabulary import ZERO, S, add, mul, neg

_x, _y, _z, _k = Var("x"), Var("y"), Var("z"), Var("k")


# ---------------------------------------------------------------------------
# Sparse natural-coefficient normalization
# ---------------------------------------------------------------------------


def _proves(goal: Eq) -> None:
    pf = ring_eq(goal, PEANO_SEMIRING_CONTEXT)
    seq = check(pf, PEANO)
    assert not seq.hyps
    assert seq.concl == goal


def test_semiring_context_decides_distribution_with_reordering() -> None:
    # (x + y) * z  =  z*y + x*z  -- distribution plus AC on both operations.
    _proves(Eq(mul(add(_x, _y), _z), add(mul(_z, _y), mul(_x, _z))))


def test_semiring_context_decides_a_binomial_expansion() -> None:
    # (x + y) * (x + y)  =  x*x + (x*y + (y*x + y*y)) in any spelling.
    lhs = mul(add(_x, _y), add(_x, _y))
    rhs = add(add(mul(_x, _x), mul(_x, _y)), add(mul(_y, _x), mul(_y, _y)))
    _proves(Eq(lhs, rhs))


def test_semiring_context_decides_multiplicative_units_both_sides() -> None:
    one = S(ZERO)
    _proves(Eq(mul(_x, one), _x))
    _proves(Eq(mul(one, _x), _x))


def test_semiring_context_decides_annihilation_both_sides() -> None:
    _proves(Eq(mul(_x, ZERO), ZERO))
    _proves(Eq(mul(ZERO, _x), ZERO))


def test_semiring_context_decides_mul_left_comm_through_a_product() -> None:
    # x*(y*z) = z*(y*x): only reachable with ordered multiplicative sorting.
    _proves(Eq(mul(_x, mul(_y, _z)), mul(_z, mul(_y, _x))))


def test_semiring_context_refuses_a_false_identity() -> None:
    with pytest.raises(TacticError):
        ring_eq(Eq(mul(_x, _y), add(_x, _y)), PEANO_SEMIRING_CONTEXT)


# ---------------------------------------------------------------------------
# Linear combinations with term coefficients
# ---------------------------------------------------------------------------


def test_without_coefficients_it_is_the_cancellation_recipe() -> None:
    # Transitivity by cancellation: x = z from x = y and y = z.
    h1, h2 = Eq(_x, _y), Eq(_y, _z)
    goal = Eq(_x, _z)
    pf = elaborate_combination(
        goal,
        ((h1, Assume(h1), None), (h2, Assume(h2), None)),
        PEANO_SEMIRING_CONTEXT,
    )
    seq = check(pf, PEANO)
    assert seq.hyps == frozenset({h1, h2})
    assert seq.concl == goal


def test_a_coefficient_multiplies_a_hypothesis_through() -> None:
    # From x = y conclude x*k = y*k: the hypothesis is scaled by the term k.
    h = Eq(_x, _y)
    goal = Eq(mul(_x, _k), mul(_y, _k))
    pf = elaborate_combination(goal, ((h, Assume(h), _k),), PEANO_SEMIRING_CONTEXT)
    seq = check(pf, PEANO)
    assert seq.hyps == frozenset({h})
    assert seq.concl == goal


def test_scaled_and_unscaled_hypotheses_mix() -> None:
    # From x = y (scaled by k) and z = k conclude x*k + z = y*k + k.
    h1, h2 = Eq(_x, _y), Eq(_z, _k)
    goal = Eq(add(mul(_x, _k), _z), add(mul(_y, _k), _k))
    pf = elaborate_combination(
        goal,
        ((h1, Assume(h1), _k), (h2, Assume(h2), None)),
        PEANO_SEMIRING_CONTEXT,
    )
    seq = check(pf, PEANO)
    assert seq.hyps == frozenset({h1, h2})
    assert seq.concl == goal


def test_no_hypotheses_falls_back_to_the_kit_alone() -> None:
    goal = Eq(add(_x, _y), add(_y, _x))
    pf = elaborate_combination(goal, (), PEANO_SEMIRING_CONTEXT)
    seq = check(pf, PEANO)
    assert not seq.hyps
    assert seq.concl == goal


def test_a_misoriented_hypothesis_fails_loudly() -> None:
    # Summing y = x and y = z can never balance x = z: prove_eq raises.
    h1, h2 = Eq(_y, _x), Eq(_y, _z)
    with pytest.raises(TacticError):
        elaborate_combination(
            Eq(_x, _z),
            ((h1, Assume(h1), None), (h2, Assume(h2), None)),
            PEANO_SEMIRING_CONTEXT,
        )


def test_signed_combination_uses_the_general_ring_cancellation_recipe() -> None:
    hypothesis = Eq(_x, _y)
    goal = Eq(add(_x, neg(_y)), ZERO)

    proof = elaborate_combination(
        goal,
        ((hypothesis, Assume(hypothesis), None),),
        COMM_RING_CONTEXT,
    )

    sequent = check(proof, COMM_RING)
    assert sequent.hyps == frozenset({hypothesis})
    assert sequent.concl == goal
