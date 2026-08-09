"""Sparse proof-producing polynomial normalization contracts."""

from __future__ import annotations

from typing import cast

import pytest

from cold_start.algebra import COMM_RING
from cold_start.algebra_proofs import COMM_RING_CONTEXT
from cold_start.checker import check
from cold_start.diffring2 import DIFF_RING_2, dx
from cold_start.diffring2_proofs import DIFF_RING_2_CONTEXT
from cold_start.peano import PEANO
from cold_start.peano_proofs import PEANO_SEMIRING_CONTEXT
from cold_start.ring_nf import (
    AlgebraContext,
    Polynomial,
    RingNormalizationError,
    normalize,
    quote,
    ring_eq,
)
from cold_start.sequent import Sequent
from cold_start.syntax import Eq, Rel, Term, Var, forall
from cold_start.vocabulary import ZERO, add, mul, neg


def test_f2_sparse_normalizer_proves_basic_identities_and_duplicate_cancellation() -> None:
    x, y, z = Var("x"), Var("y"), Var("z")
    goals = (
        Eq(add(x, x), ZERO),
        Eq(add(mul(x, y), mul(y, x)), ZERO),
        Eq(mul(add(x, y), z), add(mul(x, z), mul(y, z))),
        Eq(add(x, add(y, add(x, y))), ZERO),
    )
    for goal in goals:
        proof = ring_eq(goal, DIFF_RING_2_CONTEXT)
        assert check(proof, DIFF_RING_2) == Sequent(frozenset(), goal)


def test_f2_sparse_normalizer_preserves_genuine_powers_and_rejects_inequality() -> None:
    x = Var("x")
    squared = normalize(mul(x, x), DIFF_RING_2_CONTEXT)
    linear = normalize(x, DIFF_RING_2_CONTEXT)

    assert squared.term == mul(x, x)
    assert squared.polynomial != linear.polynomial
    with pytest.raises(RingNormalizationError, match="different polynomials"):
        ring_eq(Eq(mul(x, x), x), DIFF_RING_2_CONTEXT)


@pytest.mark.parametrize("coefficient", [0, 2, -1])
def test_quote_rejects_noncanonical_f2_coefficients(coefficient: int) -> None:
    polynomial = Polynomial((((), coefficient),))

    with pytest.raises(RingNormalizationError, match="noncanonical coefficient"):
        quote(polynomial, DIFF_RING_2_CONTEXT)


def test_f2_sparse_normalizer_rejects_derivatives_binders_and_relations() -> None:
    x = Var("x")
    unsupported = (
        dx(x),
        cast(Term, forall("x", "", Eq(x, x))),
        cast(Term, Rel("R", (x,))),
    )
    for term in unsupported:
        with pytest.raises(RingNormalizationError, match="unsupported"):
            normalize(term, DIFF_RING_2_CONTEXT)


def test_f2_context_cannot_smuggle_characteristic_two_into_other_theories() -> None:
    x = Var("x")
    goal = Eq(add(x, x), ZERO)
    proof = ring_eq(goal, DIFF_RING_2_CONTEXT)

    assert check(proof, DIFF_RING_2).concl == goal
    for theory in (PEANO, COMM_RING):
        with pytest.raises(ValueError, match="not an axiom"):
            check(proof, theory)


def test_natural_semiring_normalization_is_independent_of_f2() -> None:
    x, y = Var("x"), Var("y")
    goal = Eq(
        mul(add(x, y), add(x, y)),
        add(mul(x, x), add(mul(x, y), add(mul(x, y), mul(y, y)))),
    )

    proof = ring_eq(goal, PEANO_SEMIRING_CONTEXT)

    assert PEANO_SEMIRING_CONTEXT.coefficient_domain == "natural"
    assert check(proof, PEANO) == Sequent(frozenset(), goal)


def test_signed_ring_normalization_is_independent_of_f2() -> None:
    x, y = Var("x"), Var("y")
    goals = (
        Eq(
            mul(neg(add(x, y)), neg(x)),
            add(mul(x, x), mul(y, x)),
        ),
        Eq(neg(neg(x)), x),
        Eq(add(neg(x), x), ZERO),
        Eq(mul(ZERO, x), ZERO),
        Eq(neg(ZERO), ZERO),
    )

    assert COMM_RING_CONTEXT.coefficient_domain == "integer"
    for goal in goals:
        proof = ring_eq(goal, COMM_RING_CONTEXT)
        assert check(proof, COMM_RING) == Sequent(frozenset(), goal)


def test_coefficient_policy_and_cancellation_recipe_cannot_be_mixed() -> None:
    context = PEANO_SEMIRING_CONTEXT
    with pytest.raises(ValueError, match="mod2.*cancellation"):
        AlgebraContext(
            zero=context.zero,
            one=context.one,
            add=context.add,
            mul=context.mul,
            neg=context.neg,
            successor=context.successor,
            coefficient_domain="mod2",
            atoms=context.atoms,
            merge_rules=context.merge_rules,
            right_cancellation=context.right_cancellation,
            rewrite_budget=context.rewrite_budget,
        )
