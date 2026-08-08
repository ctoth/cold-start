"""Sparse proof-producing polynomial normalization contracts."""

from __future__ import annotations

from typing import cast

import pytest

from cold_start.checker import check
from cold_start.diffring2 import DIFF_RING_2, dx
from cold_start.diffring2_proofs import DIFF_RING_2_CONTEXT
from cold_start.peano import PEANO
from cold_start.ring_nf import RingNormalizationError, normalize, ring_eq
from cold_start.sequent import Sequent
from cold_start.syntax import Eq, Rel, Term, Var, forall
from cold_start.vocabulary import ZERO, add, mul


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


def test_f2_context_cannot_smuggle_characteristic_two_into_peano() -> None:
    x = Var("x")
    goal = Eq(add(x, x), ZERO)
    proof = ring_eq(goal, DIFF_RING_2_CONTEXT)

    assert check(proof, DIFF_RING_2).concl == goal
    with pytest.raises(ValueError, match="not an axiom"):
        check(proof, PEANO)
