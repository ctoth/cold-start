"""Deterministic F2 Groebner search and ordinary-proof elaboration."""

from __future__ import annotations

from dataclasses import replace

import pytest

from cold_start.checker import check
from cold_start.diffring2 import DIFF_RING_2
from cold_start.diffring2_proofs import DIFF_RING_2_CONTEXT
from cold_start.groebner2 import (
    DEFAULT_GROEBNER_LIMITS,
    CertifiedMembership,
    NotMember,
    SearchExhausted,
    prove_ideal_membership,
    search_ideal_membership,
)
from cold_start.proof import Assume
from cold_start.ring_nf import Polynomial, RingNormalizationError, elaborate_ideal_membership
from cold_start.sequent import Sequent
from cold_start.syntax import Eq, Var
from cold_start.vocabulary import ONE, ZERO, mul


def _nontrivial_s_pair_problem():
    x, y = Var("x"), Var("y")
    generators = (
        Eq(mul(x, y), ONE),
        Eq(mul(y, y), y),
    )
    goal = Eq(mul(x, y), y)
    return generators, goal


def test_nontrivial_s_polynomial_returns_cofactors_and_checked_conditional_proof() -> None:
    generators, goal = _nontrivial_s_pair_problem()
    sources = tuple((equation, Assume(equation)) for equation in generators)

    result = prove_ideal_membership(goal, sources, DIFF_RING_2_CONTEXT)

    assert isinstance(result, CertifiedMembership)
    assert result.witness.stats.critical_pairs >= 1
    assert result.witness.stats.basis_size >= 3
    assert any(cofactor.terms for cofactor in result.witness.cofactors)
    assert check(result.proof, DIFF_RING_2) == Sequent(frozenset(generators), goal)


def test_corrupted_cofactor_vector_fails_before_a_candidate_proof() -> None:
    generators, goal = _nontrivial_s_pair_problem()
    sources = tuple((equation, Assume(equation)) for equation in generators)
    zeroes = tuple(Polynomial(()) for _ in generators)

    with pytest.raises(RingNormalizationError, match="different polynomials"):
        elaborate_ideal_membership(
            goal,
            sources,
            zeroes,
            DIFF_RING_2_CONTEXT,
        )


def test_true_nonmember_and_budget_exhaustion_are_distinct_outcomes() -> None:
    x, y = Var("x"), Var("y")
    nonmember = search_ideal_membership(
        Eq(x, ZERO),
        (Eq(mul(x, y), ZERO),),
        DIFF_RING_2_CONTEXT,
    )
    assert isinstance(nonmember, NotMember)
    assert nonmember.remainder.terms

    generators, goal = _nontrivial_s_pair_problem()
    exhausted = search_ideal_membership(
        goal,
        generators,
        DIFF_RING_2_CONTEXT,
        limits=replace(DEFAULT_GROEBNER_LIMITS, max_steps=1),
    )
    assert isinstance(exhausted, SearchExhausted)
    assert "steps" in exhausted.reason


def test_characteristic_two_search_does_not_assume_boolean_idempotence() -> None:
    x = Var("x")
    result = search_ideal_membership(
        Eq(mul(x, x), x),
        (),
        DIFF_RING_2_CONTEXT,
    )
    assert isinstance(result, NotMember)
