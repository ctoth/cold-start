"""Independent guards for the characteristic-two Promislow group ring."""

from __future__ import annotations

from typing import TypeAlias

from hypothesis import given
from hypothesis import strategies as st

from cold_start.algebra import COMM
from cold_start.checker import check
from cold_start.groupring2 import (
    A_INV,
    B_INV,
    CHAR2,
    GROUP_REL_A,
    GROUP_REL_B,
    GROUP_RING_P2,
    NONTRIVIAL,
    A,
    B,
)
from cold_start.kaplansky_proofs import (
    ground_multiplication_lemmas,
    group_term,
    lemma_library,
    witness_coordinates,
)
from cold_start.sequent import Sequent
from cold_start.syntax import Fun, Term
from cold_start.verify import THEORIES

GElem: TypeAlias = tuple[int, int, int, int]
RingElem: TypeAlias = frozenset[GElem]

GID: GElem = (0, 0, 0, 0)
R_ZERO: RingElem = frozenset()
R_ONE: RingElem = frozenset({GID})

_COCYCLE = (
    ((0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)),
    ((0, 0, 0), (1, 0, 0), (0, 0, 0), (1, 0, 0)),
    ((0, 0, 0), (-1, 1, -1), (0, 1, 0), (-1, 0, -1)),
    ((0, 0, 0), (0, -1, 1), (0, -1, 0), (0, 0, 1)),
)


def _gact(w: int, n: tuple[int, int, int]) -> tuple[int, int, int]:
    i, j, k = n
    signs = ((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1))[w]
    return signs[0] * i, signs[1] * j, signs[2] * k


def _gmul(g: GElem, h: GElem) -> GElem:
    i, j, k, w = g
    ai, aj, ak = _gact(w, h[:3])
    ci, cj, ck = _COCYCLE[w][h[3]]
    return i + ai + ci, j + aj + cj, k + ak + ck, w ^ h[3]


def _ginv(g: GElem) -> GElem:
    i, j, k, w = g
    ci, cj, ck = _COCYCLE[w][w]
    ni, nj, nk = _gact(w, (-i - ci, -j - cj, -k - ck))
    return ni, nj, nk, w


def _rmul(left: RingElem, right: RingElem) -> RingElem:
    result: set[GElem] = set()
    for g in left:
        for h in right:
            result.symmetric_difference_update({_gmul(g, h)})
    return frozenset(result)


_A_ELEM: GElem = (0, 0, 0, 1)
_B_ELEM: GElem = (0, 0, 0, 2)
_CONSTANTS: dict[str, RingElem] = {
    "0": R_ZERO,
    "1": R_ONE,
    "A": frozenset({_A_ELEM}),
    "B": frozenset({_B_ELEM}),
    "A'": frozenset({_ginv(_A_ELEM)}),
    "B'": frozenset({_ginv(_B_ELEM)}),
}


def evaluate(term: Term) -> RingElem:
    if type(term) is Fun:
        if term.name in _CONSTANTS:
            return _CONSTANTS[term.name]
        args = tuple(evaluate(arg) for arg in term.args)
        if term.name == "+":
            return args[0] ^ args[1]
        if term.name == "*":
            return _rmul(args[0], args[1])
    raise AssertionError(f"model cannot evaluate {term!r}")


gelems = st.tuples(
    st.integers(-8, 8),
    st.integers(-8, 8),
    st.integers(-8, 8),
    st.integers(0, 3),
)


@given(gelems, gelems, gelems)
def test_independent_coordinate_model_is_associative(g, h, k):
    assert _gmul(_gmul(g, h), k) == _gmul(g, _gmul(h, k))


def test_theory_validates_without_multiplicative_commutativity():
    GROUP_RING_P2.validate()
    assert CHAR2 in GROUP_RING_P2.axioms
    assert NONTRIVIAL in GROUP_RING_P2.axioms
    assert GROUP_REL_A in GROUP_RING_P2.axioms
    assert GROUP_REL_B in GROUP_RING_P2.axioms
    assert COMM not in GROUP_RING_P2.axioms
    assert THEORIES["groupring2"] is GROUP_RING_P2


def test_generators_inverses_and_relations_hold_in_independent_model():
    assert _rmul(evaluate(A), evaluate(A_INV)) == R_ONE
    assert _rmul(evaluate(A_INV), evaluate(A)) == R_ONE
    assert _rmul(evaluate(B), evaluate(B_INV)) == R_ONE
    assert _rmul(evaluate(B_INV), evaluate(B)) == R_ONE
    for relation in (GROUP_REL_A, GROUP_REL_B):
        assert evaluate(relation.lhs) == evaluate(relation.rhs)


def test_normal_form_lemma_library_is_checked_and_model_guarded():
    rules = lemma_library()
    assert len(rules) == 40
    for rule in rules:
        assert check(rule.proof, GROUP_RING_P2) == Sequent(frozenset(), rule.eq)
        ground = rule.eq
        for name in ground.free_vars():
            ground = ground.subst(name, A)
        assert evaluate(ground.lhs) == evaluate(ground.rhs)


def test_witness_words_and_all_uv_ground_products_are_certified():
    u, v = witness_coordinates()
    assert len(u) == len(v) == 21
    for coordinate in (*u, *v):
        assert evaluate(group_term(coordinate)) == frozenset({coordinate})

    rules = ground_multiplication_lemmas(u, v)
    assert len(rules) == 441
    for rule in rules:
        assert check(rule.proof, GROUP_RING_P2) == Sequent(frozenset(), rule.eq)
        assert evaluate(rule.eq.lhs) == evaluate(rule.eq.rhs)
