"""Parity foundations: the 2-adic case split and Euclid's lemma at 2.

Every recipe below must re-derive its exact sequent, hypothesis-free, through
the trusted checker in PEANO. `euclid_two` is the load-bearing one: it is the
first instance of Euclid's lemma in the repository, and the H1 debt of the
formula (2) ledger begins here.
"""

from __future__ import annotations

from semantics import assert_theorem

from cold_start.parity import (
    CANCEL_TWO,
    EUCLID_TWO,
    EVEN_NE_ODD,
    PARITY,
    TWO,
    cancel_two,
    euclid_two,
    even_ne_odd,
    parity,
)
from cold_start.peano import PEANO
from cold_start.vocabulary import ZERO, S, mul


def test_two_is_the_second_numeral():
    assert TWO == S(S(ZERO))


def test_parity_checks():
    assert_theorem(parity(), PARITY, PEANO)


def test_even_ne_odd_checks():
    assert_theorem(even_ne_odd(), EVEN_NE_ODD, PEANO)


def test_cancel_two_checks():
    assert_theorem(cancel_two(), CANCEL_TWO, PEANO)


def test_euclid_two_checks():
    assert_theorem(euclid_two(), EUCLID_TWO, PEANO)


def test_euclid_two_shape():
    """The statement really is Euclid at 2: odd d dividing x*2 divides x."""
    from cold_start.divisibility import peano_divides
    from cold_start.syntax import Implies, Not, Var

    d, x = Var("d"), Var("x")
    assert EUCLID_TWO == Implies(
        Not(peano_divides(TWO, d)),
        Implies(peano_divides(d, mul(x, TWO)), peano_divides(d, x)),
    )
