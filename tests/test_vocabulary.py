"""Canonical arithmetic vocabulary ownership and declared Robinson language."""

import pytest

from cold_start.robinson import ONE, ROBINSON_SIG
from cold_start.syntax import Fun, Var
from cold_start.vocabulary import ONE as CANONICAL_ONE
from cold_start.vocabulary import add, mul, product, summation


def test_robinson_uses_a_primitive_one_not_hidden_zero() -> None:
    assert ONE is CANONICAL_ONE
    assert ONE == Fun("1", ())
    assert ROBINSON_SIG.rank("1") == ((), "")
    assert ROBINSON_SIG.rank("0") is None


def test_products_and_sums_of_many_terms_are_right_nested() -> None:
    a, b, c = Var("a"), Var("b"), Var("c")
    assert product(a) == a
    assert product(a, b) == mul(a, b)
    assert product(a, b, c) == mul(a, mul(b, c))
    assert summation(a) == a
    assert summation(a, b, c) == add(a, add(b, c))


def test_a_product_or_sum_of_nothing_is_not_a_term() -> None:
    with pytest.raises(ValueError):
        product()
    with pytest.raises(ValueError):
        summation()
