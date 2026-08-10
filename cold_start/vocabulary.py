"""Canonical constructors for the shared arithmetic object language.

Signatures remain the authority for which of these spellings a theory admits.
This module owns only the immutable syntax constructors, so equal arithmetic
symbols cannot drift between theory and prover modules.
"""

from __future__ import annotations

from functools import reduce

from .syntax import Fun, Term

ZERO: Term = Fun("0", ())
ONE: Term = Fun("1", ())


def S(term: Term) -> Term:
    return Fun("S", (term,))


def add(left: Term, right: Term) -> Term:
    return Fun("+", (left, right))


def mul(left: Term, right: Term) -> Term:
    return Fun("*", (left, right))


def neg(term: Term) -> Term:
    return Fun("neg", (term,))


def product(*factors: Term) -> Term:
    """The right-nested product of one or more factors: a*(b*c)."""
    if not factors:
        raise ValueError("a product needs at least one factor")
    return reduce(lambda acc, factor: mul(factor, acc), reversed(factors[:-1]), factors[-1])


def summation(*terms: Term) -> Term:
    """The right-nested sum of one or more terms: a+(b+c)."""
    if not terms:
        raise ValueError("a sum needs at least one term")
    return reduce(lambda acc, term: add(term, acc), reversed(terms[:-1]), terms[-1])


def numeral(value: int) -> Term:
    if type(value) is not int or value < 0:
        raise ValueError("natural numerals require a nonnegative genuine int")
    term = ZERO
    for _ in range(value):
        term = S(term)
    return term


__all__ = [
    "ONE",
    "ZERO",
    "S",
    "add",
    "mul",
    "neg",
    "numeral",
    "product",
    "summation",
]
