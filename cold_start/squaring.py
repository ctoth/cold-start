"""Arithmetic with addition and a primitive square operation.

The square function is characterized without multiplication:

    sq(0)    = 0
    sq(S(x)) = sq(x) + S(x + x)

The second equation is ``(x+1)^2 = x^2 + 2x + 1`` in the object language.
Together with Presburger induction these axioms describe standard squaring and
are the honest target theory for the subtraction-free polarization bridge.
"""

from __future__ import annotations

from dataclasses import replace

from .presburger import PRESBURGER, ZERO, S, add
from .syntax import Eq, Formula, Fun, Term, Var


def sq(term: Term) -> Term:
    return Fun("sq", (term,))


def double(term: Term) -> Term:
    return add(term, term)


def square_product(left: Term, right: Term, result: Term) -> Eq:
    """The subtraction-free polarization graph for ``result = left*right``."""
    return Eq(
        add(add(double(result), sq(left)), sq(right)),
        sq(add(left, right)),
    )


_x = Var("x")

SQUARE_ZERO_F: Formula = Eq(sq(ZERO), ZERO)
SQUARE_SUCC_F: Formula = Eq(
    sq(S(_x)),
    add(sq(_x), S(add(_x, _x))),
)

SQUARE_ARITHMETIC = replace(
    PRESBURGER,
    axioms=PRESBURGER.axioms | {SQUARE_ZERO_F, SQUARE_SUCC_F},
)


__all__ = [
    "SQUARE_ARITHMETIC",
    "SQUARE_SUCC_F",
    "SQUARE_ZERO_F",
    "double",
    "sq",
    "square_product",
]
