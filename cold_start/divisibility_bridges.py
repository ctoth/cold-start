"""Interpretation artifacts around Robinson's ``(S, |)`` multiplication graph.

Two shores are kept distinct:

* ``divisibility_into_peano`` interprets an elementary seven-law divisibility
  theory by ``a|b := exists k, a*k=b``. Every axiom is paid by an actual PEANO
  proof from :mod:`cold_start.divisibility`.
* ``robinson_product_interpretation`` registers Robinson's full 1949 formula
  (2) as a multiplication graph over successor and divisibility. Its empty
  target theory deliberately proves nothing about the standard integers, so the
  report exposes exactly the deep remaining debts: totality and uniqueness.

An open bridge is a measured conjecture with a ledger, never a theorem claim.
"""

from __future__ import annotations

from .divisibility import (
    divides_factor,
    divides_product,
    divides_product_right,
    divides_refl,
    divides_trans,
    divides_zero,
    one_divides,
    peano_divides,
)
from .interp import GraphSymbol, Interpretation, PredicateSymbol
from .peano import PEANO, mul
from .presburger import ZERO, S
from .robinson_divisibility import divides, robinson_product
from .syntax import Formula, Implies, Var
from .theory import Theory

ONE = S(ZERO)
_a, _b, _c = Var("a"), Var("b"), Var("c")

DIVIDES_REFL_ATOM: Formula = divides(_a, _a)
DIVIDES_TRANS_ATOM: Formula = Implies(
    divides(_a, _b),
    Implies(divides(_b, _c), divides(_a, _c)),
)
DIVIDES_ZERO_ATOM: Formula = divides(_a, ZERO)
ONE_DIVIDES_ATOM: Formula = divides(ONE, _a)
DIVIDES_FACTOR_ATOM: Formula = divides(_a, mul(_a, _b))
DIVIDES_PRODUCT_RIGHT_ATOM: Formula = divides(_b, mul(_a, _b))
DIVIDES_PRODUCT_ATOM: Formula = Implies(
    divides(_a, _b),
    divides(_a, mul(_b, _c)),
)

DIVISIBILITY_CORE = Theory(
    axioms=frozenset(
        {
            DIVIDES_REFL_ATOM,
            DIVIDES_TRANS_ATOM,
            DIVIDES_ZERO_ATOM,
            ONE_DIVIDES_ATOM,
            DIVIDES_FACTOR_ATOM,
            DIVIDES_PRODUCT_RIGHT_ATOM,
            DIVIDES_PRODUCT_ATOM,
        }
    )
)

DIVIDES_IN_PEANO = PredicateSymbol(
    "|",
    2,
    lambda args: peano_divides(args[0], args[1]),
)


def divisibility_into_peano() -> Interpretation:
    """The seven elementary divisibility laws, all checker-paid in PEANO."""
    return Interpretation(
        name="divisibility-foundations-into-peano",
        source=DIVISIBILITY_CORE,
        target=PEANO,
        symbols=(),
        predicates=(DIVIDES_IN_PEANO,),
        payments=(
            (f"axiom:{DIVIDES_REFL_ATOM!r}", divides_refl()),
            (f"axiom:{DIVIDES_TRANS_ATOM!r}", divides_trans()),
            (f"axiom:{DIVIDES_ZERO_ATOM!r}", divides_zero()),
            (f"axiom:{ONE_DIVIDES_ATOM!r}", one_divides()),
            (f"axiom:{DIVIDES_FACTOR_ATOM!r}", divides_factor()),
            (f"axiom:{DIVIDES_PRODUCT_RIGHT_ATOM!r}", divides_product_right()),
            (f"axiom:{DIVIDES_PRODUCT_ATOM!r}", divides_product()),
        ),
    )


PRODUCT_FROM_DIVIDES = GraphSymbol(
    "*",
    2,
    lambda args, result: robinson_product(args[0], args[1], result),
)

PURE_SUCCESSOR_DIVISIBILITY = Theory(axioms=frozenset())
BARE_MULTIPLICATION = Theory(axioms=frozenset())


def robinson_product_interpretation() -> Interpretation:
    """Robinson formula (2) as a measured graph with definedness still open."""
    return Interpretation(
        name="robinson-1949-theorem-1.2-product",
        source=BARE_MULTIPLICATION,
        target=PURE_SUCCESSOR_DIVISIBILITY,
        symbols=(PRODUCT_FROM_DIVIDES,),
    )


__all__ = [
    "BARE_MULTIPLICATION",
    "DIVIDES_IN_PEANO",
    "DIVISIBILITY_CORE",
    "PRODUCT_FROM_DIVIDES",
    "PURE_SUCCESSOR_DIVISIBILITY",
    "divisibility_into_peano",
    "robinson_product_interpretation",
]
