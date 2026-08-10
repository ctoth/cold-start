"""Interpretation artifacts around Robinson's ``(S, |)`` multiplication graph.

Two shores are kept distinct:

* ``divisibility_into_peano`` interprets an elementary seven-law divisibility
  theory by ``a|b := exists k, a*k=b``. Every axiom is paid by an actual PEANO
  proof from :mod:`cold_start.divisibility`.
* ``robinson_product_interpretation`` registers Robinson's full 1949 formula
  (2) as a multiplication graph over successor and divisibility. Its empty
  target theory deliberately proves nothing about the standard integers.
* ``robinson_product_into_positive_peano`` composes the graph with ordinary
  PEANO divisibility and guards Robinson's entire positive-integer universe.
  This is the shore on which the deep totality and uniqueness proofs belong.

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
from .interp import GraphSymbol, Interpretation, ObligationKey, PredicateSymbol
from .peano import PEANO, positive_peano
from .proof import ExistsIntro, Pf, Refl
from .robinson_divisibility import divides, robinson_product
from .syntax import Formula, Implies, Var, exists
from .theory import Signature, Theory
from .vocabulary import ZERO, S, mul

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
    ),
    signature=Signature(
        sorts=frozenset({""}),
        ranks=(("0", (), ""), ("S", ("",), ""), ("*", ("", ""), "")),
        relations=(("|", ("", "")),),
    ),
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
        retained_funs=(("0", 0), ("S", 1), ("*", 2)),
        payments=(
            (ObligationKey.axiom(DIVIDES_REFL_ATOM), divides_refl()),
            (ObligationKey.axiom(DIVIDES_TRANS_ATOM), divides_trans()),
            (ObligationKey.axiom(DIVIDES_ZERO_ATOM), divides_zero()),
            (ObligationKey.axiom(ONE_DIVIDES_ATOM), one_divides()),
            (ObligationKey.axiom(DIVIDES_FACTOR_ATOM), divides_factor()),
            (ObligationKey.axiom(DIVIDES_PRODUCT_RIGHT_ATOM), divides_product_right()),
            (ObligationKey.axiom(DIVIDES_PRODUCT_ATOM), divides_product()),
        ),
    )


PRODUCT_FROM_DIVIDES = GraphSymbol(
    "*",
    2,
    lambda args, result: robinson_product(args[0], args[1], result),
)


PRODUCT_IN_POSITIVE_PEANO = GraphSymbol(
    "*",
    2,
    lambda args, result: robinson_product(
        args[0],
        args[1],
        result,
        via=peano_divides,
        domain=positive_peano,
    ),
)

PURE_SUCCESSOR_DIVISIBILITY = Theory(
    axioms=frozenset(),
    signature=Signature(
        sorts=frozenset({""}),
        ranks=(("S", ("",), ""),),
        relations=(("|", ("", "")),),
    ),
)
BARE_MULTIPLICATION = Theory(
    axioms=frozenset(),
    signature=Signature(
        sorts=frozenset({""}),
        ranks=(("*", ("", ""), ""),),
    ),
)


def robinson_product_interpretation() -> Interpretation:
    """Robinson formula (2) as a measured graph with definedness still open."""
    return Interpretation(
        name="robinson-1949-theorem-1.2-product",
        source=BARE_MULTIPLICATION,
        target=PURE_SUCCESSOR_DIVISIBILITY,
        symbols=(PRODUCT_FROM_DIVIDES,),
    )


def _positive_nonempty() -> Pf:
    one_positive = ExistsIntro(positive_peano(ONE), ZERO, Refl(ONE))
    claim = exists("x!", "", positive_peano(Var("x!")))
    return ExistsIntro(claim, ONE, one_positive)


def robinson_product_into_positive_peano() -> Interpretation:
    """Robinson formula (2) on its proof-eligible standard arithmetic shore.

    The graph's own bound variables and the interpretation's external
    arguments/results are all restricted to positive naturals. Divisibility is
    expanded as ``exists k. a*k=b``. Only the genuine number-theory debts stay
    open; nonemptiness is checker-paid at 1.
    """
    return Interpretation(
        name="robinson-1949-theorem-1.2-product-into-positive-peano",
        source=BARE_MULTIPLICATION,
        target=PEANO,
        symbols=(PRODUCT_IN_POSITIVE_PEANO,),
        domain=positive_peano,
        payments=((ObligationKey.domain("nonempty"), _positive_nonempty()),),
    )


__all__ = [
    "BARE_MULTIPLICATION",
    "DIVIDES_IN_PEANO",
    "DIVISIBILITY_CORE",
    "PRODUCT_FROM_DIVIDES",
    "PRODUCT_IN_POSITIVE_PEANO",
    "PURE_SUCCESSOR_DIVISIBILITY",
    "divisibility_into_peano",
    "robinson_product_into_positive_peano",
    "robinson_product_interpretation",
]
