"""Peano arithmetic as a *theory*: a signature, axioms, and induction data.

The checker is theory-agnostic; this module supplies what makes it arithmetic.
Everything trusted here is small and on the page: two addition axioms plus the
zero term and successor symbol used by the checker's first-class `Induct` rule.
Induction is deliberately not exposed as an axiom formula.
"""

from __future__ import annotations

from .checker import Theory
from .proof import Induct, Pf
from .syntax import (
    Eq,
    Formula,
    Fun,
    Implies,
    Not,
    Term,
    Var,
)

# --- signature ------------------------------------------------------------

ZERO = Fun("0", ())


def S(t: Term) -> Term:
    return Fun("S", (t,))


def add(a: Term, b: Term) -> Term:
    return Fun("+", (a, b))


def numeral(n: int) -> Term:
    if n < 0:
        raise ValueError("naturals only")
    t: Term = ZERO
    for _ in range(n):
        t = S(t)
    return t


# --- axioms (the trusted base) -------------------------------------------
# Recursive definition of addition. Free vars implicitly universally quantified.

ADD_ZERO_F: Formula = Eq(add(Var("x"), ZERO), Var("x"))  # x + 0 = x
ADD_SUCC_F: Formula = Eq(add(Var("x"), S(Var("y"))), S(add(Var("x"), Var("y"))))  # x + S y = S(x+y)

# The two Peano axioms that need negation: 0 is not a successor, and successor is
# injective. Together they make distinct numerals provably unequal -- retiring
# the model-only witness we used before `Not` existed.
SUCC_NEQ_ZERO: Formula = Not(Eq(S(Var("x")), ZERO))  # S x != 0
SUCC_INJ: Formula = Implies(Eq(S(Var("x")), S(Var("y"))), Eq(Var("x"), Var("y")))  # Sx=Sy -> x=y


# Induction is a *rule*, not an axiom (encoding the schema as an axiom formula
# is unsound here -- see checker.Theory). The theory just declares its zero and
# successor so the checker's Induct rule knows the recursion structure.
PEANO = Theory(
    axioms=frozenset({ADD_ZERO_F, ADD_SUCC_F, SUCC_NEQ_ZERO, SUCC_INJ}),
    zero=ZERO,
    succ="S",
)


# --- inference: induction ------------------------------------------------


def induction(var: str, pred: Formula, base: Pf, step: Pf) -> Pf:
    """Build an induction proof term.

        base : |- pred[var := 0]
        step : |- pred -> pred[var := S(var)]
        ----------------------------------------
              |- pred

    Just the `Induct` node constructor; the checker enforces base/step shape and
    the side condition that `var` is not free in their hypotheses.
    """
    return Induct(var, pred, base, step)
