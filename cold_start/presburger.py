"""Presburger arithmetic as a *theory*: the addition fragment of number theory.

Signature 0, S, + with the recursion axioms for addition, the two successor
axioms (0 is not a successor; successor is injective), and induction as a
first-class rule. This fragment -- no multiplication -- is **complete and
decidable**: Goedel's incompleteness does not apply. `cold_start.peano` extends
it with multiplication, which is where incompleteness begins.

The checker is theory-agnostic; this module supplies the arithmetic. Everything
trusted here is small and on the page. Induction is deliberately a rule, not an
axiom formula (see checker.Theory for why the schema-as-axiom is unsound).
"""

from __future__ import annotations

from . import vocabulary as _v
from .proof import Induct, Pf
from .syntax import Eq, Formula, Implies, Not, Var
from .theory import Signature, Theory

# --- signature: the shared arithmetic vocabulary --------------------------

# --- axioms (the trusted base) -------------------------------------------
# Recursive definition of addition. Free vars implicitly universally quantified.

ADD_ZERO_F: Formula = Eq(_v.add(Var("x"), _v.ZERO), Var("x"))  # x + 0 = x
ADD_SUCC_F: Formula = Eq(
    _v.add(Var("x"), _v.S(Var("y"))),
    _v.S(_v.add(Var("x"), Var("y"))),
)  # x + S y = S(x+y)

# The successor axioms that need negation: 0 is not a successor, and successor is
# injective. Together they make distinct numerals provably unequal -- retiring
# the model-only witness we used before `Not` existed.
SUCC_NEQ_ZERO: Formula = Not(Eq(_v.S(Var("x")), _v.ZERO))  # S x != 0
SUCC_INJ: Formula = Implies(
    Eq(_v.S(Var("x")), _v.S(Var("y"))), Eq(Var("x"), Var("y"))
)  # Sx=Sy -> x=y


# Induction is a *rule*, not an axiom (encoding the schema as an axiom formula
# is unsound here -- see checker.Theory). The theory just declares its zero and
# successor so the checker's Induct rule knows the recursion structure.
PRESBURGER_SIG = Signature(
    sorts=frozenset({""}),
    ranks=(("0", (), ""), ("S", ("",), ""), ("+", ("", ""), "")),
)

PRESBURGER = Theory(
    axioms=frozenset({ADD_ZERO_F, ADD_SUCC_F, SUCC_NEQ_ZERO, SUCC_INJ}),
    zero=_v.ZERO,
    succ="S",
    signature=PRESBURGER_SIG,
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
