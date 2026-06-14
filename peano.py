"""Peano arithmetic, built on top of the signature-agnostic kernel.

The kernel knows nothing about numbers. Here we choose a signature -- zero and
successor -- and assert the Peano axioms through the kernel's `axiom` door.
Those axioms, together with the kernel's inference rules, are the entire
trusted base. We keep them few and visible.

Induction is *derived*, not a kernel primitive: it is two modus-ponens steps
against an induction-schema axiom (one schema instance per predicate). That
keeps the kernel free of any commitment to the naturals.
"""

from __future__ import annotations

import kernel as k
from kernel import Eq, Fun, Implies, Term, Var

# --- signature ------------------------------------------------------------

ZERO = Fun("0", ())


def S(t: Term) -> Term:
    """Successor."""
    return Fun("S", (t,))


def add(a: Term, b: Term) -> Term:
    return Fun("+", (a, b))


def numeral(n: int) -> Term:
    """Build the closed term S(S(...0...)) for a concrete natural n."""
    if n < 0:
        raise ValueError("naturals only")
    t: Term = ZERO
    for _ in range(n):
        t = S(t)
    return t


# --- axioms (the trusted base) -------------------------------------------
# Recursive definition of addition. These two are all we need to compute with
# `+` and to prove its laws. Free variables are implicitly universally
# quantified (kernel convention).

#   x + 0 = x
ADD_ZERO = k.axiom(Eq(add(Var("x"), ZERO), Var("x")))

#   x + S(y) = S(x + y)
ADD_SUCC = k.axiom(Eq(add(Var("x"), S(Var("y"))), S(add(Var("x"), Var("y")))))

# (Successor injectivity, zero-is-not-a-successor, etc. come later -- they need
#  Not, which v0's logic does not have yet. See README.)


def induction(var: str, pred: k.Formula, base: k.Theorem, step: k.Theorem) -> k.Theorem:
    """Mathematical induction on `var` over the predicate `pred`.

    Given
        base : |- pred[var := 0]
        step : |- pred -> pred[var := S(var)]
    derive
        |- pred

    Implemented as the induction-schema axiom

        pred[0] -> ( (pred -> pred[S var]) -> pred )

    followed by two modus-ponens steps. The kernel's `mp` checks that `base`
    and `step` are exactly the antecedents the schema demands, so this is the
    only place the schema is trusted -- everything else is checked.
    """
    pred_zero = k.formula_subst(pred, var, ZERO)
    pred_succ = k.formula_subst(pred, var, S(Var(var)))
    schema = k.axiom(Implies(pred_zero, Implies(Implies(pred, pred_succ), pred)))
    after_base = k.mp(schema, base)  # |- (pred -> pred[S var]) -> pred
    return k.mp(after_base, step)  # |- pred
