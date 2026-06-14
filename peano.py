"""Peano arithmetic as a *theory*: a signature plus axioms (and one schema).

The checker is theory-agnostic; this module supplies what makes it arithmetic.
Everything trusted here is small and on the page: two addition axioms and the
induction-schema recognizer. Defining what counts as an axiom is inherently
part of choosing a theory, so the recognizer is trusted -- and short.
"""

from __future__ import annotations

from checker import Theory
from proof import MP, Axiom, Pf
from syntax import (
    Eq,
    Formula,
    Fun,
    Implies,
    Term,
    Var,
    formula_free_vars,
    formula_subst,
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


def is_induction_instance(f: Formula) -> bool:
    """True iff `f` is an instance of the induction schema

        P[x:=0] -> ( (P -> P[x:=S x]) -> P )

    for some predicate P and induction variable x. We recover P as the final
    consequent, then search the free variables of P for an x that makes the
    antecedent and the step match. The check is structural and total.
    """
    if not isinstance(f, Implies):
        return False
    base = f.ant
    rest = f.con
    if not isinstance(rest, Implies):
        return False
    step = rest.ant  # expected: Implies(P, P[x:=S x])
    pred = rest.con  # expected: P
    if not isinstance(step, Implies) or step.ant != pred:
        return False
    succ_case = step.con  # expected: P[x:=S x]
    for x in formula_free_vars(pred):
        if formula_subst(pred, x, ZERO) == base and formula_subst(pred, x, S(Var(x))) == succ_case:
            return True
    # Degenerate: induction variable not free in P (vacuous but valid).
    return base == pred and succ_case == pred


PEANO = Theory(
    axioms=frozenset({ADD_ZERO_F, ADD_SUCC_F}),
    schemas=(is_induction_instance,),
)


# --- derived inference: induction ----------------------------------------


def induction(var: str, pred: Formula, base: Pf, step: Pf) -> Pf:
    """Build a proof term for induction on `var` over `pred`.

        base : |- pred[var := 0]
        step : |- pred -> pred[var := S(var)]
        ----------------------------------------
              |- pred

    It cites the induction-schema axiom (accepted by PEANO via
    is_induction_instance) and discharges it with two modus-ponens steps. The
    checker re-validates that `base` and `step` are exactly the right shape.
    """
    pred_zero = formula_subst(pred, var, ZERO)
    pred_succ = formula_subst(pred, var, S(Var(var)))
    schema = Implies(pred_zero, Implies(Implies(pred, pred_succ), pred))
    return MP(MP(Axiom(schema), base), step)
