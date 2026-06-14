"""Explicit quantifiers, built red-first. Capture-avoiding substitution is the
bug-prone heart, so it goes first.
"""

from __future__ import annotations

import cold_start.proof as P
from cold_start.checker import check
from cold_start.peano import PEANO, ZERO, S
from cold_start.syntax import Eq, Forall, Var, formula_free_vars, formula_subst


def test_subst_into_forall_avoids_capture():
    # ∀y. (x = y); substitute the term `y` for `x`. Naive substitution captures
    # the incoming y, giving ∀y. (y = y) -- wrong. Capture-avoiding substitution
    # must alpha-rename the bound y so the substituted y stays FREE.
    f = Forall("y", "", Eq(Var("x"), Var("y")))
    result = formula_subst(f, "x", Var("y"))
    assert "y" in formula_free_vars(result), f"captured: {result!r}"


def test_forall_elim_instantiates():
    # Assume ∀x. (x = x); eliminate at t := S(0), giving S0 = S0.
    phi = Forall("x", "", Eq(Var("x"), Var("x")))
    seq = check(P.ForallElim(P.Assume(phi), S(ZERO)), PEANO)
    assert seq.concl == Eq(S(ZERO), S(ZERO))
    assert seq.hyps == frozenset({phi})


def test_forall_intro_generalizes():
    # From |- x = x (x free, schematic) conclude |- ∀x. x = x.
    seq = check(P.ForallIntro("x", "", P.Refl(Var("x"))), PEANO)
    assert seq.concl == Forall("x", "", Eq(Var("x"), Var("x")))
    assert seq.hyps == frozenset()


def test_forall_intro_rejects_free_eigenvariable():
    # Assuming x = 0, you cannot generalize x: {x=0} |- ∀x. x=0 is unsound.
    sub = P.Assume(Eq(Var("x"), ZERO))  # {x=0} |- x=0
    try:
        check(P.ForallIntro("x", "", sub), PEANO)
    except ValueError:
        return
    raise AssertionError("generalized a variable free in a hypothesis")
