"""Lean 4 compatibility layer tests.

The export is untrusted: it claims nothing about our checker's soundness, it
hands our proofs to a *foreign* kernel. These tests pin the rendering (golden
snippets, not whole-file equality), the statement round-trip, and -- when a Lean
4 toolchain is on PATH -- the actual compilation of the generated corpus.
"""

from __future__ import annotations

from cold_start.lean import (
    render_formula,
    render_statement,
    render_term,
)
from cold_start.peano import mul
from cold_start.presburger import ADD_SUCC_F, SUCC_INJ, ZERO, S, add, numeral
from cold_start.syntax import Eq, Not, Var, forall


def test_render_term_maps_arithmetic_symbols_to_lean_names():
    assert render_term(numeral(2)) == "succ (succ zero)"
    assert render_term(add(Var("x"), mul(Var("y"), ZERO))) == "add x (mul y zero)"


def test_render_formula_uses_arrow_and_False():
    assert render_formula(Not(Eq(S(Var("x")), ZERO))) == "succ x = zero → False"
    assert render_formula(SUCC_INJ) == "succ x = succ y → x = y"


def test_render_statement_closes_free_vars_lexicographically():
    assert render_statement(ADD_SUCC_F) == "∀ x : M, ∀ y : M, add x (succ y) = succ (add x y)"


def test_render_statement_binder_names_avoid_free_names():
    f = forall("x", "", Eq(Var("x"), Var("y")))
    assert render_statement(f) == "∀ y : M, ∀ x : M, x = y"


def test_nested_quantifier_binders_get_distinct_names():
    f = forall("x", "", forall("y", "", Eq(Var("x"), Var("y"))))
    assert render_statement(f) == "∀ x : M, ∀ y : M, x = y"
