"""The untrusted prover half of the De Bruijn split.

`cold_start.tactics` may be arbitrarily clever -- nothing here is trusted. Every
proof term it emits is put in front of `check(_, PRESBURGER)`, which is the only
authority in the room. A tactic bug shows up as a rejected proof, never as a
false theorem.
"""

from __future__ import annotations

from cold_start.presburger import ZERO, S, add
from cold_start.syntax import Eq, Fun, Implies, Var
from cold_start.tactics import match

x, y, n = Var("x"), Var("y"), Var("n")


# --- first-order matching -------------------------------------------------


def test_match_binds_pattern_variables():
    assert match(add(x, ZERO), add(S(y), ZERO)) == {"x": S(y)}


def test_match_of_a_variable_pattern_binds_the_whole_target():
    assert match(x, add(y, ZERO)) == {"x": add(y, ZERO)}


def test_match_fails_on_a_different_function_symbol():
    assert match(add(x, ZERO), S(ZERO)) is None


def test_match_fails_on_a_different_arity():
    assert match(Fun("f", (x,)), Fun("f", (x, y))) is None


def test_match_requires_repeated_pattern_variables_to_agree():
    assert match(add(x, x), add(ZERO, S(ZERO))) is None
    assert match(add(x, x), add(S(ZERO), S(ZERO))) == {"x": S(ZERO)}


def test_variables_outside_the_pattern_set_match_literally():
    # The induction hypothesis is a *ground* rule: its `n` is a fixed
    # eigenvariable, not a hole. Passing an empty `vars` says exactly that.
    assert match(add(ZERO, n), add(ZERO, n), vars=frozenset()) == {}
    assert match(add(ZERO, n), add(ZERO, ZERO), vars=frozenset()) is None


def test_match_works_on_formulas_too():
    pattern = Implies(Eq(x, y), Eq(y, x))
    target = Implies(Eq(ZERO, S(ZERO)), Eq(S(ZERO), ZERO))
    assert match(pattern, target) == {"x": ZERO, "y": S(ZERO)}


def test_match_of_an_empty_pattern_set_is_structural_equality():
    assert match(add(x, y), add(x, y), vars=frozenset()) == {}
