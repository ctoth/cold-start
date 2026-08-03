"""The untrusted prover half of the De Bruijn split.

`cold_start.tactics` may be arbitrarily clever -- nothing here is trusted. Every
proof term it emits is put in front of `check(_, PRESBURGER)`, which is the only
authority in the room. A tactic bug shows up as a rejected proof, never as a
false theorem.
"""

from __future__ import annotations

from cold_start.checker import check
from cold_start.presburger import ADD_SUCC_F, ADD_ZERO_F, PRESBURGER, ZERO, S, add
from cold_start.proof import Axiom, Inst
from cold_start.syntax import Eq, Fun, Implies, Var
from cold_start.tactics import axiom_rule, hypothesis_rule, match

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


# --- rules: a directed equation plus the Pf that justifies it -------------


def test_a_naive_inst_chain_captures():
    """Pinning the trusted API's behaviour before building on it. `Inst` is a
    *sequential* substitution, so instantiating x := y and then y := 0 rewrites
    the y that the first step just introduced. Rule.instance must not do this."""
    naive = Inst(Inst(Axiom(ADD_SUCC_F), "x", y), "y", ZERO)
    assert check(naive, PRESBURGER).concl == Eq(add(ZERO, S(ZERO)), S(add(ZERO, ZERO)))


def test_rule_instance_is_simultaneous_and_capture_free():
    rule = axiom_rule(ADD_SUCC_F)
    pf = rule.instance({"x": y, "y": ZERO})
    seq = check(pf, PRESBURGER)
    assert seq.hyps == frozenset()
    assert seq.concl == Eq(add(y, S(ZERO)), S(add(y, ZERO)))


def test_axiom_rule_instance_checks_against_the_theory():
    rule = axiom_rule(ADD_ZERO_F)
    assert rule.lhs == add(x, ZERO)
    assert rule.rhs == x
    seq = check(rule.instance({"x": S(ZERO)}), PRESBURGER)
    assert seq == check(Inst(Axiom(ADD_ZERO_F), "x", S(ZERO)), PRESBURGER)


def test_a_flipped_rule_runs_the_equation_right_to_left():
    rule = axiom_rule(ADD_ZERO_F).flipped
    assert rule.lhs == x
    assert rule.rhs == add(x, ZERO)
    seq = check(rule.instance({"x": ZERO}), PRESBURGER)
    assert seq.concl == Eq(ZERO, add(ZERO, ZERO))
    assert seq.hyps == frozenset()


def test_a_hypothesis_rule_is_ground_and_keeps_its_hypothesis():
    eq = Eq(add(ZERO, n), n)
    rule = hypothesis_rule(eq)
    assert rule.vars == frozenset()  # `n` is an eigenvariable, not a hole
    seq = check(rule.instance({}), PRESBURGER)
    assert seq.concl == eq
    assert seq.hyps == frozenset({eq})
