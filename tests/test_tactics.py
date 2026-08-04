"""The untrusted prover half of the De Bruijn split.

`cold_start.tactics` may be arbitrarily clever -- nothing here is trusted. Every
proof term it emits is put in front of `check(_, PRESBURGER)`, which is the only
authority in the room. A tactic bug shows up as a rejected proof, never as a
false theorem.
"""

from __future__ import annotations

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

import cold_start.tactics
from cold_start.checker import check
from cold_start.presburger import ADD_SUCC_F, ADD_ZERO_F, PRESBURGER, ZERO, S, add, numeral
from cold_start.proof import Axiom, Inst
from cold_start.proofs import (
    ADD_ASSOC,
    ADD_COMM,
    LEFT_IDENTITY,
    SUCC_ADD,
    add_assoc,
    add_comm,
    left_identity,
    left_identity_proof,
    succ_add,
)
from cold_start.syntax import Eq, Fun, Implies, Var
from cold_start.tactics import (
    TacticError,
    axiom_rule,
    by_induction,
    hypothesis_rule,
    match,
    normalize,
    prove_eq,
    rewrite_step,
)

ADD_RULES = (axiom_rule(ADD_ZERO_F), axiom_rule(ADD_SUCC_F))

x, y, z, n = Var("x"), Var("y"), Var("z"), Var("n")

TRUSTED_MODULES = ("syntax", "proof", "sequent", "checker")


# --- the boundary ---------------------------------------------------------


def _imports_tactics(module_name: str) -> bool:
    import ast
    import pathlib

    source = pathlib.Path(cold_start.tactics.__file__).with_name(f"{module_name}.py")
    tree = ast.parse(source.read_text(encoding="utf-8"))
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module == "tactics":
            return True
        if isinstance(node, ast.Import) and any("tactics" in a.name for a in node.names):
            return True
    return False


def test_the_trusted_core_does_not_import_the_tactics():
    """The split only means anything one way round. Tactics may read the whole
    trusted core; the trusted core must never depend on the prover, or a bug in
    this file would become a bug in the judge."""
    for name in TRUSTED_MODULES:
        assert not _imports_tactics(name), f"{name}.py imports the tactics"


def test_the_import_direction_check_can_actually_see_an_import():
    # proofs.py DOES use the tactics -- which is what makes the negative result
    # above evidence rather than a vacuous pass.
    assert _imports_tactics("proofs")


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


def test_firing_a_rule_yields_the_rewritten_term_and_its_proof_together():
    new, pf = axiom_rule(ADD_SUCC_F).fire({"x": ZERO, "y": n})
    assert new == S(add(ZERO, n))
    assert check(pf, PRESBURGER).concl == Eq(add(ZERO, S(n)), new)


def test_a_hypothesis_rule_is_ground_and_keeps_its_hypothesis():
    eq = Eq(add(ZERO, n), n)
    rule = hypothesis_rule(eq)
    assert rule.vars == frozenset()  # `n` is an eigenvariable, not a hole
    seq = check(rule.instance({}), PRESBURGER)
    assert seq.concl == eq
    assert seq.hyps == frozenset({eq})


# --- positional rewriting -------------------------------------------------


def test_rewrite_step_at_the_root():
    step = rewrite_step(add(x, ZERO), ADD_RULES)
    assert step is not None
    new, pf = step
    assert new == x
    assert check(pf, PRESBURGER).concl == Eq(add(x, ZERO), x)


def test_rewrite_step_under_a_congruence_tower():
    # the redex sits two constructors deep: S(S(x + 0))
    term = S(S(add(x, ZERO)))
    step = rewrite_step(term, ADD_RULES)
    assert step is not None
    new, pf = step
    assert new == S(S(x))
    seq = check(pf, PRESBURGER)
    assert seq.concl == Eq(term, S(S(x)))
    assert seq.hyps == frozenset()


def test_rewrite_step_keeps_untouched_siblings_by_reflexivity():
    term = add(add(y, ZERO), S(ZERO))  # the LEFT argument is the redex
    step = rewrite_step(term, (axiom_rule(ADD_ZERO_F),))
    assert step is not None
    new, pf = step
    assert new == add(y, S(ZERO))
    assert check(pf, PRESBURGER).concl == Eq(term, new)


def test_rewrite_step_is_leftmost_outermost():
    # (x + 0) + 0 has redexes at the root and inside. Outermost wins, so one
    # step yields x + 0, not (x) + 0 -- both are legal, we pick deterministically.
    step = rewrite_step(add(add(x, ZERO), ZERO), ADD_RULES)
    assert step is not None
    assert step[0] == add(x, ZERO)


def test_rewrite_step_returns_none_when_nothing_matches():
    assert rewrite_step(S(x), ADD_RULES) is None


def test_normalize_rewrites_to_a_fixpoint():
    term = add(add(add(x, ZERO), ZERO), ZERO)
    nf, pf = normalize(term, ADD_RULES)
    assert nf == x
    seq = check(pf, PRESBURGER)
    assert seq.concl == Eq(term, x)
    assert seq.hyps == frozenset()


def test_normalize_of_a_normal_form_is_reflexivity():
    nf, pf = normalize(S(x), ADD_RULES)
    assert nf == S(x)
    assert check(pf, PRESBURGER).concl == Eq(S(x), S(x))


def test_normalize_evaluates_closed_numeral_addition():
    nf, pf = normalize(add(numeral(2), numeral(3)), ADD_RULES)
    assert nf == numeral(5)
    assert check(pf, PRESBURGER).concl == Eq(add(numeral(2), numeral(3)), numeral(5))


def test_normalize_accepts_a_one_shot_iterable_of_rules():
    """`_find_redex` re-reads `rules` at every position it visits, so a
    generator would be exhausted after the first one and every later position
    would see an empty rule set -- normalize would return a NON-normal form
    with an honest proof of only the partial rewrite. The entry points
    materialize the rules once so the answer cannot depend on the container."""
    term = add(numeral(2), numeral(2))
    expected = normalize(term, ADD_RULES)[0]
    assert expected == numeral(4)
    nf, pf = normalize(term, (r for r in ADD_RULES))
    assert nf == expected
    assert check(pf, PRESBURGER).concl == Eq(term, expected)


def test_prove_eq_accepts_a_one_shot_iterable_of_rules():
    goal = Eq(add(numeral(2), numeral(2)), numeral(4))
    assert check(prove_eq(goal, (r for r in ADD_RULES)), PRESBURGER).concl == goal


def test_by_induction_accepts_a_one_shot_iterable_of_rules():
    pred = Eq(add(ZERO, n), n)
    seq = check(by_induction("n", pred, (r for r in ADD_RULES)), PRESBURGER)
    assert seq.concl == pred
    assert seq.hyps == frozenset()


def test_rewrite_step_accepts_a_one_shot_iterable_of_rules():
    # The redex is under a congruence, so the walk visits the root first and
    # only finds the rule at a later position -- exactly where exhaustion bites.
    term = S(add(x, ZERO))
    step = rewrite_step(term, (r for r in ADD_RULES))
    assert step is not None
    assert step[0] == S(x)


def test_normalize_raises_instead_of_hanging_on_a_looping_rule_set():
    looping = (axiom_rule(ADD_ZERO_F).flipped,)  # x -> x + 0, forever
    with pytest.raises(TacticError):
        normalize(x, looping, budget=8)


# --- prove_eq: join the two normal forms ----------------------------------


def test_prove_eq_joins_both_sides_through_their_normal_form():
    goal = Eq(add(add(x, ZERO), S(ZERO)), S(x))
    seq = check(prove_eq(goal, ADD_RULES), PRESBURGER)
    assert seq.concl == goal
    assert seq.hyps == frozenset()


def test_prove_eq_proves_a_goal_that_only_the_right_side_reduces():
    goal = Eq(S(x), S(add(x, ZERO)))
    assert check(prove_eq(goal, ADD_RULES), PRESBURGER).concl == goal


def test_prove_eq_names_both_normal_forms_when_they_differ():
    with pytest.raises(TacticError) as excinfo:
        prove_eq(Eq(add(x, ZERO), S(x)), ADD_RULES)
    message = str(excinfo.value)
    assert repr(x) in message
    assert repr(S(x)) in message


# --- by_induction ---------------------------------------------------------


def test_by_induction_proves_left_identity():
    pred = Eq(add(ZERO, n), n)
    seq = check(by_induction("n", pred, ADD_RULES), PRESBURGER)
    assert seq.concl == pred
    assert seq.hyps == frozenset()  # the IH was discharged by ImpIntro


def test_by_induction_discharges_the_hypothesis_it_assumed():
    # The eigenvariable side condition is the whole game: Induct rejects a proof
    # whose base or step leaves the induction variable free in a hypothesis. An
    # undischarged IH would do exactly that, so a checked result with empty hyps
    # is evidence the ImpIntro really fired.
    pred = Eq(add(ZERO, n), n)
    pf = by_induction("n", pred, ADD_RULES)
    assert check(pf, PRESBURGER).hyps == frozenset()


def test_by_induction_reports_the_offending_case():
    pred = Eq(add(ZERO, n), S(n))  # false, so the base case 0 + 0 = S(0) fails
    with pytest.raises(TacticError):
        by_induction("n", pred, ADD_RULES)


# --- the theorems, all four built by tactics and judged by check() --------


def test_left_identity_by_tactics_matches_the_hand_built_proof():
    seq = check(left_identity(), PRESBURGER)
    assert seq.concl == LEFT_IDENTITY == Eq(add(ZERO, n), n)
    assert seq.hyps == frozenset()
    assert seq == check(left_identity_proof(), PRESBURGER)


def test_successor_pushes_out_of_a_sum():
    seq = check(succ_add(), PRESBURGER)
    assert seq.concl == SUCC_ADD == Eq(add(S(x), y), S(add(x, y)))
    assert seq.hyps == frozenset()


def test_addition_is_commutative():
    seq = check(add_comm(), PRESBURGER)
    assert seq.concl == ADD_COMM == Eq(add(x, y), add(y, x))
    assert seq.hyps == frozenset()


def test_addition_is_associative():
    seq = check(add_assoc(), PRESBURGER)
    assert seq.concl == ADD_ASSOC == Eq(add(add(x, y), z), add(x, add(y, z)))
    assert seq.hyps == frozenset()


# --- the tactics agree with arithmetic, on generated input ----------------


@given(st.integers(0, 20), st.integers(0, 20))
@settings(deadline=None)
def test_prove_eq_computes_numeral_addition(a, b):
    """The engine reduces a closed sum with nothing but the two recursion
    axioms, and the checker agrees -- for every small a and b, not just the
    ones I thought to write down. Compare `proofs.add_proof`, which builds the
    same theorem by hand: here we only state it."""
    goal = Eq(add(numeral(a), numeral(b)), numeral(a + b))
    seq = check(prove_eq(goal, ADD_RULES), PRESBURGER)
    assert seq.concl == goal
    assert seq.hyps == frozenset()


@given(st.integers(0, 20), st.integers(0, 20))
@settings(deadline=None)
def test_a_false_sum_is_refused_rather_than_mis_proved(a, b):
    """The failure direction: the tactics never emit a proof of a false
    equation -- they raise. (And if they ever did emit one, `check` would be
    the one to say no.)"""
    with pytest.raises(TacticError):
        prove_eq(Eq(add(numeral(a), numeral(b)), numeral(a + b + 1)), ADD_RULES)
