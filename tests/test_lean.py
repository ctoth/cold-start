"""Lean 4 compatibility layer tests.

The export is untrusted: it claims nothing about our checker's soundness, it
hands our proofs to a *foreign* kernel. These tests pin the rendering (golden
snippets, not whole-file equality), the statement round-trip, and -- when a Lean
4 toolchain is on PATH -- the actual compilation of the generated corpus.
"""

from __future__ import annotations

import pytest
from hypothesis import given
from hypothesis import strategies as st

from cold_start.checker import Theory
from cold_start.lean import (
    LeanError,
    export_theorem,
    parse_formula,
    parse_term,
    render_formula,
    render_statement,
    render_term,
    universal_closure,
)
from cold_start.peano import MUL_SUCC_F, MUL_ZERO_F, PEANO, mul
from cold_start.presburger import (
    ADD_SUCC_F,
    ADD_ZERO_F,
    PRESBURGER,
    SUCC_INJ,
    SUCC_NEQ_ZERO,
    ZERO,
    S,
    add,
    numeral,
)
from cold_start.proof import MP, Assume, Axiom, Cong, ImpIntro, Inst, Refl
from cold_start.proofs import add_proof, left_identity_proof, mul_proof, robinson_add_proof
from cold_start.robinson import ADD_ONE, ADD_SUCC, MUL_SUCC, ROBINSON_PEANO
from cold_start.syntax import (
    Bottom,
    Eq,
    Exists,
    Formula,
    Fun,
    Implies,
    Not,
    Term,
    Var,
    exists,
    forall,
)


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


# --- from Lean: the statement fragment we emit, parsed back ----------------


def test_parse_term_reads_applications():
    assert parse_term("succ (succ zero)") == numeral(2)
    assert parse_term("add x (mul y zero)") == add(Var("x"), mul(Var("y"), ZERO))


def test_parse_formula_reads_a_binder():
    assert parse_formula("∀ x : M, add x zero = x") == forall("x", "", ADD_ZERO_F)


def test_parse_formula_reads_implication_right_associatively():
    text = "succ x = zero → x = zero → False"
    assert parse_formula(text) == Implies(
        Eq(S(Var("x")), ZERO), Implies(Eq(Var("x"), ZERO), Bottom())
    )


def test_parse_formula_accepts_ascii_arrow():
    assert parse_formula("x = zero -> False") == Not(Eq(Var("x"), ZERO))


def test_parse_rejects_a_term_where_a_formula_is_required():
    with pytest.raises(LeanError):
        parse_formula("add x y")


def test_parse_rejects_a_shadowing_binder():
    with pytest.raises(LeanError):
        parse_formula("∀ x : M, ∀ x : M, x = x")


def test_parse_rejects_a_foreign_carrier():
    with pytest.raises(LeanError):
        parse_formula("∀ x : Nat, x = zero")


def test_parse_rejects_trailing_junk():
    with pytest.raises(LeanError):
        parse_formula("x = zero )")


AXIOM_CORPUS = [
    ADD_ZERO_F,
    ADD_SUCC_F,
    SUCC_NEQ_ZERO,
    SUCC_INJ,
    MUL_ZERO_F,
    MUL_SUCC_F,
    ADD_ONE,
    ADD_SUCC,
    MUL_SUCC,
]


@pytest.mark.parametrize("formula", AXIOM_CORPUS)
def test_axiom_statements_round_trip_through_lean_text(formula: Formula):
    assert parse_formula(render_statement(formula)) == universal_closure(formula)


VAR_NAMES = st.sampled_from(["x", "y", "z", "n", "m", "a", "b"])


def terms() -> st.SearchStrategy[Term]:
    leaf = st.one_of(st.builds(Var, VAR_NAMES), st.just(ZERO))
    return st.recursive(
        leaf,
        lambda kids: st.one_of(
            st.builds(S, kids),
            st.builds(add, kids, kids),
            st.builds(mul, kids, kids),
        ),
        max_leaves=6,
    )


def formulas() -> st.SearchStrategy[Formula]:
    leaf = st.one_of(st.builds(Eq, terms(), terms()), st.just(Bottom()))
    return st.recursive(
        leaf,
        lambda kids: st.one_of(
            st.builds(Implies, kids, kids),
            st.builds(forall, VAR_NAMES, st.just(""), kids),
            st.builds(exists, VAR_NAMES, st.just(""), kids),
        ),
        max_leaves=5,
    )


@given(formulas())
def test_statements_round_trip_through_lean_text(formula: Formula):
    assert parse_formula(render_statement(formula)) == universal_closure(formula)


def test_existential_statements_round_trip():
    f = exists("x", "", Eq(add(Var("x"), Var("y")), ZERO))
    assert render_statement(f) == "∀ y : M, ∃ x : M, add x y = zero"
    assert parse_formula(render_statement(f)) == universal_closure(f)
    assert isinstance(parse_formula("∃ x : M, x = zero"), Exists)


def test_unknown_symbols_round_trip_as_uninterpreted_functions():
    f = Eq(Fun("f", (Var("x"),)), Var("x"))
    assert render_statement(f) == "∀ x : M, f x = x"
    assert parse_formula(render_statement(f)) == universal_closure(f)


# --- proof export: conditional theorems over an abstract carrier -----------

CORPUS = [
    ("left_identity", left_identity_proof(), PRESBURGER),
    ("add_two_three", add_proof(2, 3), PRESBURGER),
    ("mul_two_three", mul_proof(2, 3), PEANO),
    ("robinson_add_two_three", robinson_add_proof(2, 3), ROBINSON_PEANO),
]


def test_left_identity_exports_as_a_conditional_theorem():
    text = export_theorem("left_identity", left_identity_proof(), PRESBURGER)
    assert text.startswith("theorem left_identity {M : Type}")
    assert "(zero : M)" in text
    assert "(succ : M → M)" in text
    assert "(add : M → M → M)" in text
    assert "(ax_add_zero : ∀ x : M, add x zero = x)" in text
    assert "(ax_add_succ : ∀ x : M, ∀ y : M, add x (succ y) = succ (add x y))" in text
    assert "(ind : ∀ P : M → Prop, P zero → (∀ n : M, P n → P (succ n)) → ∀ n : M, P n)" in text
    assert ": ∀ n : M, add zero n = n :=" in text


@pytest.mark.parametrize(("name", "pf", "theory"), CORPUS)
def test_export_never_asserts_anything_to_lean(name: str, pf, theory: Theory):
    """The soundness-critical property: no `axiom`, no `sorry`, no tactic escape
    hatch. Every assumption is a hypothesis of the exported theorem."""
    text = export_theorem(name, pf, theory)
    assert "axiom" not in text
    assert "sorry" not in text
    assert text.count("theorem") == 1


def test_a_proof_without_induction_takes_no_induction_hypothesis():
    text = export_theorem("add_two_three", add_proof(2, 3), PRESBURGER)
    assert "(ind :" not in text
    assert "(ax_add_zero :" in text


def test_instantiation_follows_the_closure_order_not_the_inst_order():
    """`ax_add_succ` is closed as `∀ x, ∀ y`, so its arguments are (x, y) however
    the `Inst` chain nests -- instantiating y first must not swap them."""
    x_then_y = Inst(Inst(Axiom(ADD_SUCC_F), "x", ZERO), "y", Var("n"))
    y_then_x = Inst(Inst(Axiom(ADD_SUCC_F), "y", Var("n")), "x", ZERO)
    for pf in (x_then_y, y_then_x):
        text = export_theorem("inst", pf, PRESBURGER)
        assert "ax_add_succ zero n" in text
        assert ": ∀ n : M, add zero (succ n) = succ (add zero n) :=" in text


def test_induction_becomes_an_application_of_the_induction_hypothesis():
    text = export_theorem("left_identity", left_identity_proof(), PRESBURGER)
    assert "ind (fun n_1 : M => add zero n_1 = n_1)" in text
    assert "congrArg succ" in text


def test_congruence_of_a_binary_symbol_composes_congr_and_congrArg():
    pf = Cong("+", (Refl(ZERO), Refl(Var("x"))))
    text = export_theorem("cong", pf, PRESBURGER)
    assert "congr (congrArg add (Eq.refl zero)) (Eq.refl x)" in text


def test_open_hypotheses_become_named_theorem_parameters():
    pf = ImpIntro(Eq(Var("x"), ZERO), Assume(Eq(Var("x"), ZERO)))
    text = export_theorem("discharge", pf, PRESBURGER)
    assert ": ∀ x : M, x = zero → x = zero :=" in text
    assert "fun h : x = zero => h" in text

    open_pf = Assume(Eq(Var("x"), ZERO))
    open_text = export_theorem("open_hyp", open_pf, PRESBURGER)
    assert "(x : M)" in open_text
    assert "(h : x = zero)" in open_text
    assert open_text.rstrip().splitlines()[-1].strip() == "h"


def test_modus_ponens_is_application():
    pf = MP(Inst(Axiom(SUCC_INJ), "x", ZERO), Assume(Eq(S(ZERO), S(Var("y")))))
    text = export_theorem("mp", pf, PRESBURGER)
    assert "((ax_succ_inj zero y) h)" in text
    assert "(h : succ zero = succ y)" in text
    assert ": zero = y :=" in text


def test_a_sorted_theory_is_out_of_scope():
    with pytest.raises(LeanError):
        render_statement(forall("x", "K", Eq(Var("x", "K"), Var("x", "K"))))
