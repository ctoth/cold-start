"""Explicit quantifiers, built red-first. Capture-avoiding substitution is the
bug-prone heart, so it goes first.
"""

from __future__ import annotations

import cold_start.proof as P
from cold_start.checker import check
from cold_start.peano import PEANO
from cold_start.presburger import SUCC_NEQ_ZERO, ZERO, S
from cold_start.syntax import (
    Eq,
    Not,
    Var,
    exists,
    forall,
)
from cold_start.theory import Theory


def test_alpha_equivalence_is_structural_equality():
    # ∀x. x = x  and  ∀y. y = y  are the SAME formula. With a locally-nameless
    # representation the bound name is gone, so this is literal `==` -- no fresh
    # names, no separate alpha-equivalence relation to remember.
    fa = forall("x", "", Eq(Var("x"), Var("x")))
    fb = forall("y", "", Eq(Var("y"), Var("y")))
    assert fa == fb


def test_subst_into_forall_avoids_capture():
    # ∀y. (x = y); substitute the term `y` for `x`. With named binders this is
    # the classic capture trap; locally-nameless makes it impossible -- the bound
    # variable is an index, so the substituted `y` stays FREE by construction.
    f = forall("y", "", Eq(Var("x"), Var("y")))
    result = f.subst("x", Var("y"))
    assert "y" in result.free_vars(), f"captured: {result!r}"


def test_forall_elim_instantiates():
    # Assume ∀x. (x = x); eliminate at t := S(0), giving S0 = S0.
    phi = forall("x", "", Eq(Var("x"), Var("x")))
    seq = check(P.ForallElim(P.Assume(phi), S(ZERO)), PEANO)
    assert seq.concl == Eq(S(ZERO), S(ZERO))
    assert seq.hyps == frozenset({phi})


def test_forall_intro_generalizes():
    # From |- x = x (x free, schematic) conclude |- ∀x. x = x.
    seq = check(P.ForallIntro("x", "", P.Refl(Var("x"))), PEANO)
    assert seq.concl == forall("x", "", Eq(Var("x"), Var("x")))
    assert seq.hyps == frozenset()


def test_forall_intro_rejects_free_eigenvariable():
    # Assuming x = 0, you cannot generalize x: {x=0} |- ∀x. x=0 is unsound.
    sub = P.Assume(Eq(Var("x"), ZERO))  # {x=0} |- x=0
    try:
        check(P.ForallIntro("x", "", sub), PEANO)
    except ValueError:
        return
    raise AssertionError("generalized a variable free in a hypothesis")


# --- existential quantifier ----------------------------------------------


def test_subst_into_exists_avoids_capture():
    f = exists("y", "", Eq(Var("x"), Var("y")))
    result = f.subst("x", Var("y"))
    assert "y" in result.free_vars(), f"captured: {result!r}"


def test_exists_intro_from_witness():
    # From S0 = S0, introduce ∃x. x = S0 with witness x := S0.
    claim = exists("x", "", Eq(Var("x"), S(ZERO)))
    seq = check(P.ExistsIntro(claim, S(ZERO), P.Refl(S(ZERO))), PEANO)
    assert seq.concl == claim
    assert seq.hyps == frozenset()


def test_quantifier_rules_remain_untyped_for_an_explicit_open_theory():
    theory = Theory(axioms=frozenset())
    universal = forall("x", "N", Eq(Var("x", "N"), Var("x", "N")))
    eliminated = check(P.ForallElim(P.Assume(universal), Var("z", "M")), theory)
    assert eliminated.concl == Eq(Var("z", "M"), Var("z", "M"))

    claim = exists("x", "N", Eq(Var("x", "N"), Var("x", "N")))
    introduced = check(P.ExistsIntro(claim, Var("z", "M"), P.Refl(Var("z", "M"))), theory)
    assert introduced.concl == claim


def test_exists_elim_proves_no_successor_is_zero():
    # |- not (exists x. S x = 0): assume one exists, instantiate with eigenvar w,
    # contradict S w != 0, discharge. The eigenvar w does not escape (phi = ⊥).
    ex = exists("x", "", Eq(S(Var("x")), ZERO))  # ∃x. S x = 0
    instance = Eq(S(Var("w")), ZERO)  # S w = 0
    contra = P.MP(P.Inst(P.Axiom(SUCC_NEQ_ZERO), "x", Var("w")), P.Assume(instance))
    elim = P.ExistsElim("w", P.Assume(ex), contra)  # {∃x.Sx=0} |- ⊥
    seq = check(P.ImpIntro(ex, elim), PEANO)
    assert seq.concl == Not(ex)
    assert seq.hyps == frozenset()


def test_exists_elim_rejects_eigenvariable_escape():
    # If the conclusion mentions the eigenvariable, elimination is unsound.
    ex = exists("x", "", Eq(Var("x"), ZERO))  # ∃x. x = 0
    sub_use = P.Assume(Eq(Var("w"), ZERO))  # {w=0} |- w=0  -- concl mentions w
    bad = P.ExistsElim("w", P.Assume(ex), sub_use)
    try:
        check(bad, PEANO)
    except ValueError:
        return
    raise AssertionError("eigenvariable escaped into the conclusion")


# --- coverage gaps found by pytest-cov: soundness branches with no test ----


def test_exists_elim_rejects_eigenvariable_in_remaining_hypothesis():
    # The eigenvariable must not escape into a *remaining* hypothesis either.
    # Here the using proof derives ⊥ from {w=0, ¬(w=0)}; discharging the instance
    # (w=0) leaves ¬(w=0), which still mentions w -- so elimination must be refused.
    ex = exists("x", "", Eq(Var("x"), ZERO))  # ∃x. x = 0
    instance = Eq(Var("w"), ZERO)  # w = 0
    not_instance = Not(instance)  # (w=0) -> ⊥, mentions w
    sub_use = P.MP(P.Assume(not_instance), P.Assume(instance))  # {w=0, ¬(w=0)} |- ⊥
    bad = P.ExistsElim("w", P.Assume(ex), sub_use)
    try:
        check(bad, PEANO)
    except ValueError:
        return
    raise AssertionError("eigenvariable free in a remaining hypothesis was allowed")


def test_forall_elim_through_implication_and_bottom():
    # ∀x. ¬(x = 0); eliminate at S(0) -> ¬(S0 = 0). The body is Implies(.., ⊥), so
    # this exercises `instantiate` recursing through both connectives (untested
    # binder-open paths until now).
    phi = forall("x", "", Not(Eq(Var("x"), ZERO)))
    seq = check(P.ForallElim(P.Assume(phi), S(ZERO)), PEANO)
    assert seq.concl == Not(Eq(S(ZERO), ZERO))
    assert seq.hyps == frozenset({phi})


def test_exists_intro_rejects_non_existential_claim():
    bad = P.ExistsIntro(Eq(ZERO, ZERO), ZERO, P.Refl(ZERO))  # claim is not an Exists
    try:
        check(bad, PEANO)
    except ValueError:
        return
    raise AssertionError("exists-intro accepted a non-existential claim")


def test_exists_elim_rejects_non_existential():
    bad = P.ExistsElim("w", P.Refl(ZERO), P.Assume(Eq(Var("w"), ZERO)))  # sub_ex not ∃
    try:
        check(bad, PEANO)
    except ValueError:
        return
    raise AssertionError("exists-elim accepted a non-existential premise")


def test_exists_elim_rejects_missing_instance():
    ex = exists("x", "", Eq(Var("x"), ZERO))
    bad = P.ExistsElim("w", P.Assume(ex), P.Refl(ZERO))  # using proof never assumes w=0
    try:
        check(bad, PEANO)
    except ValueError:
        return
    raise AssertionError("exists-elim accepted a using-proof missing the instance")
