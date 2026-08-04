"""The derived propositional kit: conjunction over the →/⊥ core.

The object language deliberately has no And node -- `prop.And` is the classical
encoding ¬(A → ¬B), and the combinators derive its introduction and both
eliminations as proof terms. Introduction is intuitionistic; the eliminations
are where RAA earns its keep. Everything is judged by the trusted checker."""

from __future__ import annotations

from cold_start.checker import check
from cold_start.presburger import PRESBURGER, ZERO, S
from cold_start.proof import Assume, ImpIntro, Refl
from cold_start.prop import And, Or, and_intro, and_left, and_right, or_elim, or_left, or_right
from cold_start.syntax import Eq, Implies, Not, Var

_x, _y = Var("x"), Var("y")
A = Eq(_x, _x)
B = Eq(S(_y), S(_y))


def test_and_is_the_classical_encoding() -> None:
    assert And(A, B) == Not(Implies(A, Not(B)))


def test_and_intro_packs_two_theorems() -> None:
    seq = check(and_intro(A, B, Refl(_x), Refl(S(_y))), PRESBURGER)
    assert not seq.hyps
    assert seq.concl == And(A, B)


def test_and_left_and_right_unpack() -> None:
    packed = and_intro(A, B, Refl(_x), Refl(S(_y)))
    left = check(and_left(A, B, packed), PRESBURGER)
    right = check(and_right(A, B, packed), PRESBURGER)
    assert not left.hyps and left.concl == A
    assert not right.hyps and right.concl == B


def test_and_carries_hypotheses_honestly() -> None:
    # Packing assumptions keeps them in the sequent: nothing is smuggled.
    ha, hb = Eq(_x, ZERO), Eq(_y, ZERO)
    seq = check(and_intro(ha, hb, Assume(ha), Assume(hb)), PRESBURGER)
    assert seq.hyps == frozenset({ha, hb})
    assert seq.concl == And(ha, hb)


def test_eliminations_recover_an_assumed_conjunction() -> None:
    packed = Assume(And(A, B))
    left = check(and_left(A, B, packed), PRESBURGER)
    assert left.hyps == frozenset({And(A, B)})
    assert left.concl == A


def test_or_is_the_classical_encoding() -> None:
    assert Or(A, B) == Implies(Not(A), B)


def test_or_left_and_right_inject_a_theorem() -> None:
    left = check(or_left(A, B, Refl(_x)), PRESBURGER)
    right = check(or_right(A, B, Refl(S(_y))), PRESBURGER)
    assert not left.hyps and left.concl == Or(A, B)
    assert not right.hyps and right.concl == Or(A, B)


def test_or_injections_carry_hypotheses_honestly() -> None:
    ha = Eq(_x, ZERO)
    seq = check(or_left(ha, B, Assume(ha)), PRESBURGER)
    assert seq.hyps == frozenset({ha})
    assert seq.concl == Or(ha, B)


def test_or_elim_reasons_by_cases() -> None:
    # From an assumed disjunction and one proof of C per arm, conclude C.
    goal = Eq(ZERO, ZERO)
    packed = Assume(Or(A, B))
    by_cases = or_elim(
        A,
        B,
        goal,
        packed,
        ImpIntro(A, Refl(ZERO)),
        ImpIntro(B, Refl(ZERO)),
    )
    seq = check(by_cases, PRESBURGER)
    assert seq.hyps == frozenset({Or(A, B)})
    assert seq.concl == goal
