"""Rigidity of the positive integers, checked by the trusted `check()`.

The first genuine *induction* proof in `ROBINSON_PEANO` (base 1). We extend the
(1, S, ·) theory with a fresh unary `f` and the successor half of Wehrung's
brachymorphism laws -- `f(1) = 1` and `f(S x) = S(f x)` -- and derive `f(x) = x`
by the `Induct` rule. Every successor-preserving self-map of the positive
integers is the identity.

Then the bonus: given rigidity, the OTHER brachymorphism law `f(x·y) =
f(x)·f(y)` is a *theorem*, not an axiom -- over the positive integers,
preserving successor alone forces multiplicativity.

See papers/Wehrung_2024_AdditionDefinableMultiplicationSuccessor/notes.md.
"""

from __future__ import annotations

import pytest
from semantics import Model, evaluate

from cold_start.checker import check
from cold_start.proof import Induct
from cold_start.rigidity import (
    F_ONE,
    F_SUCC,
    MULTIPLICATIVE,
    RIGIDITY,
    ROBINSON_PEANO_F,
    f,
    multiplicative,
    rigidity,
)
from cold_start.robinson import ONE, ROBINSON_AXIOMS, ROBINSON_PEANO
from cold_start.syntax import Eq, Var
from cold_start.vocabulary import S, mul

_x, _y = Var("x"), Var("y")

# N over (1, S, ·) with `f` the identity -- the intended model of the extension.
N_ID = Model(
    "N+id",
    interp={"1": lambda: 1, "S": lambda v: v + 1, "*": lambda a, b: a * b, "f": lambda v: v},
)


# --- the theory extension is data, not a subclass --------------------------


def test_extension_adds_exactly_the_two_f_axioms():
    assert ROBINSON_PEANO_F.axioms == ROBINSON_AXIOMS | {F_ONE, F_SUCC}
    assert ROBINSON_PEANO.axioms == ROBINSON_AXIOMS  # the base theory is untouched


def test_extension_inherits_the_induction_structure_with_base_one():
    # The whole point: the induction base is 1, not 0. Robinson's domain is the
    # POSITIVE integers.
    assert ROBINSON_PEANO_F.zero == ONE
    assert ROBINSON_PEANO_F.succ == "S"


def test_the_f_axioms_are_the_successor_half_of_a_brachymorphism():
    # Wehrung's f(1+x) = 1+f(x), spelled with S and pinned at the base point.
    assert F_ONE == Eq(f(ONE), ONE)
    assert F_SUCC == Eq(f(S(_x)), S(f(_x)))


# --- deliverable 1: the induction proof ------------------------------------


def test_rigidity_checks_and_is_unconditional():
    # |- f(x) = x   in ROBINSON_PEANO + {f(1)=1, f(S x)=S(f x)}.
    seq = check(rigidity(), ROBINSON_PEANO_F)
    assert seq.hyps == frozenset()
    assert seq.concl == Eq(f(_x), _x)
    assert seq.concl == RIGIDITY


def test_rigidity_really_goes_through_the_induction_rule():
    # Not a rewrite chain dressed up: the top node is `Induct` on x, so the
    # checker's base-1 side conditions are the ones that had to be satisfied.
    pf = rigidity()
    assert type(pf) is Induct
    assert pf.var == "x"
    assert pf.pred == RIGIDITY


def test_rigidity_needs_the_f_axioms():
    # Without the two new axioms the same proof term is rejected -- the theory,
    # not the term, is what carries the mathematical commitment.
    with pytest.raises(ValueError):
        check(rigidity(), ROBINSON_PEANO)


# --- deliverable 1, bonus: multiplicativity is now a theorem ---------------


def test_multiplicativity_is_derived_from_rigidity():
    # |- f(x·y) = f(x)·f(y). The second brachymorphism law, PROVED rather than
    # assumed -- over the positive integers, successor-preservation forces it.
    seq = check(multiplicative(), ROBINSON_PEANO_F)
    assert seq.hyps == frozenset()
    assert seq.concl == MULTIPLICATIVE
    assert seq.concl == Eq(f(mul(_x, _y)), mul(f(_x), f(_y)))


# --- model soundness -------------------------------------------------------


@pytest.mark.parametrize("n", [1, 2, 3, 4, 5])
def test_f_axioms_hold_in_N_with_f_the_identity(n):
    assert evaluate(F_ONE, N_ID, {})
    assert evaluate(F_SUCC, N_ID, {"x": n})


@pytest.mark.parametrize("n", [1, 2, 3, 4, 5])
def test_the_checked_theorems_are_true_in_N(n):
    assert evaluate(RIGIDITY, N_ID, {"x": n})
    assert evaluate(MULTIPLICATIVE, N_ID, {"x": n, "y": n + 1})


def test_a_rogue_successor_preserving_map_violates_the_base_axiom():
    # f(n) = n+1 preserves successor but is not the identity -- and the model
    # shows exactly which axiom stops it: the base f(1) = 1. That is why the
    # theorem needs the induction BASE at 1, and why it is a rigidity statement.
    rogue = Model(
        "N+succ",
        interp={"1": lambda: 1, "S": lambda v: v + 1, "*": lambda a, b: a * b,
                "f": lambda v: v + 1},
    )
    assert evaluate(F_SUCC, rogue, {"x": 3})  # successor half: satisfied
    assert not evaluate(F_ONE, rogue, {})  # base: violated
    assert not evaluate(RIGIDITY, rogue, {"x": 3})
