"""Semantic model registrations for unconditional Lean cash-out."""

from dataclasses import replace

import pytest

import cold_start.lean.models as lean_models
from cold_start.lean.models import (
    NAT_PEANO,
    NAT_PRESBURGER,
    NAT_SQUARE,
    LeanModel,
    model_for,
)
from cold_start.peano import PEANO
from cold_start.presburger import PRESBURGER
from cold_start.robinson import ROBINSON_PEANO
from cold_start.squaring import SQUARE_ARITHMETIC
from cold_start.syntax import Eq, Fun
from cold_start.theory import Signature, Theory


def test_only_exact_registered_theories_cash_out() -> None:
    assert model_for(PRESBURGER) is NAT_PRESBURGER
    assert model_for(PEANO) is NAT_PEANO
    assert model_for(SQUARE_ARITHMETIC) is NAT_SQUARE
    assert model_for(ROBINSON_PEANO) is None
    assert model_for(replace(PRESBURGER)) is None
    assert model_for(Theory(axioms=frozenset())) is None


def test_model_symbol_inspection_deduplicates_shared_syntax(monkeypatch) -> None:
    shared = Fun("c", ())
    root = Fun("f", (shared, shared))
    theory = Theory(
        axioms=frozenset({Eq(root, root)}),
        signature=Signature(
            sorts=frozenset({""}),
            ranks=(("c", (), ""), ("f", ("", ""), "")),
        ),
    )
    visits: dict[int, int] = {}
    original_children = lean_models.children

    def counted_children(node: object):
        visits[id(node)] = visits.get(id(node), 0) + 1
        return original_children(node)

    monkeypatch.setattr(lean_models, "children", counted_children)
    assert lean_models._theory_symbols(theory) == {"c": 0, "f": 2}
    assert visits[id(shared)] == 1


def test_model_registration_requires_every_axiom_payment() -> None:
    with pytest.raises(ValueError, match="axiom proofs do not exactly cover"):
        LeanModel(
            name="broken-nat-presburger",
            theory=PRESBURGER,
            carrier="Nat",
            symbols=(("0", "Nat.zero"), ("S", "Nat.succ"), ("+", "Nat.add")),
            axiom_proofs=(),
            induction_proof="fun P h0 hs n => Nat.rec (motive := P) h0 hs n",
        )


def test_model_registration_rejects_duplicate_or_missing_operations() -> None:
    payments = NAT_PRESBURGER.axiom_proofs
    with pytest.raises(ValueError, match="duplicate model symbol"):
        LeanModel(
            name="duplicate-operation",
            theory=PRESBURGER,
            carrier="Nat",
            symbols=(("0", "Nat.zero"), ("0", "Nat.zero"), ("S", "Nat.succ"), ("+", "Nat.add")),
            axiom_proofs=payments,
            induction_proof=NAT_PRESBURGER.induction_proof,
        )

    with pytest.raises(ValueError, match="model symbols do not exactly cover"):
        LeanModel(
            name="missing-operation",
            theory=PRESBURGER,
            carrier="Nat",
            symbols=(("0", "Nat.zero"), ("S", "Nat.succ")),
            axiom_proofs=payments,
            induction_proof=NAT_PRESBURGER.induction_proof,
        )
