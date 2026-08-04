"""The first checked bridge: base-1 Presburger interpreted in (1, S, ·).

`bridge_total` is the repo's FIRST existential theorem -- `∃c bridge(a,b,c)`,
derived inside ROBINSON_PEANO by induction based at 1 (A4' supplies the witness
S(a); A5' steps it). `robinson_interpretation` then assembles the artifact:
every translated source axiom is paid, totality is paid by that new theorem,
and uniqueness is honestly ledgered OPEN -- deriving it needs a multiplication
ladder rebuilt on the far shore, which is a campaign of its own.
"""

from __future__ import annotations

from cold_start.bridges import (
    PRESBURGER_ONE,
    bridge_total,
    robinson_interpretation,
)
from cold_start.checker import check
from cold_start.interp import verify
from cold_start.presburger import S, add
from cold_start.robinson import ONE, ROBINSON_PEANO, bridge
from cold_start.syntax import Eq, Var, exists

_a, _b = Var("a"), Var("b")


def test_presburger_one_is_the_base_one_addition_theory() -> None:
    assert PRESBURGER_ONE.zero == ONE
    assert PRESBURGER_ONE.succ == "S"
    assert Eq(add(_a, ONE), S(_a)) in PRESBURGER_ONE.axioms
    assert Eq(add(_a, S(_b)), S(add(_a, _b))) in PRESBURGER_ONE.axioms


def test_bridge_total_is_a_robinson_peano_theorem() -> None:
    # ∃c bridge(a,b,c): addition is TOTAL on the far shore -- the repo's first
    # existential theorem, and it lives in the (1, S, ·) theory, not at home.
    seq = check(bridge_total(), ROBINSON_PEANO)
    assert not seq.hyps
    assert seq.concl == exists("c", "", bridge(_a, _b, Var("c")))


def test_robinson_bridge_report() -> None:
    report = verify(robinson_interpretation())
    by_label = {s.obligation.label: s for s in report.statuses}

    # Every translated source axiom is paid.
    axiom_statuses = [s for label, s in by_label.items() if label.startswith("axiom:")]
    assert len(axiom_statuses) == len(PRESBURGER_ONE.axioms) == 4
    assert all(s.paid for s in axiom_statuses)

    # Totality is paid by the new existential theorem; uniqueness is the one
    # honest open debt.
    assert by_label["totality:+"].paid
    assert report.open_labels() == ("uniqueness:+",)
    assert not report.complete

    # The bridge itself: Robinson's whole identity is 19 nodes. That number is
    # the aesthetic headline -- all of addition crosses on 19 nodes of S and ·.
    assert report.bridge_size == 19
    assert report.total_toll > 0


def test_robinson_into_peano_positives_is_fully_paid() -> None:
    # The same 19-node bridge landing in PEANO relativized to the positives:
    # EVERY obligation paid -- uniqueness by last wave's converse theorem, the
    # recursion axiom by guarded A5', totality by the bridge theorem. No open
    # ledger: base-1 Presburger is interpreted in PEANO's positive domain.
    from cold_start.bridges import robinson_into_peano

    report = verify(robinson_into_peano())
    assert report.complete
    assert report.open_labels() == ()
    assert report.bridge_size == 19
    assert len(report.statuses) == 9  # 4 axioms + 2 definedness + 3 domain debts
    assert all(s.paid for s in report.statuses)
