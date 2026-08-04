"""Checked elementary shore and explicit deep debts for Robinson Theorem 1.2."""

from __future__ import annotations

from cold_start.divisibility_bridges import (
    DIVISIBILITY_CORE,
    PRODUCT_FROM_DIVIDES,
    divisibility_into_peano,
    robinson_product_interpretation,
)
from cold_start.interp import obligations, verify
from cold_start.syntax import Fun, Rel, subnodes


def test_elementary_divisibility_core_is_fully_paid_in_peano():
    report = verify(divisibility_into_peano())

    assert report.complete
    assert report.open_labels() == ()
    assert len(report.statuses) == len(DIVISIBILITY_CORE.axioms) == 7
    assert all(status.paid and status.toll > 0 for status in report.statuses)
    assert report.bridge_size == 6
    assert report.total_toll == 9_953


def test_robinson_product_graph_ledgers_exactly_the_deep_definedness_debts():
    artifact = robinson_product_interpretation()
    report = verify(artifact)

    assert not report.complete
    assert report.open_labels() == ("totality:*", "uniqueness:*")
    assert len(obligations(artifact)) == 2
    assert report.total_toll == 0
    assert report.bridge_size == 331


def test_measured_product_bridge_really_uses_only_successor_and_divisibility():
    graph = PRODUCT_FROM_DIVIDES.instance()
    nodes = tuple(subnodes(graph))

    assert {n.name for n in nodes if type(n) is Rel} == {"|"}
    assert {n.name for n in nodes if type(n) is Fun} == {"S"}
    assert not any(type(n) is Fun and n.name in {"+", "*"} for n in nodes)
