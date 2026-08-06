"""Checked elementary shore and explicit deep debts for Robinson Theorem 1.2."""

from __future__ import annotations

from semantics import Model, evaluate

from cold_start.divisibility_bridges import (
    DIVISIBILITY_CORE,
    PRODUCT_FROM_DIVIDES,
    PRODUCT_IN_POSITIVE_PEANO,
    divisibility_into_peano,
    robinson_product_interpretation,
    robinson_product_into_positive_peano,
)
from cold_start.interp import obligations, verify
from cold_start.peano import PEANO
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


def test_raw_product_graph_cannot_be_unique_over_the_axiomless_target():
    """A two-element target model makes the raw graph true at both results.

    This is executable evidence that ``uniqueness:*`` cannot be paid in the
    axiomless successor-divisibility theory.  Any complete theorem artifact
    must first interpret divisibility on a stronger shore.
    """
    total_divisibility = Model(
        "two elements with total divisibility",
        interp={"S": lambda value: value, "|": lambda _a, _b: True},
        carriers={"": (0, 1)},
    )
    uniqueness = next(
        obligation.formula
        for obligation in obligations(robinson_product_interpretation())
        if obligation.label == "uniqueness:*"
    )

    assert not evaluate(
        uniqueness,
        total_divisibility,
        {"x!0": 0, "x!1": 0, "c!": 0, "d!": 1},
    )


def test_robinson_product_has_a_proof_eligible_positive_peano_shore():
    artifact = robinson_product_into_positive_peano()
    report = verify(artifact)

    assert artifact.target is PEANO
    assert report.open_labels() == ("totality:*", "uniqueness:*")
    assert len(report.statuses) == 3
    assert report.statuses[-1].obligation.label == "domain:nonempty"
    assert report.statuses[-1].paid
    assert report.total_toll > 0
    assert report.bridge_size > 331

    nodes = tuple(subnodes(PRODUCT_IN_POSITIVE_PEANO.instance()))
    assert not any(type(node) is Rel for node in nodes)
    assert {node.name for node in nodes if type(node) is Fun} == {"S", "*"}


def test_measured_product_bridge_really_uses_only_successor_and_divisibility():
    graph = PRODUCT_FROM_DIVIDES.instance()
    nodes = tuple(subnodes(graph))

    assert {n.name for n in nodes if type(n) is Rel} == {"|"}
    assert {n.name for n in nodes if type(n) is Fun} == {"S"}
    assert not any(type(n) is Fun and n.name in {"+", "*"} for n in nodes)
