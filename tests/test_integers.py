"""The Grothendieck bridge: the integers, built inside Presburger arithmetic.

A pair (a, b) of naturals denotes the integer a - b; two pairs are the same
integer when a + d = c + b. Over that defined equivalence the theory of
abelian groups -- WITH its inverse axiom, which the naturals themselves
refuse -- interprets into plain Presburger arithmetic, every obligation paid.
Subtraction is spoken here without ever existing in the target.
"""

from __future__ import annotations

import pytest
from semantics import Model, evaluate

from cold_start.algebra import AB_GROUP, ADD_ASSOC, ADD_COMM, ADD_NEG, ADD_ZERO
from cold_start.integers import int_eq, integers_interpretation
from cold_start.quotient import vec, verify
from cold_start.syntax import Var


def test_ab_group_is_the_four_axiom_theory() -> None:
    assert AB_GROUP.axioms == frozenset({ADD_ASSOC, ADD_COMM, ADD_ZERO, ADD_NEG})


def test_int_eq_models_integer_equality() -> None:
    # (a, b) ~ (c, d) in the standard model iff a - b == c - d.
    model = Model("N", {"+": lambda a, b: a + b})
    formula = int_eq(vec("p", 2), vec("q", 2))
    for a in range(4):
        for b in range(4):
            for c in range(4):
                for d in range(4):
                    env = {"p.1": a, "p.2": b, "q.1": c, "q.2": d}
                    assert evaluate(formula, model, env) == (a - b == c - d)


@pytest.fixture(scope="module")
def report():
    return verify(integers_interpretation())


def test_integers_bridge_is_complete(report) -> None:
    assert report.complete
    assert report.open_labels() == ()
    # 3 equivalence laws + (totality + respect) for 0, +, neg + 4 axioms.
    assert len(report.statuses) == 13
    assert report.bridge_size > 0
    assert report.total_toll > 0


def test_the_inverse_axiom_is_a_paid_theorem(report) -> None:
    # x + (-x) = 0 -- the axiom the naturals refuse -- is paid, not open.
    status = {s.obligation.label: s for s in report.statuses}[f"axiom:{ADD_NEG!r}"]
    assert status.paid and status.toll > 0


def test_neg_is_the_swap_and_zero_is_the_diagonal() -> None:
    # Semantic sanity for the graphs at concrete pairs: the interpretation's
    # own symbols, evaluated in the standard model, compute integer negation
    # and zero.
    interp = integers_interpretation()
    model = Model("N", {"+": lambda a, b: a + b})
    graphs = {s.fun: s for s in interp.symbols}
    a = vec("a", 2)
    c = vec("c", 2)
    neg_graph = graphs["neg"].graph((a,), c)
    zero_graph = graphs["0"].graph((), c)
    for a1 in range(3):
        for a2 in range(3):
            for c1 in range(3):
                for c2 in range(3):
                    env = {"a.1": a1, "a.2": a2, "c.1": c1, "c.2": c2}
                    assert evaluate(neg_graph, model, env) == (-(a1 - a2) == c1 - c2)
                    assert evaluate(zero_graph, model, env) == (c1 - c2 == 0)


def test_var_component_naming_stays_disjoint_from_source_names() -> None:
    # The components of the source variable "x" are fresh target variables,
    # never the bare source name itself.
    assert vec("x", 2) == (Var("x.1"), Var("x.2"))
