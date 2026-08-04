"""The ring of integers, interpreted into Peano arithmetic.

Wave 7 of the bridge workstream: the same Grothendieck pairs that carried
ℤ's abelian group into Presburger now carry the FULL commutative ring into
PEANO. Multiplication of differences is the difference product

    (a1, a2) * (b1, b2)  =  (a1*b1 + a2*b2,  a1*b2 + a2*b1)

and 1 is any pair one step above the diagonal. Every obligation -- the three
equivalence laws, totality and respect for all five symbols, and the ten
translated ring axioms -- must be paid in PEANO.
"""

from __future__ import annotations

import pytest
from semantics import Model, evaluate

from cold_start.algebra import COMM, COMM_RING, MUL_ASSOC, RING_AXIOMS
from cold_start.quotient import vec, verify
from cold_start.ring_z import ring_z_interpretation

_MODEL = Model(
    "N",
    {
        "+": lambda a, b: a + b,
        "*": lambda a, b: a * b,
        "S": lambda a: a + 1,
    },
)


def test_comm_ring_is_the_eleven_axiom_theory() -> None:
    assert COMM_RING.axioms == RING_AXIOMS | {COMM}
    assert len(COMM_RING.axioms) == 10


def test_the_difference_product_models_integer_multiplication() -> None:
    # graph((a, b), c) holds in the standard model iff (a1-a2)(b1-b2) = c1-c2.
    interp = ring_z_interpretation()
    graphs = {s.fun: s for s in interp.symbols}
    a, b, c = vec("a", 2), vec("b", 2), vec("c", 2)
    mul_graph = graphs["*"].graph((a, b), c)
    for a1, a2, b1, b2 in [
        (a1, a2, b1, b2) for a1 in range(3) for a2 in range(3) for b1 in range(3) for b2 in range(3)
    ]:
        for c1, c2 in [(0, 0), (1, 3), (4, 0), (2, 2)]:
            env = {"a.1": a1, "a.2": a2, "b.1": b1, "b.2": b2, "c.1": c1, "c.2": c2}
            expected = (a1 - a2) * (b1 - b2) == c1 - c2
            assert evaluate(mul_graph, _MODEL, env) == expected


def test_one_models_the_integer_one() -> None:
    interp = ring_z_interpretation()
    one_graph = {s.fun: s for s in interp.symbols}["1"].graph((), vec("c", 2))
    for c1 in range(4):
        for c2 in range(4):
            env = {"c.1": c1, "c.2": c2}
            assert evaluate(one_graph, _MODEL, env) == (c1 - c2 == 1)


@pytest.fixture(scope="module")
def report():
    return verify(ring_z_interpretation())


def test_the_ring_bridge_is_complete(report) -> None:
    assert report.complete
    assert report.open_labels() == ()
    # 3 equivalence laws + (totality + respect) for 0, 1, +, neg, * + 10 axioms.
    assert len(report.statuses) == 23
    assert report.bridge_size > 0
    assert report.total_toll > 0


def test_multiplicative_laws_are_paid_theorems(report) -> None:
    # Commutativity and associativity of `*` -- paid in a theory of naturals.
    status = {s.obligation.label: s for s in report.statuses}
    assert status[f"axiom:{COMM!r}"].paid
    assert status[f"axiom:{MUL_ASSOC!r}"].paid
    assert status["respect:*"].paid and status["respect:*"].toll > 0
