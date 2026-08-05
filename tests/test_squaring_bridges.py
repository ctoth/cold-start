"""B1: multiplication defined in addition arithmetic with a square function."""

from semantics import Model, evaluate

from cold_start.interp import verify
from cold_start.lean.proof import export_theorem
from cold_start.presburger import PRESBURGER, ZERO, S, add
from cold_start.squaring import (
    SQUARE_ARITHMETIC,
    SQUARE_SUCC_F,
    SQUARE_ZERO_F,
    sq,
)
from cold_start.squaring_bridges import square_product, squaring_interpretation
from cold_start.squaring_proofs import square_product_total
from cold_start.syntax import Fun, Var, children, subnodes


def _function_names(root: object) -> set[str]:
    names: set[str] = set()
    stack = [root]
    while stack:
        node = stack.pop()
        if isinstance(node, (tuple, list, set, frozenset)):
            stack.extend(node)
            continue
        if type(node) is Fun:
            names.add(node.name)
        stack.extend(children(node))
    return names


def test_square_arithmetic_is_presburger_plus_two_square_recursions() -> None:
    assert SQUARE_ARITHMETIC.zero == ZERO
    assert SQUARE_ARITHMETIC.succ == "S"
    assert SQUARE_ARITHMETIC.axioms - PRESBURGER.axioms == {
        SQUARE_ZERO_F,
        SQUARE_SUCC_F,
    }
    assert _function_names(SQUARE_ARITHMETIC.axioms) == {"0", "S", "+", "sq"}


def test_subtraction_free_graph_defines_standard_multiplication() -> None:
    model = Model(
        "bounded-naturals-with-square",
        {
            "0": lambda: 0,
            "S": lambda n: n + 1,
            "+": lambda a, b: a + b,
            "sq": lambda n: n * n,
        },
        carriers={"": tuple(range(32))},
    )
    x, y, z = Var("x"), Var("y"), Var("z")
    graph = square_product(x, y, z)
    for a in range(5):
        for b in range(5):
            for c in range(17):
                assert evaluate(graph, model, {"x": a, "y": b, "z": c}) == (c == a * b)


def test_squaring_bridge_is_fully_paid_and_measured() -> None:
    artifact = squaring_interpretation()
    report = verify(artifact)

    assert artifact.target is SQUARE_ARITHMETIC
    assert report.name == "multiplication-into-addition-and-square"
    assert report.complete
    assert report.open_labels() == ()
    assert {status.obligation.label for status in report.statuses} == {
        "totality:*",
        "uniqueness:*",
    }
    assert all(status.paid and status.toll > 0 for status in report.statuses)
    assert report.bridge_size == 14
    assert report.total_toll == 20_230


def test_graph_and_payments_never_smuggle_multiplication_or_subtraction() -> None:
    artifact = squaring_interpretation()
    graph = square_product(Var("x"), Var("y"), Var("z"))
    graph_names = {n.name for n in subnodes(graph) if type(n) is Fun}
    payment_names = set().union(
        *(_function_names(payment) for _label, payment in artifact.payments)
    )

    assert graph_names == {"+", "sq"}
    assert payment_names <= {"0", "S", "+", "sq"}
    assert "*" not in payment_names
    assert "-" not in payment_names


def test_square_recursions_have_the_standard_bounded_model() -> None:
    model = Model(
        "bounded-naturals-with-square",
        {
            "0": lambda: 0,
            "S": lambda n: n + 1,
            "+": lambda a, b: a + b,
            "sq": lambda n: n * n,
        },
        carriers={"": tuple(range(64))},
    )
    for n in range(12):
        env = {"x": n}
        assert evaluate(SQUARE_ZERO_F, model, env)
        assert evaluate(SQUARE_SUCC_F, model, env)
        assert evaluate(sq(add(S(ZERO), Var("x"))), model, env) == (n + 1) ** 2


def test_canonical_interpretation_names_export_without_double_quoting() -> None:
    text = export_theorem("square_total", square_product_total(), SQUARE_ARITHMETIC)
    assert "««" not in text
    assert "x!" not in text
