"""Robinson's Theorem 1.2, transcribed from the rendered primary-source pages."""

from __future__ import annotations

from itertools import product

from semantics import Model, evaluate

from cold_start.notation import format_formula
from cold_start.prop import And, Iff, Or
from cold_start.robinson_divisibility import (
    coprime,
    divides,
    lcm,
    robinson_product,
    unit_case,
)
from cold_start.syntax import (
    Bottom,
    Eq,
    Formula,
    Fun,
    Implies,
    Not,
    Rel,
    Var,
    forall,
    subnodes,
    validate,
)
from cold_start.vocabulary import S


def truth(value: bool) -> Formula:
    return Not(Bottom()) if value else Bottom()


def test_classical_connective_sugar_has_the_expected_truth_tables():
    model = Model("propositional", interp={})

    for a, b in product((False, True), repeat=2):
        assert evaluate(And(truth(a), truth(b)), model, {}) is (a and b)
        assert evaluate(Or(truth(a), truth(b)), model, {}) is (a or b)
        assert evaluate(Iff(truth(a), truth(b)), model, {}) is (a == b)


def test_connective_sugar_expands_only_to_the_existing_logic_core():
    a, b = Eq(Var("a"), Var("a")), Eq(Var("b"), Var("b"))

    assert And(a, b) == Not(Implies(a, Not(b)))
    assert Or(a, b) == Implies(Not(a), b)
    assert Iff(a, b) == And(Implies(a, b), Implies(b, a))


def test_divisibility_coprimality_and_lcm_match_robinsons_definitions():
    a, b, c = Var("a"), Var("b"), Var("c")
    d, y, x = Var("d"), Var("y"), Var("x")

    assert divides(a, b) == Rel("|", (a, b))
    assert coprime(a, b) == forall(
        "d",
        "",
        Implies(
            And(divides(d, a), divides(d, b)),
            forall("y", "", divides(d, y)),
        ),
    )
    assert lcm(a, b, c) == forall(
        "x",
        "",
        Iff(And(divides(a, x), divides(b, x)), divides(c, x)),
    )


def test_definition_binders_are_hygienic_for_adversarial_free_names():
    formula = And(coprime(Var("d"), Var("y")), lcm(Var("x"), Var("d"), Var("y")))

    assert formula.free_vars() == frozenset({"d", "y", "x"})


def test_source_abbreviations_have_their_standard_positive_integer_semantics():
    carrier = tuple(range(1, 61))
    positive = Model(
        "positive integers",
        interp={"|": lambda a, b: b % a == 0},
        carriers={"": carrier},
    )
    a, b, c = Var("a"), Var("b"), Var("c")

    assert evaluate(coprime(a, b), positive, {"a": 8, "b": 9})
    assert not evaluate(coprime(a, b), positive, {"a": 8, "b": 12})
    assert evaluate(lcm(a, b, c), positive, {"a": 4, "b": 6, "c": 12})
    assert not evaluate(lcm(a, b, c), positive, {"a": 4, "b": 6, "c": 24})
    assert evaluate(unit_case(a, b, c), positive, {"a": 1, "b": 1, "c": 1})
    assert not evaluate(unit_case(a, b, c), positive, {"a": 1, "b": 2, "c": 1})


def test_robinson_product_is_an_honest_successor_divisibility_formula():
    formula = robinson_product(Var("a"), Var("b"), Var("c"))
    nodes = tuple(subnodes(formula))

    validate(formula)
    assert formula.free_vars() == frozenset({"a", "b", "c"})
    assert {n.name for n in nodes if type(n) is Rel} == {"|"}
    assert {n.name for n in nodes if type(n) is Fun} == {"S"}
    assert not any(type(n) is Fun and n.name in {"+", "*"} for n in nodes)
    assert " | " in format_formula(formula)


def test_successor_remains_visible_in_the_expanded_product_definition():
    formula = robinson_product(Var("a"), Var("b"), Var("c"))

    assert any(type(n) is Fun and n == S(n.args[0]) for n in subnodes(formula))


def test_constructors_accept_an_interpreted_divisibility_relation():
    from cold_start.divisibility import peano_divides

    a, b, c = Var("a"), Var("b"), Var("c")
    formula = robinson_product(a, b, c, via=peano_divides)
    nodes = tuple(subnodes(formula))

    validate(formula)
    assert formula.free_vars() == frozenset({"a", "b", "c"})
    # every | atom became the PEANO existential graph: no relation symbols left
    assert not any(type(n) is Rel for n in nodes)
    assert {n.name for n in nodes if type(n) is Fun} == {"S", "*"}
    # the interpreted formula keeps the shape of the pure one exactly
    pure = robinson_product(a, b, c)
    interpreted_units = unit_case(a, b, c, via=peano_divides)
    assert interpreted_units == forall(
        "x",
        "",
        And(
            peano_divides(a, Var("x")),
            peano_divides(b, Var("x")),
            peano_divides(c, Var("x")),
        ),
    )
    assert len(nodes) > len(tuple(subnodes(pure)))
