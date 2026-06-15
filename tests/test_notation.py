"""Notation parser/formatter tests.

The parser is only a human surface over syntax.py. These tests make that exact:
generated syntax nodes must print to notation and parse back to the same data.
"""

from __future__ import annotations

from hypothesis import given
from hypothesis import strategies as st

from cold_start.notation import format_formula, format_term, parse_formula, parse_term
from cold_start.syntax import (
    Bottom,
    Eq,
    Exists,
    Forall,
    Formula,
    Fun,
    Implies,
    Not,
    Term,
    Var,
    exists,
    forall,
)

VAR_NAMES = st.sampled_from(["x", "y", "z", "n", "m", "a", "b"])
SORTS = st.sampled_from(["", "N", "M", "X"])
FUN_NAMES = st.sampled_from(["0", "1", "e", "S", "+", "*", "f", "g", "act"])


def terms():
    leaf = st.one_of(
        st.builds(Var, VAR_NAMES, SORTS),
        st.builds(lambda name: Fun(name, ()), FUN_NAMES),
    )
    return st.recursive(
        leaf,
        lambda kids: st.one_of(
            st.builds(lambda a, b: Fun("+", (a, b)), kids, kids),
            st.builds(lambda a, b: Fun("*", (a, b)), kids, kids),
            st.builds(
                lambda name, args: Fun(name, tuple(args)),
                FUN_NAMES,
                st.lists(kids, max_size=3),
            ),
        ),
        max_leaves=12,
    )


def formulas():
    return st.recursive(
        st.one_of(st.builds(Eq, terms(), terms()), st.builds(Bottom)),
        lambda kids: st.one_of(
            st.builds(Implies, kids, kids),
            st.builds(forall, VAR_NAMES, SORTS, kids),
            st.builds(exists, VAR_NAMES, SORTS, kids),
        ),
        max_leaves=10,
    )


def test_parse_unicode_quantifier_and_infix_term():
    parsed = parse_formula("∀x:N. x + 0 = x")
    expected = forall("x", "N", Eq(Fun("+", (Var("x", "N"), Fun("0", ()))), Var("x", "N")))
    assert parsed == expected


def test_parse_negation_inequality_bottom_and_ascii_aliases():
    assert parse_formula("S(x) ≠ 0") == Not(Eq(Fun("S", (Var("x"),)), Fun("0", ())))
    assert parse_formula("not (x = 0)") == Not(Eq(Var("x"), Fun("0", ())))
    assert parse_formula("x = 0 -> ⊥") == Not(Eq(Var("x"), Fun("0", ())))
    assert parse_formula("exists x. x != 0") == exists("x", "", Not(Eq(Var("x"), Fun("0", ()))))


def test_parse_parenthesized_terms_inside_formula():
    parsed = parse_formula("(x + y) * z = x * z + y * z")
    expected = Eq(
        Fun("*", (Fun("+", (Var("x"), Var("y"))), Var("z"))),
        Fun("+", (Fun("*", (Var("x"), Var("z"))), Fun("*", (Var("y"), Var("z"))))),
    )
    assert parsed == expected


def test_formatter_uses_binder_sort_without_repeating_it_in_body():
    formula = forall("x", "N", Eq(Var("x", "N"), Var("x", "N")))
    assert format_formula(formula) == "∀x:N. x = x"
    assert parse_formula(format_formula(formula)) == formula


def test_quoted_names_roundtrip():
    term = Fun("odd function", (Var("x-y"),))
    rendered = format_term(term)
    assert rendered == "`odd function`(`x-y`)"
    assert parse_term(rendered) == term


@given(terms())
def test_terms_roundtrip_through_notation(term: Term):
    assert parse_term(format_term(term)) == term


@given(formulas())
def test_formulas_roundtrip_through_notation(formula: Formula):
    assert parse_formula(format_formula(formula)) == formula


@given(st.sampled_from([Eq, Implies, Bottom, Forall, Exists]))
def test_symbols_are_declared_on_formula_classes(cls):
    assert isinstance(cls.symbol, str)
    assert cls.symbol


def test_quantifier_repr_uses_the_locally_nameless_form():
    # Regression: the binder dataclasses must carry repr=False so the iterative
    # Node.__repr__ / _repr_with is used, not a dataclass-generated recursive repr.
    f = forall("x", "N", Eq(Var("x", "N"), Var("x", "N")))
    assert repr(f) == "(forall :N. #0 = #0)"
    g = exists("y", "", Eq(Var("y"), Var("y")))
    assert repr(g) == "(exists. #0 = #0)"


def test_deep_formula_formats_without_recursion():
    """The notation printer is iterative: a formula nested far deeper than the
    recursion limit renders without blowing the stack (implications, no binders --
    binder fresh-naming is a separate, quadratic concern)."""
    import sys as _sys

    f: Formula = Eq(Var("x"), Var("x"))  # not Bottom: avoid the ¬ (Not) sugar
    for _ in range(50_000):
        f = Implies(Bottom(), f)
    old = _sys.getrecursionlimit()
    _sys.setrecursionlimit(300)
    try:
        rendered = format_formula(f)
    finally:
        _sys.setrecursionlimit(old)
    assert isinstance(rendered, str)
    assert rendered.count("→") == 50_000
