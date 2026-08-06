"""Predicate-symbol interpretations: atomic ``|`` lands on its PEANO graph."""

from __future__ import annotations

import pytest

from cold_start.bridges import PLUS
from cold_start.divisibility import divides_factor, divides_refl, peano_divides
from cold_start.interp import InterpError, Interpretation, PredicateSymbol, translate, verify
from cold_start.peano import PEANO, mul
from cold_start.presburger import add
from cold_start.robinson import bridge
from cold_start.syntax import Implies, Rel, Var, forall
from cold_start.theory import Theory

_a, _b, _c = Var("a"), Var("b"), Var("c")

DIVIDES = PredicateSymbol("|", 2, lambda args: peano_divides(args[0], args[1]))


def test_translate_maps_an_atomic_predicate_to_its_target_formula():
    source = Rel("|", (_a, _b))

    assert translate(source, (), predicates=(DIVIDES,)) == peano_divides(_a, _b)


def test_translate_leaves_an_unmapped_relation_atom_intact():
    source = Rel("R", (_a, _b))

    assert translate(source, (), predicates=(DIVIDES,)) == source


def test_translate_rejects_a_mapped_predicate_at_the_wrong_arity():
    with pytest.raises(InterpError, match="expects 2 args"):
        translate(Rel("|", (_a,)), (), predicates=(DIVIDES,))


def test_predicate_arguments_can_contain_a_relationally_translated_function():
    source = Rel("|", (add(_a, _b), _c))
    witness = Var("u!")
    expected = forall(
        "u!",
        "",
        Implies(bridge(_a, _b, witness), peano_divides(witness, _c)),
    )

    assert translate(source, (PLUS,), predicates=(DIVIDES,)) == expected


def test_predicate_interpretation_has_no_function_definedness_debt():
    refl_atom = Rel("|", (_a, _a))
    factor_atom = Rel("|", (_a, mul(_a, _b)))
    source = Theory(axioms=frozenset({refl_atom, factor_atom}))
    artifact = Interpretation(
        name="divisibility-foundations-into-peano",
        source=source,
        target=PEANO,
        symbols=(),
        predicates=(DIVIDES,),
        payments=(
            (f"axiom:{refl_atom!r}", divides_refl()),
            (f"axiom:{factor_atom!r}", divides_factor()),
        ),
    )

    report = verify(artifact)

    assert report.complete
    assert report.open_labels() == ()
    assert {s.obligation.label for s in report.statuses} == {
        f"axiom:{refl_atom!r}",
        f"axiom:{factor_atom!r}",
    }
    assert report.bridge_size > 0
