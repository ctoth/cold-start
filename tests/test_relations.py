"""Atomic relation symbols, the missing syntax needed for Robinson's ``|``.

Relations are formulas, not Boolean-valued function terms.  They pass through
the same exact-type gate, serialization, substitution, sorting, notation, model
semantics, and proof checker as equality atoms.
"""

from __future__ import annotations

import pytest
from semantics import Model, evaluate

from cold_start.checker import Signature, Theory, check
from cold_start.notation import format_formula, parse_formula
from cold_start.proof import Assume, Axiom, from_bytes, to_bytes
from cold_start.syntax import Rel, Var, formula_from_bytes, formula_to_bytes, validate


def test_relation_round_trips_through_syntax_and_proof_bytes():
    claim = Rel("|", (Var("a"), Var("b")))

    assert formula_from_bytes(formula_to_bytes(claim)) == claim
    assert from_bytes(to_bytes(Assume(claim))) == Assume(claim)


def test_relation_args_are_snapshotted_and_exact_type_validated():
    args = [Var("a"), Var("b")]
    claim = Rel("|", args)  # pyright: ignore[reportArgumentType] -- list alias is the attack
    args[0] = Var("changed")

    validate(claim)
    assert claim.args == (Var("a"), Var("b"))

    class LyingRel(Rel):
        def __eq__(self, other):
            return True

    with pytest.raises(TypeError, match="non-canonical node"):
        validate(LyingRel("|", (Var("a"), Var("b"))))


def test_divisibility_notation_round_trips_as_a_relation_atom():
    claim = Rel("|", (Var("a"), Var("b")))

    assert format_formula(claim) == "a | b"
    assert parse_formula("a | b") == claim


def test_model_evaluator_interprets_relation_symbols_directly():
    model = Model("positive divisibility", interp={"|": lambda a, b: b % a == 0})
    claim = Rel("|", (Var("a"), Var("b")))

    assert evaluate(claim, model, {"a": 3, "b": 12})
    assert not evaluate(claim, model, {"a": 5, "b": 12})


NAT_REL_SIG = Signature(
    sorts=frozenset({"N", "X"}),
    ranks=(),
    relations=(("|", ("N", "N")),),
)


def test_sorted_relation_axiom_checks_at_its_declared_rank():
    claim = Rel("|", (Var("a", "N"), Var("b", "N")))
    theory = Theory(axioms=frozenset({claim}), signature=NAT_REL_SIG)

    seq = check(Axiom(claim), theory)

    assert seq.concl == claim
    assert seq.hyps == frozenset()


@pytest.mark.parametrize(
    "claim, message",
    [
        (Rel("|", (Var("a", "N"),)), "expects 2 args"),
        (Rel("bogus", (Var("a", "N"), Var("b", "N"))), "undeclared relation"),
        (Rel("|", (Var("a", "N"), Var("b", "X"))), "arg has sort"),
    ],
)
def test_sorted_relations_reject_wrong_arity_symbol_or_sort(claim, message):
    theory = Theory(axioms=frozenset({claim}), signature=NAT_REL_SIG)

    with pytest.raises(ValueError, match=message):
        check(Axiom(claim), theory)
