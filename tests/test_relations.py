"""Atomic relation symbols, the missing syntax needed for Robinson's ``|``.

Relations are formulas, not Boolean-valued function terms.  They pass through
the same exact-type gate, serialization, substitution, sorting, notation, model
semantics, and proof checker as equality atoms.
"""

from __future__ import annotations

import pytest
from semantics import Model, evaluate

from cold_start.certificate import Certificate
from cold_start.checker import check
from cold_start.codec import (
    decode_certificate,
    decode_formula,
    encode_certificate,
    encode_formula,
)
from cold_start.notation import format_formula, parse_formula
from cold_start.proof import Assume, Axiom
from cold_start.sequent import Sequent
from cold_start.syntax import Rel, Var, validate
from cold_start.theory import Signature, Theory


def test_relation_round_trips_through_syntax_and_proof_bytes():
    claim = Rel("|", (Var("a"), Var("b")))

    assert decode_formula(encode_formula(claim)) == claim
    certificate = Certificate(
        "unused",
        b"\x00" * 32,
        Sequent(frozenset({claim}), claim),
        Assume(claim),
    )
    assert decode_certificate(encode_certificate(certificate)).proof == Assume(claim)


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
def test_theory_rejects_relation_axioms_with_wrong_arity_symbol_or_sort(claim, message):
    with pytest.raises(ValueError, match=message):
        Theory(axioms=frozenset({claim}), signature=NAT_REL_SIG)
