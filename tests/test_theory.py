"""Fail-closed construction and validation of signatures and theories."""

from __future__ import annotations

import pytest

from cold_start.algebra import (
    AB_GROUP,
    COMM_MONOID,
    COMM_RING,
    MONOID,
    MONOID_ACTION,
    RING,
    SEMIGROUP,
)
from cold_start.bridges import PRESBURGER_ONE
from cold_start.checker import check
from cold_start.divisibility_bridges import (
    BARE_MULTIPLICATION,
    DIVISIBILITY_CORE,
    PURE_SUCCESSOR_DIVISIBILITY,
)
from cold_start.peano import PEANO
from cold_start.presburger import PRESBURGER
from cold_start.proof import Assume, Refl
from cold_start.rigidity import ROBINSON_PEANO_F
from cold_start.robinson import ROBINSON_PEANO
from cold_start.squaring import SQUARE_ARITHMETIC
from cold_start.squaring_bridges import BARE_MULTIPLICATION_FROM_SQUARE
from cold_start.syntax import Eq, Fun, Rel, Var
from cold_start.theory import Signature, Theory


def test_signature_rejects_duplicate_function_declarations() -> None:
    with pytest.raises(ValueError, match="duplicate function symbol"):
        Signature(
            sorts=frozenset({"N"}),
            ranks=(("f", (), "N"), ("f", ("N",), "N")),
        )


def test_signature_rejects_duplicate_relation_declarations() -> None:
    with pytest.raises(ValueError, match="duplicate relation symbol"):
        Signature(
            sorts=frozenset({"N"}),
            ranks=(),
            relations=(("R", ("N",)), ("R", ())),
        )


def test_signature_rejects_ranks_over_undeclared_sorts() -> None:
    with pytest.raises(ValueError, match="undeclared sort"):
        Signature(
            sorts=frozenset({"N"}),
            ranks=(("f", ("Missing",), "N"),),
        )


def test_signature_rejects_noncanonical_containers() -> None:
    with pytest.raises(TypeError, match="sorts must be a frozenset"):
        Signature(sorts={"N"}, ranks=())  # type: ignore[arg-type]

    with pytest.raises(TypeError, match="ranks must be a tuple"):
        Signature(sorts=frozenset({"N"}), ranks=[])  # type: ignore[arg-type]


@pytest.mark.parametrize(
    ("zero", "succ"),
    [(Fun("0", ()), None), (None, "S")],
)
def test_theory_rejects_half_an_induction_structure(zero, succ) -> None:
    with pytest.raises(ValueError, match="zero and successor must be declared together"):
        Theory(axioms=frozenset(), zero=zero, succ=succ)


def test_theory_rejects_an_induction_successor_with_the_wrong_rank() -> None:
    signature = Signature(
        sorts=frozenset({"N", "M"}),
        ranks=(("0", (), "N"), ("S", ("M",), "M")),
    )

    with pytest.raises(ValueError, match="induction successor"):
        Theory(
            axioms=frozenset(),
            zero=Fun("0", ()),
            succ="S",
            signature=signature,
        )


def test_theory_rejects_ill_sorted_axioms() -> None:
    signature = Signature(
        sorts=frozenset({"N", "M"}),
        ranks=(),
    )
    bad_axiom = Eq(Var("n", "N"), Var("m", "M"))

    with pytest.raises(ValueError, match="equality across sorts"):
        Theory(axioms=frozenset({bad_axiom}), signature=signature)


def test_check_revalidates_an_exact_theory_before_using_it() -> None:
    signature = Signature(sorts=frozenset({"N"}), ranks=())
    theory = Theory(axioms=frozenset(), signature=signature)
    object.__setattr__(theory, "signature", object())

    with pytest.raises(TypeError, match="Theory.signature"):
        check(Refl(Var("n", "N")), theory)


@pytest.mark.parametrize(
    "theory",
    [
        SEMIGROUP,
        MONOID,
        COMM_MONOID,
        MONOID_ACTION,
        RING,
        COMM_RING,
        AB_GROUP,
        PRESBURGER,
        PEANO,
        ROBINSON_PEANO,
        ROBINSON_PEANO_F,
        PRESBURGER_ONE,
        DIVISIBILITY_CORE,
        PURE_SUCCESSOR_DIVISIBILITY,
        BARE_MULTIPLICATION,
        SQUARE_ARITHMETIC,
        BARE_MULTIPLICATION_FROM_SQUARE,
    ],
)
def test_exported_named_theories_have_closed_signatures(theory: Theory) -> None:
    assert theory.signature is not None


def test_presburger_rejects_multiplication() -> None:
    with pytest.raises(ValueError, match="undeclared function symbol"):
        check(Refl(Fun("*", (Var("a"), Var("b")))), PRESBURGER)


def test_peano_and_monoid_reject_unknown_functions() -> None:
    for theory in (PEANO, MONOID):
        with pytest.raises(ValueError, match="undeclared function symbol"):
            check(Refl(Fun("totally_not_declared", ())), theory)


def test_robinson_rejects_primitive_addition() -> None:
    with pytest.raises(ValueError, match="undeclared function symbol"):
        check(Refl(Fun("+", (Var("a"), Var("b")))), ROBINSON_PEANO)


def test_bare_multiplication_rejects_unknown_symbols_and_wrong_arity() -> None:
    with pytest.raises(ValueError, match="undeclared function symbol"):
        check(Refl(Fun("bogus", ())), BARE_MULTIPLICATION)
    with pytest.raises(ValueError, match="expects 2 args"):
        check(Refl(Fun("*", (Var("a"),))), BARE_MULTIPLICATION)


def test_relation_theory_rejects_unknown_relations_and_wrong_arity() -> None:
    with pytest.raises(ValueError, match="undeclared relation"):
        check(Assume(Rel("bogus", (Var("a"),))), DIVISIBILITY_CORE)
    with pytest.raises(ValueError, match="expects 2 args"):
        check(Assume(Rel("|", (Var("a"),))), DIVISIBILITY_CORE)
