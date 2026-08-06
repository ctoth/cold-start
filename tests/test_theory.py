"""Fail-closed construction and validation of signatures and theories."""

from __future__ import annotations

import pytest

from cold_start.checker import check
from cold_start.proof import Refl
from cold_start.syntax import Eq, Fun, Var
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
