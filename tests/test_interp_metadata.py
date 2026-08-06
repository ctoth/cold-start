"""Fail-closed contracts for interpretation metadata and structural debts."""

from __future__ import annotations

import pytest

from cold_start.interp import (
    GraphSymbol,
    InterpError,
    Interpretation,
    ObligationKey,
    PredicateSymbol,
    obligations,
)
from cold_start.presburger import PRESBURGER
from cold_start.proof import Refl
from cold_start.quotient import QuotientInterpretation, VecSymbol
from cold_start.syntax import Eq, Formula, Term, Var
from cold_start.theory import Signature, Theory
from cold_start.vocabulary import ZERO


def _graph(args: tuple[Term, ...], result: Term) -> Formula:
    return Eq(result, result)


def _closed_source() -> Theory:
    return Theory(
        axioms=frozenset({Eq(Var("x"), Var("x"))}),
        signature=Signature(
            frozenset({""}),
            (("0", (), ""), ("f", ("",), "")),
            (("P", ("",)),),
        ),
    )


def test_obligation_axiom_identity_is_structural() -> None:
    axiom = Eq(Var("x"), Var("x"))
    key = ObligationKey.axiom(axiom)
    artifact = Interpretation(
        "structural",
        Theory(frozenset({axiom})),
        PRESBURGER,
        (),
        payments=((key, Refl(Var("x"))),),
    )
    assert next(o for o in obligations(artifact) if o.key.kind == "axiom").key == key
    assert key.label == f"axiom:{axiom!r}"


def test_duplicate_payment_keys_are_rejected_at_construction() -> None:
    key = ObligationKey.totality("f")
    with pytest.raises(InterpError, match="duplicate payment"):
        Interpretation(
            "duplicate",
            Theory(frozenset()),
            PRESBURGER,
            (),
            payments=((key, Refl(ZERO)), (key, Refl(ZERO))),
        )


@pytest.mark.parametrize("arity", [-1, -20])
def test_symbol_arities_must_be_nonnegative(arity: int) -> None:
    with pytest.raises(InterpError, match="arity"):
        GraphSymbol("f", arity, _graph)
    with pytest.raises(InterpError, match="arity"):
        PredicateSymbol("P", arity, lambda args: Eq(args[0], args[0]))


def test_graph_builders_must_return_canonical_formulas() -> None:
    with pytest.raises(InterpError, match="formula"):
        GraphSymbol("f", 1, lambda args, result: result)  # type: ignore[arg-type,return-value]


def test_artifacts_reject_duplicate_symbols_and_incomplete_source_coverage() -> None:
    source = _closed_source()
    f = GraphSymbol("f", 1, _graph)
    with pytest.raises(InterpError, match="duplicate graph symbol"):
        Interpretation("duplicate", source, PRESBURGER, (f, f))
    with pytest.raises(InterpError, match="missing disposition"):
        Interpretation("incomplete", source, PRESBURGER, (f,))


def test_source_symbol_arity_must_match_the_signature() -> None:
    source = _closed_source()
    with pytest.raises(InterpError, match="source arity"):
        Interpretation(
            "wrong-arity",
            source,
            PRESBURGER,
            (GraphSymbol("f", 2, _graph),),
            retained_funs=(("0", 0),),
            retained_predicates=("P",),
        )


def test_quotient_dimensions_and_metadata_fail_closed() -> None:
    vector = VecSymbol("f", 1, lambda args, result: Eq(result[0], result[0]))
    source = Theory(
        frozenset(),
        signature=Signature(frozenset({""}), (("f", ("",), ""),)),
    )
    for dim in (0, -1):
        with pytest.raises(InterpError, match="dimension"):
            QuotientInterpretation(
                "bad-dimension",
                source,
                PRESBURGER,
                dim,
                lambda left, right: Eq(left[0], right[0]),
                (vector,),
            )
    with pytest.raises(InterpError, match="duplicate vector symbol"):
        QuotientInterpretation(
            "duplicate",
            source,
            PRESBURGER,
            1,
            lambda left, right: Eq(left[0], right[0]),
            (vector, vector),
        )


def test_vector_graphs_are_validated_at_artifact_construction() -> None:
    source = Theory(
        frozenset(),
        signature=Signature(frozenset({""}), (("f", ("",), ""),)),
    )
    bad = VecSymbol("f", 1, lambda args, result: result[0])  # type: ignore[arg-type,return-value]
    with pytest.raises(InterpError, match="formula"):
        QuotientInterpretation(
            "bad-graph",
            source,
            PRESBURGER,
            1,
            lambda left, right: Eq(left[0], right[0]),
            (bad,),
        )
