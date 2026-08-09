"""Deterministic trusted work limits across checking and verification."""

from __future__ import annotations

from dataclasses import replace
from typing import cast

import pytest

from cold_start.checker import check, check_with_usage
from cold_start.codec import (
    DEFAULT_CERTIFICATE_LIMITS,
    CertificateLimits,
    encode_certificate,
    make_certificate,
    require_lowered_certificate_limits,
)
from cold_start.peano import PEANO
from cold_start.proof import Assume, Axiom, Cong, Inst, Refl, Sym, Trans
from cold_start.syntax import Eq, Fun, Rel, Var
from cold_start.theory import Signature, Theory
from cold_start.verify import THEORIES, verify_bytes, verify_certificate
from cold_start.work import (
    DEFAULT_WORK_LIMITS,
    WorkLimitError,
    WorkLimits,
    WorkMeter,
    require_lowered_work_limits,
)


def _deep_term(depth: int):
    term = Var("z")
    for _ in range(depth):
        term = Fun("f", (term,))
    return term


def test_small_proof_large_substitution_exceeds_syntax_rebuild_limit() -> None:
    source_term = Var("x")
    for _ in range(100):
        source_term = Fun("f", (source_term,))
    source = Eq(source_term, source_term)
    proof = Inst(Axiom(source), "x", Var("z"))
    theory = Theory(axioms=frozenset({source}))

    check(proof, theory)
    limits = replace(DEFAULT_WORK_LIMITS, max_syntax_rebuilds=50)
    with pytest.raises(WorkLimitError, match="syntax_rebuilds"):
        check(proof, theory, limits=limits)


def test_excessive_hypotheses_exceed_named_derived_limit() -> None:
    equations = tuple(Eq(Var(f"x{index}"), Var(f"x{index}")) for index in range(20))
    proof = Cong("f", tuple(Assume(equation) for equation in equations))
    limits = replace(DEFAULT_WORK_LIMITS, max_derived_hypotheses=10)

    with pytest.raises(WorkLimitError, match="derived_hypotheses"):
        check(proof, Theory(axioms=frozenset()), limits=limits)


def test_huge_string_and_large_derived_formula_have_independent_limits() -> None:
    theory = Theory(axioms=frozenset())
    with pytest.raises(WorkLimitError, match="string_bytes"):
        check(
            Refl(Var("x" * 100)),
            theory,
            limits=replace(DEFAULT_WORK_LIMITS, max_string_bytes=16),
        )

    proof = Refl(_deep_term(100))
    with pytest.raises(WorkLimitError, match="single_formula_nodes"):
        check(
            proof,
            theory,
            limits=replace(DEFAULT_WORK_LIMITS, max_single_formula_nodes=50),
        )


@pytest.mark.parametrize(
    ("field", "proof", "theory"),
    [
        ("max_proof_nodes", Sym(Refl(Var("x"))), Theory(axioms=frozenset())),
        (
            "max_proof_edges",
            Trans(Refl(Var("x")), Refl(Var("x"))),
            Theory(axioms=frozenset()),
        ),
        ("max_syntax_nodes", Refl(Fun("f", (Var("x"),))), Theory(axioms=frozenset())),
        (
            "max_syntax_edges",
            Refl(Fun("f", (Var("x"), Var("y")))),
            Theory(axioms=frozenset()),
        ),
        ("max_syntax_visits", Refl(Fun("f", (Var("x"),))), Theory(axioms=frozenset())),
        ("max_sequent_steps", Sym(Refl(Var("x"))), Theory(axioms=frozenset())),
        ("max_sort_steps", Refl(Var("x")), PEANO),
        (
            "max_hypothesis_elements",
            Cong(
                "f",
                (
                    Assume(Eq(Var("x"), Var("x"))),
                    Assume(Eq(Var("y"), Var("y"))),
                ),
            ),
            Theory(axioms=frozenset()),
        ),
        (
            "max_single_term_nodes",
            Refl(Fun("f", (Var("x"),))),
            Theory(axioms=frozenset()),
        ),
        (
            "max_derived_sequent_nodes",
            Refl(Var("x")),
            Theory(axioms=frozenset()),
        ),
    ],
)
def test_lowering_each_named_cumulative_limit_rejects_predictably(
    field: str, proof, theory: Theory
) -> None:
    limits = replace(DEFAULT_WORK_LIMITS, **{field: 1})
    with pytest.raises(WorkLimitError, match=field.removeprefix("max_")):
        check(proof, theory, limits=limits)


def test_usage_snapshots_are_deterministic() -> None:
    proof = Sym(Refl(Var("x")))
    theory = Theory(axioms=frozenset())

    first = check_with_usage(proof, theory)
    second = check_with_usage(proof, theory)

    assert first.sequent == second.sequent
    assert first.usage == second.usage
    assert first.usage.proof_nodes == 2
    assert first.usage.proof_edges == 1


def test_cumulative_usage_exactly_at_its_limit_is_accepted() -> None:
    meter = WorkMeter(replace(DEFAULT_WORK_LIMITS, max_proof_nodes=2))

    meter.consume("proof_nodes", 2)

    assert meter.snapshot().proof_nodes == 2


@pytest.mark.parametrize("value", [-1, True])
def test_observed_maximum_requires_a_nonnegative_exact_int(value: int) -> None:
    meter = WorkMeter()

    with pytest.raises(TypeError, match="nonnegative exact int"):
        meter.observe("single_term_nodes", value)


def test_string_accounting_accepts_the_exact_ascii_byte_ceiling() -> None:
    meter = WorkMeter(replace(DEFAULT_WORK_LIMITS, max_string_bytes=1))

    meter.inspect_string("x")

    assert meter.snapshot().string_bytes == 1


@pytest.mark.parametrize("size", [0, -1, True])
def test_cached_syntax_size_requires_a_positive_exact_int(size: int) -> None:
    meter = WorkMeter()

    with pytest.raises(TypeError, match="positive exact int"):
        meter.remember_syntax_size(1, size)


def test_work_meter_caches_reject_identity_inconsistency() -> None:
    meter = WorkMeter()
    meter.remember_syntax_size(1, 2)
    meter.remember_term_sort(1, 2, (), "S")
    meter.remember_free_var_sorts(3, frozenset({("x", "S")}))

    assert meter.syntax_size(1) == 2
    assert meter.term_sort(1, 2, ()) == "S"
    assert meter.free_var_sorts(3) == frozenset({("x", "S")})
    with pytest.raises(RuntimeError, match="changed size"):
        meter.remember_syntax_size(1, 3)
    with pytest.raises(RuntimeError, match="changed sort"):
        meter.remember_term_sort(1, 2, (), "T")
    with pytest.raises(RuntimeError, match="changed free variables"):
        meter.remember_free_var_sorts(3, frozenset({("y", "S")}))


def test_work_limit_lowering_requires_exact_objects_in_both_positions() -> None:
    assert require_lowered_work_limits(DEFAULT_WORK_LIMITS) is DEFAULT_WORK_LIMITS
    with pytest.raises(TypeError, match="exact WorkLimits"):
        require_lowered_work_limits(cast(WorkLimits, object()))
    with pytest.raises(TypeError, match="exact WorkLimits"):
        require_lowered_work_limits(
            DEFAULT_WORK_LIMITS,
            cast(WorkLimits, object()),
        )


def test_intrinsic_syntax_accounting_distinguishes_each_operation_kind() -> None:
    x, y = Var("x", "S"), Var("y", "S")
    variables = WorkMeter()
    assert Eq(x, y).free_vars(variables) == frozenset({"x", "y"})
    assert variables.snapshot().syntax_visits == 3

    signature = Signature(
        frozenset({"S"}),
        (("f", ("S", "S"), "S"),),
        (("R", ("S",)),),
    )
    term_work = WorkMeter()
    assert Fun("f", (x, y)).sort_of(signature, meter=term_work) == "S"
    assert term_work.snapshot().sort_steps == 4

    relation_work = WorkMeter()
    Rel("R", (x,)).sort_check(signature, meter=relation_work)
    assert relation_work.snapshot().sort_steps == 3


def test_defaults_accept_every_registered_theory_certificate() -> None:
    for key, theory in THEORIES.items():
        proof = Axiom(next(iter(theory.axioms)))
        certificate = make_certificate(key, theory, proof)
        assert verify_certificate(certificate) == certificate.claim


def test_verifier_overrides_may_only_lower_repository_ceilings() -> None:
    certificate = make_certificate("peano", PEANO, Sym(Refl(Var("x"))))
    data = encode_certificate(certificate)
    lowered = replace(DEFAULT_WORK_LIMITS, max_proof_nodes=1)
    with pytest.raises(WorkLimitError, match="proof_nodes"):
        verify_certificate(certificate, work_limits=lowered)

    raised_work = replace(
        DEFAULT_WORK_LIMITS,
        max_proof_nodes=DEFAULT_WORK_LIMITS.max_proof_nodes + 1,
    )
    with pytest.raises(ValueError, match="may only lower"):
        verify_certificate(certificate, work_limits=raised_work)

    raised_input = replace(
        DEFAULT_CERTIFICATE_LIMITS,
        max_input_bytes=DEFAULT_CERTIFICATE_LIMITS.max_input_bytes + 1,
    )
    with pytest.raises(ValueError, match="may only lower"):
        verify_bytes(data, certificate_limits=raised_input)


@pytest.mark.parametrize("value", [0, True])
def test_work_limit_values_must_be_positive_exact_ints(value: int) -> None:
    with pytest.raises(ValueError, match="positive exact int"):
        replace(DEFAULT_WORK_LIMITS, max_proof_nodes=value)


def test_certificate_limit_values_and_lowering_types_are_exact() -> None:
    with pytest.raises(ValueError, match="positive exact int"):
        replace(DEFAULT_CERTIFICATE_LIMITS, max_input_bytes=0)
    with pytest.raises(ValueError, match="positive exact int"):
        replace(DEFAULT_CERTIFICATE_LIMITS, max_input_bytes=True)
    with pytest.raises(TypeError, match="exact CertificateLimits"):
        require_lowered_certificate_limits(cast(CertificateLimits, object()))
    with pytest.raises(TypeError, match="exact CertificateLimits"):
        require_lowered_certificate_limits(
            DEFAULT_CERTIFICATE_LIMITS,
            cast(CertificateLimits, object()),
        )
