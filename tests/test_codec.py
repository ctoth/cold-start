"""Standalone syntax bytes and portable certificate bytes have one owner."""

from dataclasses import dataclass
from typing import cast

import hamblin
import pytest

import cold_start.codec as codec
from cold_start.certificate import Certificate
from cold_start.codec import (
    decode_certificate,
    decode_formula,
    decode_term,
    encode_certificate,
    encode_formula,
    encode_term,
    make_certificate,
)
from cold_start.peano import PEANO
from cold_start.proof import CANONICAL_PROOF_TYPES, Pf, Refl
from cold_start.syntax import CANONICAL_NODE_TYPES, Eq, Formula, Fun, Term, Var


@dataclass(frozen=True, slots=True)
class _ForeignProof(Pf):
    pass


@dataclass(frozen=True, slots=True)
class _ForeignTerm(Term):
    pass


def test_codec_registry_rejects_noncanonical_proof_and_syntax_classes():
    with pytest.raises(TypeError, match="noncanonical proof type"):
        codec._build_registry(
            CANONICAL_NODE_TYPES,
            CANONICAL_PROOF_TYPES | {_ForeignProof},
        )
    with pytest.raises(TypeError, match="noncanonical syntax type"):
        codec._build_registry(
            CANONICAL_NODE_TYPES | {_ForeignTerm},
            CANONICAL_PROOF_TYPES,
        )


def test_raw_proof_wire_api_is_deleted() -> None:
    assert not hasattr(codec, "encode_proof")
    assert not hasattr(codec, "decode_proof")


def test_each_root_kind_round_trips_through_its_explicit_entrypoint():
    term = Fun("S", (Var("x"),))
    formula = Eq(term, term)
    proof = Refl(term)

    assert decode_term(encode_term(term)) == term
    assert decode_formula(encode_formula(formula)) == formula
    certificate = make_certificate("peano", PEANO, proof)
    assert decode_certificate(encode_certificate(certificate)).proof == proof


def test_decoders_reject_a_known_value_of_the_wrong_root_kind():
    term = Var("x")
    formula = Eq(term, term)

    with pytest.raises(ValueError, match="expected a term"):
        decode_term(encode_formula(formula))
    with pytest.raises(ValueError, match="expected a formula"):
        decode_formula(encode_term(term))
    with pytest.raises(ValueError, match="magic"):
        decode_certificate(encode_formula(formula))


def test_decoders_validate_hostile_field_values_before_returning():
    malformed_term = Var(cast(str, 7))
    malformed_formula = Eq(cast(Term, "not a term"), Var("x"))

    with pytest.raises(TypeError, match="genuine str"):
        decode_term(hamblin.encode(malformed_term))
    with pytest.raises(TypeError, match="non-canonical node"):
        decode_formula(hamblin.encode(malformed_formula))


def test_encoders_reject_a_value_of_the_wrong_root_kind():
    term = Var("x")
    formula = Eq(term, term)

    with pytest.raises(TypeError, match="expected a term"):
        encode_term(cast(Term, formula))
    with pytest.raises(TypeError, match="expected a formula"):
        encode_formula(cast(Formula, term))
    with pytest.raises(TypeError, match="Certificate"):
        encode_certificate(cast(Certificate, formula))


def test_unknown_or_truncated_payload_is_rejected_cleanly():
    with pytest.raises(ValueError):
        decode_certificate(b"not a certificate")


def test_encoding_is_deterministic():
    proof = Refl(Fun("S", (Var("x"),)))
    certificate = make_certificate("peano", PEANO, proof)
    assert encode_certificate(certificate) == encode_certificate(certificate)
