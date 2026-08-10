"""Standalone syntax bytes and portable certificate bytes have one owner."""

from dataclasses import dataclass
from typing import cast

import pytest

import cold_start.codec as codec
from cold_start.certificate import Certificate
from cold_start.codec import (
    decode_certificate,
    encode_certificate,
    make_certificate,
)
from cold_start.peano import PEANO
from cold_start.proof import CANONICAL_PROOF_TYPES, Pf, Refl
from cold_start.syntax import CANONICAL_NODE_TYPES, Eq, Fun, Term, Var


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


def test_frozen_schema_field_kinds_are_exact_and_exhaustive() -> None:
    assert codec._field_kind(int) == ("int", 0)
    assert codec._field_kind(str) == ("string", 1)
    assert codec._field_kind(Term) == ("syntax", 2)
    assert codec._field_kind(Pf) == ("proof", 4)
    assert codec._field_kind(tuple[Term, ...]) == ("syntax_tuple", 3)
    assert codec._field_kind(tuple[Pf, ...]) == ("proof_tuple", 5)
    with pytest.raises(TypeError, match="unsupported"):
        codec._field_kind(tuple[Term])
    with pytest.raises(TypeError, match="unsupported"):
        codec._field_kind(tuple[int, ...])


def test_private_unsigned_varint_rejects_bool_and_negative_values() -> None:
    with pytest.raises(TypeError, match="nonnegative exact int"):
        codec._uvarint(True)
    with pytest.raises(TypeError, match="nonnegative exact int"):
        codec._uvarint(-1)
    with pytest.raises(TypeError, match="noncanonical syntax type"):
        codec._build_registry(
            CANONICAL_NODE_TYPES | {_ForeignTerm},
            CANONICAL_PROOF_TYPES,
        )


def test_raw_proof_wire_api_is_deleted() -> None:
    assert not hasattr(codec, "encode_proof")
    assert not hasattr(codec, "decode_proof")


def test_the_certificate_round_trips_through_its_explicit_entrypoint():
    term = Fun("S", (Var("x"),))
    proof = Refl(term)

    certificate = make_certificate("peano", PEANO, proof)
    assert decode_certificate(encode_certificate(certificate)).proof == proof


def test_the_certificate_decoder_rejects_standalone_syntax_bytes():
    """Standalone syntax bytes are a real encoding of this repo's own making,
    but they are not a certificate: the frame check must say so."""
    formula = Eq(Var("x"), Var("x"))

    with pytest.raises(ValueError, match="magic"):
        decode_certificate(codec._standalone_syntax_bytes(formula))


def test_the_certificate_encoder_rejects_a_value_of_the_wrong_root_kind():
    formula = Eq(Var("x"), Var("x"))

    with pytest.raises(TypeError, match="Certificate"):
        encode_certificate(cast(Certificate, formula))


def test_unknown_or_truncated_payload_is_rejected_cleanly():
    with pytest.raises(ValueError):
        decode_certificate(b"not a certificate")


def test_encoding_is_deterministic():
    proof = Refl(Fun("S", (Var("x"),)))
    certificate = make_certificate("peano", PEANO, proof)
    assert encode_certificate(certificate) == encode_certificate(certificate)
