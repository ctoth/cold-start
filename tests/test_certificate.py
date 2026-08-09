"""Portable DAG certificates: canonical bytes, hostile input, and verification."""

from __future__ import annotations

import subprocess
import sys
from dataclasses import replace
from typing import cast

import pytest

import cold_start.verify as verifier
from cold_start.certificate import Certificate
from cold_start.codec import (
    DEFAULT_CERTIFICATE_LIMITS,
    CertificateLimits,
    decode_certificate,
    encode_certificate,
    make_certificate,
    theory_fingerprint,
)
from cold_start.peano import PEANO
from cold_start.proof import Assume, Axiom, Cong, Refl, Sym, Trans
from cold_start.sequent import Sequent
from cold_start.syntax import Eq, Fun, Var
from cold_start.theory import Signature, Theory
from cold_start.verify import THEORIES, verify_certificate


def _uvarint(value: int) -> bytes:
    out = bytearray()
    while True:
        byte = value & 0x7F
        value >>= 7
        out.append(byte | (0x80 if value else 0))
        if not value:
            return bytes(out)


def _string(value: str) -> bytes:
    payload = value.encode("utf-8")
    return _uvarint(len(payload)) + payload


def _field_int(value: int) -> bytes:
    return b"\x00" + _uvarint(value)


def _field_string(value: str) -> bytes:
    return b"\x01" + _string(value)


def _field_syntax(index: int) -> bytes:
    return b"\x02" + _uvarint(index)


def _field_syntax_tuple(*indices: int) -> bytes:
    return b"\x03" + _uvarint(len(indices)) + b"".join(map(_uvarint, indices))


def _field_proof(index: int) -> bytes:
    return b"\x04" + _uvarint(index)


def _field_proof_tuple(*indices: int) -> bytes:
    return b"\x05" + _uvarint(len(indices)) + b"".join(map(_uvarint, indices))


def _entry(name: str, *fields: bytes) -> bytes:
    return _string(name) + _uvarint(len(fields)) + b"".join(fields)


def _raw_certificate(
    syntax: tuple[bytes, ...],
    proofs: tuple[bytes, ...],
    *,
    hypotheses: tuple[int, ...] = (),
    conclusion: int = 1,
    root: int = 0,
    version: int = 1,
) -> bytes:
    return b"".join(
        (
            b"CSPC",
            _uvarint(version),
            _string("peano"),
            b"\x00" * 32,
            _uvarint(len(syntax)),
            *syntax,
            _uvarint(len(proofs)),
            *proofs,
            _uvarint(len(hypotheses)),
            *(_uvarint(index) for index in hypotheses),
            _uvarint(conclusion),
            _uvarint(root),
        )
    )


VAR_X = _entry("Var", _field_string("x"), _field_string(""))
EQ_XX = _entry("Eq", _field_syntax(0), _field_syntax(0))
REFL_X = _entry("Refl", _field_syntax(0))


def _tiny_certificate() -> Certificate:
    return make_certificate("peano", PEANO, Refl(Var("x")))


def test_certificate_is_inert_data_and_canonical_roundtrip() -> None:
    certificate = _tiny_certificate()
    data = encode_certificate(certificate)
    decoded = decode_certificate(data)

    assert type(decoded) is Certificate
    assert decoded == certificate
    assert encode_certificate(decoded) == data


def test_structural_duplicates_decode_to_shared_exact_objects() -> None:
    shared = Refl(Var("x"))
    certificate = make_certificate("peano", PEANO, Trans(shared, shared))

    decoded = decode_certificate(encode_certificate(certificate))

    assert type(decoded.proof) is Trans
    assert decoded.proof.left is decoded.proof.right
    assert type(decoded.claim.concl) is Eq
    assert decoded.claim.concl.lhs is decoded.claim.concl.rhs


def test_unknown_version_tag_and_malformed_field_are_rejected() -> None:
    unknown_version = _raw_certificate((VAR_X, EQ_XX), (REFL_X,), version=2)
    unknown_tag_var = _entry("Var", b"\xff", _field_string(""))
    unknown_tag = _raw_certificate((unknown_tag_var, EQ_XX), (REFL_X,))
    malformed_var = _entry("Var", _field_int(7), _field_string(""))
    malformed_field = _raw_certificate((malformed_var, EQ_XX), (REFL_X,))

    with pytest.raises(ValueError, match="version"):
        decode_certificate(unknown_version)
    with pytest.raises(ValueError, match="field tag"):
        decode_certificate(unknown_tag)
    with pytest.raises(ValueError, match="field marker"):
        decode_certificate(malformed_field)


def test_trailing_nonminimal_truncated_and_invalid_utf8_are_rejected() -> None:
    valid_shape = _raw_certificate((VAR_X, EQ_XX), (REFL_X,))
    nonminimal_version = b"CSPC\x81\x00" + valid_shape[5:]
    invalid_key = b"CSPC\x01\x01\xff" + valid_shape[len(b"CSPC\x01\x06peano") :]

    with pytest.raises(ValueError, match="trailing"):
        decode_certificate(valid_shape + b"extra")
    with pytest.raises(ValueError, match="nonminimal"):
        decode_certificate(nonminimal_version)
    with pytest.raises(ValueError, match="UTF-8"):
        decode_certificate(invalid_key)
    with pytest.raises(ValueError, match="truncated"):
        decode_certificate(valid_shape[:-1])


@pytest.mark.parametrize(
    ("bad_eq", "message"),
    [
        (_entry("Eq", _field_syntax(1), _field_syntax(0)), "cyclic"),
        (_entry("Eq", _field_syntax(2), _field_syntax(0)), "forward"),
        (_entry("Eq", _field_syntax(99), _field_syntax(0)), "out of range"),
    ],
)
def test_syntax_self_forward_and_out_of_range_references_are_rejected(
    bad_eq: bytes, message: str
) -> None:
    syntax = (VAR_X, bad_eq, _entry("Var", _field_string("y"), _field_string("")))
    with pytest.raises(ValueError, match=message):
        decode_certificate(_raw_certificate(syntax, (REFL_X,)))


@pytest.mark.parametrize(
    ("index", "message"),
    [(1, "cyclic"), (2, "forward"), (3, "out of range")],
)
def test_syntax_tuple_references_are_checked_backward(
    index: int, message: str
) -> None:
    bad_fun = _entry("Fun", _field_string("f"), _field_syntax_tuple(index))
    syntax = (VAR_X, bad_fun, _entry("Var", _field_string("y"), _field_string("")))
    with pytest.raises(ValueError, match=message):
        decode_certificate(_raw_certificate(syntax, (REFL_X,)))


def test_proof_self_forward_and_out_of_range_references_are_rejected() -> None:
    cases = (
        ((_entry("Sym", _field_proof(0)),), "cyclic"),
        (
            (
                _entry("Sym", _field_proof(1)),
                _entry("Refl", _field_syntax(0)),
            ),
            "forward",
        ),
        ((_entry("Sym", _field_proof(99)),), "out of range"),
    )
    for proofs, message in cases:
        with pytest.raises(ValueError, match=message):
            decode_certificate(_raw_certificate((VAR_X, EQ_XX), proofs))


def test_duplicate_and_noncanonical_table_entries_are_rejected() -> None:
    duplicate_syntax = _raw_certificate(
        (VAR_X, VAR_X, _entry("Eq", _field_syntax(0), _field_syntax(0))),
        (REFL_X,),
        conclusion=2,
    )
    duplicate_proof = _raw_certificate(
        (VAR_X, EQ_XX),
        (REFL_X, REFL_X),
        root=1,
    )
    with pytest.raises(ValueError, match="duplicate syntax"):
        decode_certificate(duplicate_syntax)
    with pytest.raises(ValueError, match="duplicate proof"):
        decode_certificate(duplicate_proof)


def test_claim_hypotheses_must_be_sorted_unique_formula_references() -> None:
    var_y = _entry("Var", _field_string("y"), _field_string(""))
    eq_yy = _entry("Eq", _field_syntax(2), _field_syntax(2))
    syntax = (VAR_X, EQ_XX, var_y, eq_yy)
    proof = _entry("Assume", _field_syntax(1))
    with pytest.raises(ValueError, match="duplicate claim"):
        decode_certificate(
            _raw_certificate(syntax, (proof,), hypotheses=(1, 1), conclusion=1)
        )
    with pytest.raises(ValueError, match="sorted"):
        decode_certificate(
            _raw_certificate(syntax, (proof,), hypotheses=(3, 1), conclusion=1)
        )


def test_unknown_class_wrong_root_and_trailing_claim_references_are_rejected() -> None:
    unknown = _entry("UnknownNode", _field_string("x"))
    with pytest.raises(ValueError, match="unknown syntax class"):
        decode_certificate(_raw_certificate((unknown, EQ_XX), (REFL_X,)))
    with pytest.raises(ValueError, match="claim conclusion.*formula"):
        decode_certificate(_raw_certificate((VAR_X,), (REFL_X,), conclusion=0))
    with pytest.raises(ValueError, match="proof root"):
        decode_certificate(_raw_certificate((VAR_X, EQ_XX), (REFL_X,), root=9))


def test_theory_fingerprint_is_semantic_and_slug_independent() -> None:
    proof = Refl(Var("x"))
    assert make_certificate("peano", PEANO, proof).theory_fingerprint == make_certificate(
        "an-alias", PEANO, proof
    ).theory_fingerprint
    assert theory_fingerprint(PEANO) != theory_fingerprint(THEORIES["presburger"])
    assert theory_fingerprint(PEANO).hex() == (
        "2fcbbde618c3db3c5136a63480178c21f05cfddfa8f92601514bd19a71da3ff3"
    )
    assert theory_fingerprint(THEORIES["robinson"]).hex() == (
        "3dcb23bcdf128906e62982d82c361ea5384453e3c7c9cf759a5d183457bef6e5"
    )
    no_relation = Theory(
        axioms=frozenset(),
        signature=Signature(frozenset({"S"}), ()),
    )
    one_relation = Theory(
        axioms=frozenset(),
        signature=Signature(frozenset({"S"}), (), (("R", ("S",)),)),
    )
    assert theory_fingerprint(no_relation) != theory_fingerprint(one_relation)


def test_certificate_scalar_fields_and_builder_key_are_exact() -> None:
    certificate = _tiny_certificate()
    malformed = (
        replace(certificate, theory_key=""),
        replace(certificate, theory_key=cast(str, 7)),
        replace(certificate, theory_fingerprint=b""),
        replace(certificate, theory_fingerprint=cast(bytes, bytearray(32))),
    )
    for value in malformed:
        with pytest.raises(TypeError):
            encode_certificate(value)
    with pytest.raises(TypeError, match="nonempty exact str"):
        make_certificate("", PEANO, Refl(Var("x")))
    with pytest.raises(TypeError, match="nonempty exact str"):
        make_certificate(cast(str, 7), PEANO, Refl(Var("x")))


def test_verifier_rejects_unknown_theory_fingerprint_and_claim_mismatch() -> None:
    certificate = _tiny_certificate()
    wrong_key = replace(certificate, theory_key="nonesuch")
    wrong_fingerprint = replace(certificate, theory_fingerprint=b"x" * 32)
    wrong_claim = replace(certificate, claim=Sequent(frozenset(), Eq(Var("y"), Var("y"))))

    with pytest.raises(ValueError, match="unknown embedded theory"):
        verify_certificate(wrong_key)
    with pytest.raises(ValueError, match="fingerprint mismatch"):
        verify_certificate(wrong_fingerprint)
    with pytest.raises(ValueError, match="claim mismatch"):
        verify_certificate(wrong_claim)


def test_every_registered_theory_verifies_in_a_fresh_process() -> None:
    for key, theory in THEORIES.items():
        proof = Axiom(next(iter(theory.axioms)))
        data = encode_certificate(make_certificate(key, theory, proof))
        result = subprocess.run(
            [sys.executable, "-m", "cold_start.verify"],
            input=data,
            capture_output=True,
            check=False,
        )
        assert result.returncode == 0, (key, result.stderr.decode())
        assert f"VERIFIED [{key}]" in result.stdout.decode()


def test_cli_has_no_external_theory_selector() -> None:
    result = subprocess.run(
        [sys.executable, "-m", "cold_start.verify", "--theory", "peano"],
        input=encode_certificate(_tiny_certificate()),
        capture_output=True,
        check=False,
    )
    assert result.returncode == 2
    assert "unrecognized arguments" in result.stderr.decode()


def test_cli_reports_artifact_work_and_repository_ceilings_on_request() -> None:
    data = encode_certificate(_tiny_certificate())
    result = subprocess.run(
        [sys.executable, "-m", "cold_start.verify", "--report-work"],
        input=data,
        capture_output=True,
        check=False,
    )

    assert result.returncode == 0, result.stderr.decode()
    output = result.stdout.decode()
    assert f"certificate_bytes={len(data)}" in output
    assert "proof_nodes=1" in output
    assert "max_proof_nodes=1000000" in output
    assert "max_input_bytes=67108864" in output


def test_verifier_file_reader_accepts_exact_size_and_labels_file_errors(
    tmp_path,
) -> None:
    path = tmp_path / "proof.cspc"
    data = encode_certificate(_tiny_certificate())
    path.write_bytes(data)
    assert verifier._read_input(str(path), len(data)) == data
    with pytest.raises(ValueError, match="input bytes limit"):
        verifier._read_input(str(path), len(data) - 1)

    missing = tmp_path / "missing.cspc"
    result = subprocess.run(
        [sys.executable, "-m", "cold_start.verify", str(missing)],
        capture_output=True,
        check=False,
    )
    assert result.returncode == 2
    assert "missing.cspc" in result.stderr.decode()
    assert "standard input" not in result.stderr.decode()


def test_each_certificate_input_limit_rejects_before_acceptance() -> None:
    tiny = encode_certificate(_tiny_certificate())
    x, y = Var("x"), Var("y")
    tuple_data = encode_certificate(
        make_certificate("peano", PEANO, Refl(Fun("+", (x, y))))
    )
    two_proof_data = encode_certificate(
        make_certificate("peano", PEANO, Sym(Refl(x)))
    )
    two_hypothesis_data = encode_certificate(
        make_certificate(
            "peano",
            PEANO,
            Cong("+", (Assume(Eq(x, x)), Assume(Eq(y, y)))),
        )
    )
    cases: tuple[tuple[bytes, CertificateLimits, str], ...] = (
        (
            tiny,
            replace(DEFAULT_CERTIFICATE_LIMITS, max_input_bytes=len(tiny) - 1),
            "input bytes",
        ),
        (tiny, replace(DEFAULT_CERTIFICATE_LIMITS, max_syntax_entries=1), "syntax entries"),
        (
            two_proof_data,
            replace(DEFAULT_CERTIFICATE_LIMITS, max_proof_entries=1),
            "proof entries",
        ),
        (tiny, replace(DEFAULT_CERTIFICATE_LIMITS, max_edges=2), "edges"),
        (tuple_data, replace(DEFAULT_CERTIFICATE_LIMITS, max_tuple_arity=1), "tuple arity"),
        (tiny, replace(DEFAULT_CERTIFICATE_LIMITS, max_string_bytes=1), "string bytes"),
        (
            two_hypothesis_data,
            replace(DEFAULT_CERTIFICATE_LIMITS, max_claim_hypotheses=1),
            "claim hypotheses",
        ),
    )
    for data, limits, message in cases:
        with pytest.raises(ValueError, match=message):
            decode_certificate(data, limits=limits)


def test_each_certificate_limit_accepts_its_exact_boundary() -> None:
    tiny = encode_certificate(_tiny_certificate())
    exact_tiny = replace(
        DEFAULT_CERTIFICATE_LIMITS,
        max_input_bytes=len(tiny),
        max_syntax_entries=2,
        max_proof_entries=1,
        max_edges=5,
        max_string_bytes=5,
    )
    assert decode_certificate(tiny, limits=exact_tiny) == _tiny_certificate()

    x, y = Var("x"), Var("y")
    tuple_data = encode_certificate(
        make_certificate("peano", PEANO, Refl(Fun("+", (x, y))))
    )
    assert decode_certificate(
        tuple_data,
        limits=replace(DEFAULT_CERTIFICATE_LIMITS, max_tuple_arity=2),
    ).proof == Refl(Fun("+", (x, y)))

    two_hypothesis_data = encode_certificate(
        make_certificate(
            "peano",
            PEANO,
            Cong("+", (Assume(Eq(x, x)), Assume(Eq(y, y)))),
        )
    )
    assert len(
        decode_certificate(
            two_hypothesis_data,
            limits=replace(DEFAULT_CERTIFICATE_LIMITS, max_claim_hypotheses=2),
        ).claim.hyps
    ) == 2


def test_exactly_out_of_range_references_are_rejected() -> None:
    var_y = _entry("Var", _field_string("y"), _field_string(""))
    syntax = (VAR_X, EQ_XX, var_y)
    cases = (
        _raw_certificate(
            (VAR_X, _entry("Eq", _field_syntax(2), _field_syntax(0))),
            (REFL_X,),
        ),
        _raw_certificate(
            (VAR_X, EQ_XX),
            (_entry("Refl", _field_syntax(2)),),
        ),
        _raw_certificate(syntax, (REFL_X,), hypotheses=(3,)),
        _raw_certificate((VAR_X, EQ_XX), (REFL_X,), conclusion=2),
        _raw_certificate((VAR_X, EQ_XX), (REFL_X,), root=1),
        _raw_certificate(
            (VAR_X, EQ_XX),
            (REFL_X, _entry("Sym", _field_proof(2))),
            root=1,
        ),
    )
    for data in cases:
        with pytest.raises(ValueError, match="out of range"):
            decode_certificate(data)


def test_deep_valid_proof_graph_roundtrips_without_recursion() -> None:
    proof = Refl(Var("x"))
    for _ in range(5_000):
        proof = Sym(proof)
    certificate = make_certificate("peano", PEANO, proof)

    decoded = decode_certificate(encode_certificate(certificate))

    assert verify_certificate(decoded) == certificate.claim


def test_field_helpers_cover_tuple_tags_in_the_frozen_grammar() -> None:
    fun = _entry("Fun", _field_string("f"), _field_syntax_tuple(0))
    congruence = _entry("Cong", _field_string("f"), _field_proof_tuple(0))
    assert fun and congruence
