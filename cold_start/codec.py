"""Canonical external encodings for syntax and portable DAG certificates.

Standalone term/formula bytes remain an untrusted Hamblin adapter. Proofs cross
the external boundary only inside the versioned ``CSPC`` certificate format,
which embeds a theory key, semantic fingerprint, claimed sequent, canonical
syntax table, and canonical proof DAG.
"""

from __future__ import annotations

from collections.abc import Collection, Iterable
from dataclasses import dataclass, fields
from hashlib import sha256
from typing import Any, Literal, TypeAlias, cast, get_args, get_origin, get_type_hints

import hamblin

from .certificate import Certificate
from .checker import check, validate_proof
from .proof import CANONICAL_PROOF_TYPES, Pf
from .sequent import Sequent
from .syntax import (
    CANONICAL_NODE_TYPES,
    BVar,
    Formula,
    Node,
    Term,
    children,
    validate,
)
from .theory import Theory, validate_theory

_MAGIC = b"CSPC"
_VERSION = 1
_INT = 0
_STRING = 1
_SYNTAX = 2
_SYNTAX_TUPLE = 3
_PROOF = 4
_PROOF_TUPLE = 5
_KNOWN_FIELD_TAGS = frozenset({_INT, _STRING, _SYNTAX, _SYNTAX_TUPLE, _PROOF, _PROOF_TUPLE})

_TERM_TYPES = frozenset(cls for cls in CANONICAL_NODE_TYPES if issubclass(cls, Term))
_FORMULA_TYPES = frozenset(cls for cls in CANONICAL_NODE_TYPES if issubclass(cls, Formula))


@dataclass(frozen=True, slots=True)
class CertificateLimits:
    max_input_bytes: int
    max_syntax_entries: int
    max_proof_entries: int
    max_edges: int
    max_tuple_arity: int
    max_string_bytes: int
    max_claim_hypotheses: int

    def __post_init__(self) -> None:
        for field_info in fields(self):
            value = getattr(self, field_info.name)
            if type(value) is not int or value <= 0:
                raise ValueError(f"{field_info.name} must be a positive exact int")


DEFAULT_CERTIFICATE_LIMITS = CertificateLimits(
    max_input_bytes=64 * 1024 * 1024,
    max_syntax_entries=1_000_000,
    max_proof_entries=1_000_000,
    max_edges=4_000_000,
    max_tuple_arity=1_000_000,
    max_string_bytes=1_000_000,
    max_claim_hypotheses=100_000,
)


def _build_registry(
    syntax_types: Collection[type],
    proof_types: Collection[type],
) -> tuple[dict[str, type[Node]], dict[str, type[Pf]]]:
    syntax_set = frozenset(syntax_types)
    proof_set = frozenset(proof_types)
    if syntax_set != CANONICAL_NODE_TYPES:
        extras = syntax_set - CANONICAL_NODE_TYPES
        if extras:
            raise TypeError(f"noncanonical syntax type: {next(iter(extras))!r}")
        raise TypeError("syntax registry omits a canonical type")
    if proof_set != CANONICAL_PROOF_TYPES:
        extras = proof_set - CANONICAL_PROOF_TYPES
        if extras:
            raise TypeError(f"noncanonical proof type: {next(iter(extras))!r}")
        raise TypeError("proof registry omits a canonical type")

    names = [value.__name__ for value in (*syntax_set, *proof_set)]
    if len(names) != len(set(names)):
        raise ValueError("duplicate canonical codec type name")
    return (
        {node_type.__name__: node_type for node_type in syntax_set},
        {proof_type.__name__: proof_type for proof_type in proof_set},
    )


_SYNTAX_REGISTRY, _PROOF_REGISTRY = _build_registry(
    CANONICAL_NODE_TYPES,
    CANONICAL_PROOF_TYPES,
)


FieldKind: TypeAlias = Literal[
    "int", "string", "syntax", "syntax_tuple", "proof", "proof_tuple"
]


@dataclass(frozen=True, slots=True)
class _FieldSpec:
    name: str
    kind: FieldKind
    marker: int


def _field_kind(annotation: Any) -> tuple[FieldKind, int]:
    if annotation is int:
        return "int", _INT
    if annotation is str:
        return "string", _STRING
    if isinstance(annotation, type) and issubclass(annotation, Node):
        return "syntax", _SYNTAX
    if isinstance(annotation, type) and issubclass(annotation, Pf):
        return "proof", _PROOF
    if get_origin(annotation) is tuple:
        args = get_args(annotation)
        if len(args) == 2 and args[1] is Ellipsis:
            element = args[0]
            if isinstance(element, type) and issubclass(element, Node):
                return "syntax_tuple", _SYNTAX_TUPLE
            if isinstance(element, type) and issubclass(element, Pf):
                return "proof_tuple", _PROOF_TUPLE
    raise TypeError(f"unsupported canonical codec field annotation: {annotation!r}")


def _schema(node_type: type) -> tuple[_FieldSpec, ...]:
    hints = get_type_hints(node_type)
    out: list[_FieldSpec] = []
    for field_info in fields(node_type):
        kind, marker = _field_kind(hints[field_info.name])
        out.append(_FieldSpec(field_info.name, kind, marker))
    return tuple(out)


_SYNTAX_SCHEMAS = {node_type: _schema(node_type) for node_type in CANONICAL_NODE_TYPES}
_PROOF_SCHEMAS = {proof_type: _schema(proof_type) for proof_type in CANONICAL_PROOF_TYPES}


def _require_root(
    value: object,
    kinds: Collection[type[object]],
    label: str,
    error: type[Exception],
) -> None:
    if type(value) not in kinds:
        raise error(f"expected {label}, got {type(value).__name__}")


def _open_term_depth(term: Term) -> int:
    depth = 0
    stack: list[object] = [term]
    while stack:
        node = stack.pop()
        if type(node) is BVar and type(node.index) is int:
            depth = max(depth, node.index + 1)
        if type(node) in CANONICAL_NODE_TYPES:
            stack.extend(children(node))
    return depth


def encode_term(term: Term) -> bytes:
    _require_root(term, _TERM_TYPES, "a term", TypeError)
    validate(term, _open_term_depth(term))
    return hamblin.encode(term)


def decode_term(data: bytes) -> Term:
    node = hamblin.decode(data, _SYNTAX_REGISTRY)
    _require_root(node, _TERM_TYPES, "a term", ValueError)
    term = cast(Term, node)
    validate(term, _open_term_depth(term))
    return term


def encode_formula(formula: Formula) -> bytes:
    _require_root(formula, _FORMULA_TYPES, "a formula", TypeError)
    validate(formula)
    return hamblin.encode(formula)


def decode_formula(data: bytes) -> Formula:
    node = hamblin.decode(data, _SYNTAX_REGISTRY)
    _require_root(node, _FORMULA_TYPES, "a formula", ValueError)
    validate(node)
    return cast(Formula, node)


def _uvarint(value: int) -> bytes:
    if type(value) is not int or value < 0:
        raise TypeError("uvarint value must be a nonnegative exact int")
    out = bytearray()
    while True:
        byte = value & 0x7F
        value >>= 7
        out.append(byte | (0x80 if value else 0))
        if not value:
            return bytes(out)


def _string(value: str) -> bytes:
    if type(value) is not str:
        raise TypeError("certificate string must be an exact str")
    payload = value.encode("utf-8")
    return _uvarint(len(payload)) + payload


def _identity_postorder(
    roots: Iterable[object], allowed: frozenset[type]
) -> tuple[object, ...]:
    unseen, active, complete = 0, 1, 2
    colors: dict[int, int] = {}
    order: list[object] = []
    stack: list[tuple[object, bool]] = [
        (root, False) for root in reversed(tuple(roots))
    ]
    while stack:
        node, leaving = stack.pop()
        if type(node) not in allowed:
            raise TypeError(f"noncanonical table node: {type(node).__name__}")
        identity = id(node)
        color = colors.get(identity, unseen)
        if leaving:
            if color != active:
                raise ValueError("invalid certificate traversal state")
            colors[identity] = complete
            order.append(node)
            continue
        if color == complete:
            continue
        if color == active:
            raise ValueError("cyclic certificate object graph")
        colors[identity] = active
        stack.append((node, True))
        if allowed is CANONICAL_NODE_TYPES:
            child_values = [
                child for child in children(node) if type(child) in CANONICAL_NODE_TYPES
            ]
        else:
            child_values = list(_proof_children(cast(Pf, node)))
        stack.extend((child, False) for child in reversed(child_values))
    return tuple(order)


def _proof_children(proof: Pf) -> tuple[Pf, ...]:
    out: list[Pf] = []
    for spec in _PROOF_SCHEMAS[type(proof)]:
        value = getattr(proof, spec.name)
        if spec.kind == "proof":
            out.append(cast(Pf, value))
        elif spec.kind == "proof_tuple":
            out.extend(cast(tuple[Pf, ...], value))
    return tuple(out)


def _proof_syntax_roots(proofs: Iterable[Pf]) -> tuple[Node, ...]:
    out: list[Node] = []
    for proof in proofs:
        for spec in _PROOF_SCHEMAS[type(proof)]:
            value = getattr(proof, spec.name)
            if spec.kind == "syntax":
                out.append(cast(Node, value))
            elif spec.kind == "syntax_tuple":
                out.extend(cast(tuple[Node, ...], value))
    return tuple(out)


def _encode_entry(
    node: object,
    schema: tuple[_FieldSpec, ...],
    syntax_indices: dict[int, int],
    proof_indices: dict[int, int],
) -> bytes:
    out = bytearray(_string(type(node).__name__))
    out.extend(_uvarint(len(schema)))
    for spec in schema:
        value = getattr(node, spec.name)
        out.append(spec.marker)
        if spec.kind == "int":
            out.extend(_uvarint(cast(int, value)))
        elif spec.kind == "string":
            out.extend(_string(cast(str, value)))
        elif spec.kind == "syntax":
            out.extend(_uvarint(syntax_indices[id(value)]))
        elif spec.kind == "syntax_tuple":
            values = cast(tuple[Node, ...], value)
            out.extend(_uvarint(len(values)))
            for child in values:
                out.extend(_uvarint(syntax_indices[id(child)]))
        elif spec.kind == "proof":
            out.extend(_uvarint(proof_indices[id(value)]))
        elif spec.kind == "proof_tuple":
            values = cast(tuple[Pf, ...], value)
            out.extend(_uvarint(len(values)))
            for child in values:
                out.extend(_uvarint(proof_indices[id(child)]))
        else:
            raise AssertionError(f"unhandled certificate field kind: {spec.kind}")
    return bytes(out)


def _build_syntax_table(roots: Iterable[Node]) -> tuple[tuple[bytes, ...], dict[int, int]]:
    records: list[bytes] = []
    by_key: dict[bytes, int] = {}
    indices: dict[int, int] = {}
    for raw_node in _identity_postorder(roots, CANONICAL_NODE_TYPES):
        node = cast(Node, raw_node)
        record = _encode_entry(node, _SYNTAX_SCHEMAS[type(node)], indices, {})
        index = by_key.get(record)
        if index is None:
            index = len(records)
            records.append(record)
            by_key[record] = index
        indices[id(node)] = index
    return tuple(records), indices


def _standalone_syntax_bytes(root: Node) -> bytes:
    records, indices = _build_syntax_table((root,))
    return b"".join(
        (_uvarint(len(records)), *records, _uvarint(indices[id(root)]))
    )


def _build_proof_table(
    proof_order: tuple[Pf, ...], syntax_indices: dict[int, int]
) -> tuple[tuple[bytes, ...], dict[int, int]]:
    records: list[bytes] = []
    by_key: dict[bytes, int] = {}
    indices: dict[int, int] = {}
    for proof in proof_order:
        record = _encode_entry(
            proof,
            _PROOF_SCHEMAS[type(proof)],
            syntax_indices,
            indices,
        )
        index = by_key.get(record)
        if index is None:
            index = len(records)
            records.append(record)
            by_key[record] = index
        indices[id(proof)] = index
    return tuple(records), indices


def _validate_certificate_data(certificate: object) -> Certificate:
    if type(certificate) is not Certificate:
        raise TypeError("expected an exact Certificate")
    value = certificate
    if type(value.theory_key) is not str or not value.theory_key:
        raise TypeError("certificate theory key must be a nonempty exact str")
    if type(value.theory_fingerprint) is not bytes or len(value.theory_fingerprint) != 32:
        raise TypeError("certificate theory fingerprint must be exactly 32 bytes")
    if type(value.claim) is not Sequent:
        raise TypeError("certificate claim must be an exact Sequent")
    if type(value.claim.hyps) is not frozenset:
        raise TypeError("certificate claim hypotheses must be a frozenset")
    for hypothesis in value.claim.hyps:
        _require_root(hypothesis, _FORMULA_TYPES, "a claim hypothesis formula", TypeError)
        validate(hypothesis)
    _require_root(value.claim.concl, _FORMULA_TYPES, "a claim conclusion formula", TypeError)
    validate(value.claim.concl)
    _require_root(value.proof, CANONICAL_PROOF_TYPES, "a certificate proof", TypeError)
    validate_proof(value.proof)
    return value


def encode_certificate(certificate: Certificate) -> bytes:
    """Encode one inert certificate as canonical version-1 DAG bytes."""
    value = _validate_certificate_data(certificate)
    proof_order = cast(
        tuple[Pf, ...], _identity_postorder((value.proof,), CANONICAL_PROOF_TYPES)
    )
    hypotheses = tuple(
        sorted(value.claim.hyps, key=lambda formula: _standalone_syntax_bytes(formula))
    )
    syntax_roots = (
        *_proof_syntax_roots(proof_order),
        *hypotheses,
        value.claim.concl,
    )
    syntax_records, syntax_indices = _build_syntax_table(syntax_roots)
    proof_records, proof_indices = _build_proof_table(proof_order, syntax_indices)
    if not syntax_records or not proof_records:
        raise ValueError("certificate tables must be nonempty")

    return b"".join(
        (
            _MAGIC,
            _uvarint(_VERSION),
            _string(value.theory_key),
            value.theory_fingerprint,
            _uvarint(len(syntax_records)),
            *syntax_records,
            _uvarint(len(proof_records)),
            *proof_records,
            _uvarint(len(hypotheses)),
            *(_uvarint(syntax_indices[id(hypothesis)]) for hypothesis in hypotheses),
            _uvarint(syntax_indices[id(value.claim.concl)]),
            _uvarint(proof_indices[id(value.proof)]),
        )
    )


def _frame(payload: bytes) -> bytes:
    return _uvarint(len(payload)) + payload


def theory_fingerprint(theory: Theory) -> bytes:
    """Return the version-1 semantic SHA-256 fingerprint of an exact theory."""
    value = validate_theory(theory)
    signature = value.signature
    sorts = () if signature is None else tuple(sorted(signature.sorts, key=str.encode))
    functions = () if signature is None else tuple(
        sorted(signature.ranks, key=lambda rank: rank[0].encode("utf-8"))
    )
    relations = () if signature is None else tuple(
        sorted(signature.relations, key=lambda rank: rank[0].encode("utf-8"))
    )
    axiom_bytes = tuple(
        sorted(_standalone_syntax_bytes(axiom) for axiom in value.axioms)
    )

    preimage = bytearray(_frame(b"cold-start-theory-v1"))
    preimage.append(0x01)
    preimage.extend(_uvarint(len(sorts)))
    for sort in sorts:
        preimage.extend(_frame(sort.encode("utf-8")))
    preimage.append(0x02)
    preimage.extend(_uvarint(len(functions)))
    for name, args, result in functions:
        preimage.extend(_frame(name.encode("utf-8")))
        preimage.extend(_uvarint(len(args)))
        for sort in args:
            preimage.extend(_frame(sort.encode("utf-8")))
        preimage.extend(_frame(result.encode("utf-8")))
    preimage.append(0x03)
    preimage.extend(_uvarint(len(relations)))
    for name, args in relations:
        preimage.extend(_frame(name.encode("utf-8")))
        preimage.extend(_uvarint(len(args)))
        for sort in args:
            preimage.extend(_frame(sort.encode("utf-8")))
    preimage.append(0x04)
    preimage.extend(_uvarint(len(axiom_bytes)))
    for axiom in axiom_bytes:
        preimage.extend(_frame(axiom))
    preimage.append(0x05)
    if value.zero is None:
        preimage.append(0x00)
    else:
        preimage.append(0x01)
        preimage.extend(_frame(_standalone_syntax_bytes(value.zero)))
    preimage.append(0x06)
    if value.succ is None:
        preimage.append(0x00)
    else:
        preimage.append(0x01)
        preimage.extend(_frame(value.succ.encode("utf-8")))
    return sha256(preimage).digest()


def make_certificate(theory_key: str, theory: Theory, proof: Pf) -> Certificate:
    """Build an inert certificate whose claim is freshly derived by ``check``."""
    if type(theory_key) is not str or not theory_key:
        raise TypeError("certificate theory key must be a nonempty exact str")
    value = validate_theory(theory)
    claim = check(proof, value)
    return Certificate(theory_key, theory_fingerprint(value), claim, proof)


@dataclass(slots=True)
class _Reader:
    data: bytes
    limits: CertificateLimits
    position: int = 0
    edges: int = 0

    def __post_init__(self) -> None:
        if type(self.data) is not bytes:
            raise TypeError("certificate input must be exact bytes")
        if type(self.limits) is not CertificateLimits:
            raise TypeError("certificate limits must be exact CertificateLimits")
        if len(self.data) > self.limits.max_input_bytes:
            raise ValueError("certificate input bytes limit exceeded")

    def take(self, count: int) -> bytes:
        end = self.position + count
        if end > len(self.data):
            raise ValueError("truncated certificate")
        payload = self.data[self.position : end]
        self.position = end
        return payload

    def byte(self) -> int:
        return self.take(1)[0]

    def uvarint(self) -> int:
        value = 0
        shift = 0
        groups = 0
        while True:
            byte = self.byte()
            groups += 1
            value |= (byte & 0x7F) << shift
            if not byte & 0x80:
                if groups > 1 and byte == 0:
                    raise ValueError("nonminimal uvarint")
                return value
            shift += 7

    def string(self) -> str:
        size = self.uvarint()
        if size > self.limits.max_string_bytes:
            raise ValueError("certificate string bytes limit exceeded")
        try:
            return self.take(size).decode("utf-8", errors="strict")
        except UnicodeDecodeError as exc:
            raise ValueError("invalid certificate UTF-8") from exc

    def edge(self) -> None:
        self.edges += 1
        if self.edges > self.limits.max_edges:
            raise ValueError("certificate edges limit exceeded")

    def arity(self) -> int:
        value = self.uvarint()
        if value > self.limits.max_tuple_arity:
            raise ValueError("certificate tuple arity limit exceeded")
        return value


def _checked_ref(index: int, current: int, total: int, label: str) -> int:
    if index == current:
        raise ValueError(f"cyclic {label} reference")
    if index > current and index < total:
        raise ValueError(f"forward {label} reference")
    if index >= total:
        raise ValueError(f"{label} reference out of range")
    return index


def _read_entry(
    reader: _Reader,
    registry: dict[str, type],
    schemas: dict[type, tuple[_FieldSpec, ...]],
    syntax: list[Node],
    proofs: list[Pf],
    *,
    table: Literal["syntax", "proof"],
    current: int,
    total: int,
) -> tuple[object, bytes]:
    start = reader.position
    class_name = reader.string()
    node_type = registry.get(class_name)
    if node_type is None:
        raise ValueError(f"unknown {table} class: {class_name!r}")
    schema = schemas[node_type]
    field_count = reader.uvarint()
    if field_count != len(schema):
        raise ValueError(f"malformed field count for {class_name}")
    values: list[object] = []
    for spec in schema:
        marker = reader.byte()
        if marker not in _KNOWN_FIELD_TAGS:
            raise ValueError(f"unknown field tag 0x{marker:02x}")
        if marker != spec.marker:
            raise ValueError(f"field marker mismatch for {class_name}.{spec.name}")
        if spec.kind == "int":
            values.append(reader.uvarint())
        elif spec.kind == "string":
            values.append(reader.string())
        elif spec.kind == "syntax":
            reader.edge()
            index = reader.uvarint()
            if table == "syntax":
                index = _checked_ref(index, current, total, "syntax")
            elif index >= len(syntax):
                raise ValueError("syntax reference out of range")
            values.append(syntax[index])
        elif spec.kind == "syntax_tuple":
            arity = reader.arity()
            syntax_items: list[Node] = []
            for _ in range(arity):
                reader.edge()
                index = reader.uvarint()
                if table == "syntax":
                    index = _checked_ref(index, current, total, "syntax")
                elif index >= len(syntax):
                    raise ValueError("syntax reference out of range")
                syntax_items.append(syntax[index])
            values.append(tuple(syntax_items))
        elif spec.kind == "proof":
            reader.edge()
            index = _checked_ref(reader.uvarint(), current, total, "proof")
            values.append(proofs[index])
        elif spec.kind == "proof_tuple":
            arity = reader.arity()
            proof_items: list[Pf] = []
            for _ in range(arity):
                reader.edge()
                index = _checked_ref(reader.uvarint(), current, total, "proof")
                proof_items.append(proofs[index])
            values.append(tuple(proof_items))
        else:
            raise AssertionError(f"unhandled certificate field kind: {spec.kind}")
    try:
        node = node_type(*values)
    except (TypeError, ValueError) as exc:
        raise ValueError(f"malformed {class_name} field value: {exc}") from exc
    return node, reader.data[start : reader.position]


def _read_count(reader: _Reader, limit: int, label: str) -> int:
    count = reader.uvarint()
    if count > limit:
        raise ValueError(f"certificate {label} limit exceeded")
    if count == 0:
        raise ValueError(f"certificate {label} table is empty")
    return count


def decode_certificate(
    data: bytes,
    *,
    limits: CertificateLimits = DEFAULT_CERTIFICATE_LIMITS,
) -> Certificate:
    """Decode one canonical certificate under caller-lowerable I/O limits."""
    reader = _Reader(data, limits)
    if reader.take(len(_MAGIC)) != _MAGIC:
        raise ValueError("invalid certificate magic")
    version = reader.uvarint()
    if version != _VERSION:
        raise ValueError(f"unsupported certificate version: {version}")
    theory_key = reader.string()
    if not theory_key:
        raise ValueError("certificate theory key is empty")
    fingerprint = reader.take(32)

    syntax_count = _read_count(
        reader, limits.max_syntax_entries, "syntax entries"
    )
    syntax: list[Node] = []
    syntax_keys: set[bytes] = set()
    syntax_indices: dict[int, int] = {}
    for index in range(syntax_count):
        node, _raw_record = _read_entry(
            reader,
            _SYNTAX_REGISTRY,
            _SYNTAX_SCHEMAS,
            syntax,
            [],
            table="syntax",
            current=index,
            total=syntax_count,
        )
        typed_node = cast(Node, node)
        canonical_record = _encode_entry(
            typed_node,
            _SYNTAX_SCHEMAS[type(typed_node)],
            syntax_indices,
            {},
        )
        if canonical_record in syntax_keys:
            raise ValueError("duplicate syntax table entry")
        syntax_keys.add(canonical_record)
        syntax.append(typed_node)
        syntax_indices[id(typed_node)] = index

    proof_count = _read_count(reader, limits.max_proof_entries, "proof entries")
    proofs: list[Pf] = []
    proof_keys: set[bytes] = set()
    proof_indices: dict[int, int] = {}
    for index in range(proof_count):
        node, _raw_record = _read_entry(
            reader,
            _PROOF_REGISTRY,
            _PROOF_SCHEMAS,
            syntax,
            proofs,
            table="proof",
            current=index,
            total=proof_count,
        )
        proof = cast(Pf, node)
        canonical_record = _encode_entry(
            proof,
            _PROOF_SCHEMAS[type(proof)],
            syntax_indices,
            proof_indices,
        )
        if canonical_record in proof_keys:
            raise ValueError("duplicate proof table entry")
        proof_keys.add(canonical_record)
        proofs.append(proof)
        proof_indices[id(proof)] = index

    hypothesis_count = reader.uvarint()
    if hypothesis_count > limits.max_claim_hypotheses:
        raise ValueError("certificate claim hypotheses limit exceeded")
    hypotheses: list[Formula] = []
    for _ in range(hypothesis_count):
        reader.edge()
        index = reader.uvarint()
        if index >= len(syntax):
            raise ValueError("claim hypothesis reference out of range")
        formula = syntax[index]
        if type(formula) not in _FORMULA_TYPES:
            raise ValueError("claim hypothesis reference is not a formula")
        hypotheses.append(cast(Formula, formula))
    hypothesis_keys = [_standalone_syntax_bytes(value) for value in hypotheses]
    if len(hypothesis_keys) != len(set(hypothesis_keys)):
        raise ValueError("duplicate claim hypothesis")
    if hypothesis_keys != sorted(hypothesis_keys):
        raise ValueError("claim hypotheses are not sorted")

    reader.edge()
    conclusion_index = reader.uvarint()
    if conclusion_index >= len(syntax):
        raise ValueError("claim conclusion reference out of range")
    conclusion = syntax[conclusion_index]
    if type(conclusion) not in _FORMULA_TYPES:
        raise ValueError("claim conclusion reference is not a formula")
    reader.edge()
    root_index = reader.uvarint()
    if root_index >= len(proofs):
        raise ValueError("proof root reference out of range")
    if reader.position != len(data):
        raise ValueError("trailing certificate bytes")

    certificate = Certificate(
        theory_key,
        fingerprint,
        Sequent(frozenset(hypotheses), cast(Formula, conclusion)),
        proofs[root_index],
    )
    _validate_certificate_data(certificate)
    if encode_certificate(certificate) != data:
        raise ValueError("noncanonical certificate encoding")
    return certificate


__all__ = [
    "DEFAULT_CERTIFICATE_LIMITS",
    "CertificateLimits",
    "decode_certificate",
    "decode_formula",
    "decode_term",
    "encode_certificate",
    "encode_formula",
    "encode_term",
    "make_certificate",
    "theory_fingerprint",
]
