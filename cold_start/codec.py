"""Untrusted Hamblin wire encoding for syntax and proof trees.

The trusted core owns canonical data types and validation. This downstream
adapter builds its decode registry from those owner sets, validates complete
structures before returning them, and never participates in checking.
"""

from __future__ import annotations

from collections.abc import Collection
from typing import cast

import hamblin

from .checker import validate_proof
from .proof import CANONICAL_PROOF_TYPES, Pf
from .syntax import CANONICAL_NODE_TYPES, BVar, Formula, Term, children, validate

_TERM_TYPES = frozenset(cls for cls in CANONICAL_NODE_TYPES if issubclass(cls, Term))
_FORMULA_TYPES = frozenset(cls for cls in CANONICAL_NODE_TYPES if issubclass(cls, Formula))


def _build_registry(
    syntax_types: Collection[type],
    proof_types: Collection[type],
) -> tuple[dict[str, type], dict[str, type]]:
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

    combined = (*syntax_set, *proof_set)
    names = [proof_type.__name__ for proof_type in combined]
    if len(names) != len(set(names)):
        raise ValueError("duplicate canonical codec type name")
    syntax_registry = {node_type.__name__: node_type for node_type in syntax_set}
    return syntax_registry, {
        **syntax_registry,
        **{proof_type.__name__: proof_type for proof_type in proof_set},
    }


_SYNTAX_REGISTRY, _PROOF_REGISTRY = _build_registry(
    CANONICAL_NODE_TYPES,
    CANONICAL_PROOF_TYPES,
)


def _require_root(
    value: object,
    kinds: Collection[type[object]],
    label: str,
    error: type[Exception],
) -> None:
    if type(value) not in kinds:
        raise error(f"expected {label}, got {type(value).__name__}")


def _open_term_depth(term: Term) -> int:
    """Return the smallest binder depth that closes an open term fragment."""
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
    """Validate and encode one canonical term."""
    _require_root(term, _TERM_TYPES, "a term", TypeError)
    validate(term, _open_term_depth(term))
    return hamblin.encode(term)


def decode_term(data: bytes) -> Term:
    """Decode and validate one canonical term from untrusted bytes."""
    node = hamblin.decode(data, _SYNTAX_REGISTRY)
    _require_root(node, _TERM_TYPES, "a term", ValueError)
    term = cast(Term, node)
    validate(term, _open_term_depth(term))
    return term


def encode_formula(formula: Formula) -> bytes:
    """Validate and encode one canonical formula."""
    _require_root(formula, _FORMULA_TYPES, "a formula", TypeError)
    validate(formula)
    return hamblin.encode(formula)


def decode_formula(data: bytes) -> Formula:
    """Decode and validate one canonical formula from untrusted bytes."""
    node = hamblin.decode(data, _SYNTAX_REGISTRY)
    _require_root(node, _FORMULA_TYPES, "a formula", ValueError)
    validate(node)
    return cast(Formula, node)


def encode_proof(proof: Pf) -> bytes:
    """Validate and encode one canonical proof tree."""
    _require_root(proof, CANONICAL_PROOF_TYPES, "a proof term", TypeError)
    validate_proof(proof)
    return hamblin.encode(proof)


def decode_proof(data: bytes) -> Pf:
    """Decode and validate one canonical proof tree from untrusted bytes."""
    node = hamblin.decode(data, _PROOF_REGISTRY)
    _require_root(node, CANONICAL_PROOF_TYPES, "a proof term", ValueError)
    validate_proof(node)
    return cast(Pf, node)


__all__ = [
    "decode_formula",
    "decode_proof",
    "decode_term",
    "encode_formula",
    "encode_proof",
    "encode_term",
]
