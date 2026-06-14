"""Proof terms: the inert recipe an (untrusted) prover emits.

A proof term is a tree of rule applications. It is *data*, not a theorem -- it
asserts nothing until checker.check() re-derives a sequent from it. Proof terms
are serializable to JSON, so a proof can be written to disk and verified by a
separate process that trusts only checker.py.

This module is NOT trusted: a `Pf` is just a description. Building a nonsense
Pf is fine; the checker will reject it.
"""

from __future__ import annotations

import json
from dataclasses import dataclass

from .syntax import (
    SYNTAX_REGISTRY,
    Formula,
    Term,
    decode_node,
    encode_node,
)


class Pf:
    """Base class for proof terms."""

    __slots__ = ()


@dataclass(frozen=True, slots=True)
class Axiom(Pf):
    formula: Formula  # must be accepted by the theory when checked


@dataclass(frozen=True, slots=True)
class Assume(Pf):
    formula: Formula


@dataclass(frozen=True, slots=True)
class Refl(Pf):
    term: Term


@dataclass(frozen=True, slots=True)
class Sym(Pf):
    sub: Pf


@dataclass(frozen=True, slots=True)
class Trans(Pf):
    left: Pf
    right: Pf


@dataclass(frozen=True, slots=True)
class Cong(Pf):
    fun: str
    args: tuple  # tuple[Pf, ...] -- one sub-proof of an equality per slot


@dataclass(frozen=True, slots=True)
class MP(Pf):
    imp: Pf
    ant: Pf


@dataclass(frozen=True, slots=True)
class ImpIntro(Pf):
    hyp: Formula
    body: Pf


@dataclass(frozen=True, slots=True)
class Inst(Pf):
    sub: Pf
    var: str
    term: Term


@dataclass(frozen=True, slots=True)
class Induct(Pf):
    """Mathematical induction on `var` over predicate `pred`, with sub-proofs
    of the base (`pred[var:=0]`) and step (`pred -> pred[var:=S var]`). A
    first-class rule, NOT an axiom formula -- the checker enforces the side
    condition that `var` is not free in the sub-proofs' hypotheses."""

    var: str
    pred: Formula
    base: Pf
    step: Pf


@dataclass(frozen=True, slots=True)
class ExFalso(Pf):
    """Ex falso quodlibet: from a proof of Bottom, conclude any formula."""

    sub: Pf
    concl: Formula


@dataclass(frozen=True, slots=True)
class RAA(Pf):
    """Classical reductio: from a proof of Bottom under the hypothesis Not(goal),
    discharge that hypothesis and conclude goal."""

    goal: Formula
    sub: Pf


@dataclass(frozen=True, slots=True)
class ForallElim(Pf):
    """Universal instantiation: from a proof of `forall x. body`, conclude
    `body[x := term]` (capture-avoiding)."""

    sub: Pf
    term: Term


@dataclass(frozen=True, slots=True)
class ForallIntro(Pf):
    """Universal generalization: from a proof of `body` in which `var` is not
    free in any hypothesis (the eigenvariable condition), conclude
    `forall var. body`."""

    var: str
    sort: str
    sub: Pf


@dataclass(frozen=True, slots=True)
class ExistsIntro(Pf):
    """Existential introduction: from a proof of `body[var := witness]`, conclude
    the existential `claim` (an Exists formula)."""

    claim: Formula
    witness: Term
    sub: Pf


@dataclass(frozen=True, slots=True)
class ExistsElim(Pf):
    """Existential elimination: from a proof of `exists x. body` and a proof of
    `phi` that assumes `body[x := eigenvar]`, conclude `phi` -- provided the
    eigenvariable does not escape (not free in `phi` or any remaining
    hypothesis)."""

    eigenvar: str
    sub_ex: Pf
    sub_use: Pf


# ---------------------------------------------------------------------------
# Serialization
# ---------------------------------------------------------------------------


# Reflection-based, like the syntax layer: the registry is every node class, so
# a new proof rule needs no serialization code -- only its dataclass definition.
_PROOF_REGISTRY = {
    **SYNTAX_REGISTRY,
    **{
        c.__name__: c
        for c in (
            Axiom, Assume, Refl, Sym, Trans, Cong, MP, ImpIntro, Inst, Induct,
            ExFalso, RAA, ForallElim, ForallIntro, ExistsIntro, ExistsElim,
        )
    },
}


def to_dict(p: Pf) -> dict:
    return encode_node(p)


def from_dict(d: object) -> Pf:
    node = decode_node(d, _PROOF_REGISTRY)
    if not isinstance(node, Pf):
        raise ValueError(f"expected a proof term, got {type(node).__name__}")
    return node


def to_json(p: Pf, *, indent: int | None = None) -> str:
    return json.dumps(to_dict(p), indent=indent)


def from_json(s: str) -> Pf:
    return from_dict(json.loads(s))
