"""Inert proof-term data emitted by untrusted provers.

These dataclasses describe rule applications but perform no validation and
derive no sequents.  All authority lives in :mod:`cold_start.checker`, whose
exact-type gate and exhaustive rule dispatch consume these values.
"""

from __future__ import annotations

from dataclasses import dataclass

from .syntax import Formula, Term


class Pf:
    """Marker base class for inert proof terms."""

    __slots__ = ()


@dataclass(frozen=True, slots=True)
class Axiom(Pf):
    formula: Formula


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
    args: tuple[Pf, ...]


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
    """Induction on ``var`` with proofs of the base and successor step."""

    var: str
    pred: Formula
    base: Pf
    step: Pf


@dataclass(frozen=True, slots=True)
class ExFalso(Pf):
    sub: Pf
    concl: Formula


@dataclass(frozen=True, slots=True)
class RAA(Pf):
    goal: Formula
    sub: Pf


@dataclass(frozen=True, slots=True)
class ForallElim(Pf):
    sub: Pf
    term: Term


@dataclass(frozen=True, slots=True)
class ForallIntro(Pf):
    var: str
    sort: str
    sub: Pf


@dataclass(frozen=True, slots=True)
class ExistsIntro(Pf):
    claim: Formula
    witness: Term
    sub: Pf


@dataclass(frozen=True, slots=True)
class ExistsElim(Pf):
    eigenvar: str
    sub_ex: Pf
    sub_use: Pf


CANONICAL_PROOF_TYPES: frozenset[type[Pf]] = frozenset(
    {
        Axiom,
        Assume,
        Refl,
        Sym,
        Trans,
        Cong,
        MP,
        ImpIntro,
        Inst,
        Induct,
        ExFalso,
        RAA,
        ForallElim,
        ForallIntro,
        ExistsIntro,
        ExistsElim,
    }
)
