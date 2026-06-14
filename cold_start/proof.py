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
    Formula,
    Term,
    formula_from_dict,
    formula_to_dict,
    term_from_dict,
    term_to_dict,
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


# ---------------------------------------------------------------------------
# Serialization
# ---------------------------------------------------------------------------


def to_dict(p: Pf) -> dict:
    if isinstance(p, Axiom):
        return {"k": "Axiom", "formula": formula_to_dict(p.formula)}
    if isinstance(p, Assume):
        return {"k": "Assume", "formula": formula_to_dict(p.formula)}
    if isinstance(p, Refl):
        return {"k": "Refl", "term": term_to_dict(p.term)}
    if isinstance(p, Sym):
        return {"k": "Sym", "sub": to_dict(p.sub)}
    if isinstance(p, Trans):
        return {"k": "Trans", "left": to_dict(p.left), "right": to_dict(p.right)}
    if isinstance(p, Cong):
        return {"k": "Cong", "fun": p.fun, "args": [to_dict(a) for a in p.args]}
    if isinstance(p, MP):
        return {"k": "MP", "imp": to_dict(p.imp), "ant": to_dict(p.ant)}
    if isinstance(p, ImpIntro):
        return {"k": "ImpIntro", "hyp": formula_to_dict(p.hyp), "body": to_dict(p.body)}
    if isinstance(p, Inst):
        return {"k": "Inst", "sub": to_dict(p.sub), "var": p.var, "term": term_to_dict(p.term)}
    if isinstance(p, Induct):
        return {
            "k": "Induct",
            "var": p.var,
            "pred": formula_to_dict(p.pred),
            "base": to_dict(p.base),
            "step": to_dict(p.step),
        }
    raise TypeError(f"not a proof term: {p!r}")


def from_dict(d: object) -> Pf:
    """Rebuild a Pf from untrusted data, validating structure as we go."""
    if not isinstance(d, dict) or "k" not in d:
        raise ValueError(f"not a proof node: {d!r}")
    kind = d["k"]
    if kind == "Axiom":
        return Axiom(formula_from_dict(d["formula"]))
    if kind == "Assume":
        return Assume(formula_from_dict(d["formula"]))
    if kind == "Refl":
        return Refl(term_from_dict(d["term"]))
    if kind == "Sym":
        return Sym(from_dict(d["sub"]))
    if kind == "Trans":
        return Trans(from_dict(d["left"]), from_dict(d["right"]))
    if kind == "Cong":
        fun, args = d["fun"], d["args"]
        if not isinstance(fun, str) or not isinstance(args, list):
            raise ValueError("malformed Cong node")
        return Cong(fun, tuple(from_dict(a) for a in args))
    if kind == "MP":
        return MP(from_dict(d["imp"]), from_dict(d["ant"]))
    if kind == "ImpIntro":
        return ImpIntro(formula_from_dict(d["hyp"]), from_dict(d["body"]))
    if kind == "Inst":
        var = d["var"]
        if not isinstance(var, str):
            raise ValueError("Inst.var must be a string")
        return Inst(from_dict(d["sub"]), var, term_from_dict(d["term"]))
    if kind == "Induct":
        var = d["var"]
        if not isinstance(var, str):
            raise ValueError("Induct.var must be a string")
        return Induct(var, formula_from_dict(d["pred"]), from_dict(d["base"]), from_dict(d["step"]))
    raise ValueError(f"unknown proof kind: {kind!r}")


def to_json(p: Pf, *, indent: int | None = None) -> str:
    return json.dumps(to_dict(p), indent=indent)


def from_json(s: str) -> Pf:
    return from_dict(json.loads(s))
