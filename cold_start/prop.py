"""Derived propositional connectives -- the UNTRUSTED sugar over →/⊥.

The object language (syntax.py) deliberately stops at implication, absurdity,
equality, and the quantifiers; conjunction is the classical encoding

    And(A, B)  :=  ¬(A → ¬B)

and this module derives its rules as proof-term combinators. Introduction is
intuitionistic; the eliminations are classical (RAA). Like tactics.py, nothing
here is trusted: each combinator emits an inert `Pf`, and `checker.check`
remains the only judge. A combinator's hypotheses flow through honestly -- pack
two assumptions and both surface in the sequent.

Disjunction (`Or(A,B) := ¬A → B`) belongs here too when a theorem first needs
it; it is deliberately absent until then."""

from __future__ import annotations

from .proof import MP, RAA, Assume, ExFalso, ImpIntro, Pf
from .syntax import Formula, Implies, Not


def And(a: Formula, b: Formula) -> Formula:  # noqa: N802 -- reads as the connective
    """The classical conjunction: ¬(A → ¬B)."""
    return Not(Implies(a, Not(b)))


def and_intro(a: Formula, b: Formula, pa: Pf, pb: Pf) -> Pf:
    """From proofs of A and of B, a proof of And(A, B).

    Assume A → ¬B; modus ponens twice lands ⊥; discharge. Intuitionistic."""
    h = Implies(a, Not(b))
    return ImpIntro(h, MP(MP(Assume(h), pa), pb))


def and_left(a: Formula, b: Formula, pab: Pf) -> Pf:
    """From a proof of And(A, B), a proof of A -- by reductio: under ¬A the
    implication A → ¬B holds vacuously (ex falso), contradicting And(A, B)."""
    vacuous = ImpIntro(a, ExFalso(MP(Assume(Not(a)), Assume(a)), Not(b)))
    return RAA(a, MP(pab, vacuous))


def and_right(a: Formula, b: Formula, pab: Pf) -> Pf:
    """From a proof of And(A, B), a proof of B -- by reductio: under ¬B the
    implication A → ¬B holds constantly, contradicting And(A, B)."""
    constant = ImpIntro(a, Assume(Not(b)))
    return RAA(b, MP(pab, constant))


__all__ = ["And", "and_intro", "and_left", "and_right"]
