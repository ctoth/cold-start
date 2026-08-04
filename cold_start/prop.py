"""Derived propositional connectives -- the UNTRUSTED sugar over →/⊥.

The object language (syntax.py) deliberately stops at implication, absurdity,
equality, and the quantifiers; conjunction is the classical encoding

    And(A, B)  :=  ¬(A → ¬B)

and this module derives its rules as proof-term combinators. Introduction is
intuitionistic; the eliminations are classical (RAA). Like tactics.py, nothing
here is trusted: each combinator emits an inert `Pf`, and `checker.check`
remains the only judge. A combinator's hypotheses flow through honestly -- pack
two assumptions and both surface in the sequent.

Disjunction and biconditional use their standard classical encodings too. The
constructors accept n-ary And/Or calls for readable source transcriptions; the
binary proof combinators remain the small derived kernel used by proofs."""

from __future__ import annotations

from .proof import MP, RAA, Assume, ExFalso, ImpIntro, Pf
from .syntax import Formula, Implies, Not


def And(first: Formula, *rest: Formula) -> Formula:  # noqa: N802 -- connective
    """Classical conjunction, right-associated for three or more operands."""
    operands = (first, *rest)
    result = operands[-1]
    for formula in reversed(operands[:-1]):
        result = Not(Implies(formula, Not(result)))
    return result


def Or(first: Formula, *rest: Formula) -> Formula:  # noqa: N802 -- connective
    """Classical disjunction, right-associated for three or more operands."""
    operands = (first, *rest)
    result = operands[-1]
    for formula in reversed(operands[:-1]):
        result = Implies(Not(formula), result)
    return result


def Iff(left: Formula, right: Formula) -> Formula:  # noqa: N802 -- connective
    """Biconditional as the conjunction of its two implications."""
    return And(Implies(left, right), Implies(right, left))


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


__all__ = ["And", "Iff", "Or", "and_intro", "and_left", "and_right"]
