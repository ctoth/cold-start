"""cold-start: number theory from nothing, via a De Bruijn proof checker.

Public surface: build proof terms (proof.*), choose a theory (peano.PEANO),
and `check(proof, theory)` re-derives the sequent. Trust lives only in
`checker` + each theory's axioms.
"""

from __future__ import annotations

from .checker import Sequent, Theory, check, validate_proof
from .peano import PEANO, ZERO, S, add, induction, numeral
from .proof import (
    MP,
    Assume,
    Axiom,
    Cong,
    ImpIntro,
    Inst,
    Pf,
    Refl,
    Sym,
    Trans,
    from_json,
    to_json,
)
from .syntax import Eq, Formula, Fun, Implies, Term, Var

__all__ = [
    # language
    "Term", "Var", "Fun", "Formula", "Eq", "Implies",
    # proof terms
    "Pf", "Axiom", "Assume", "Refl", "Sym", "Trans", "Cong", "MP", "ImpIntro", "Inst",
    "to_json", "from_json",
    # checker
    "Sequent", "Theory", "check", "validate_proof",
    # peano
    "PEANO", "ZERO", "S", "add", "numeral", "induction",
]
