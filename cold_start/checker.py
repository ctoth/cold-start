"""THE TRUSTED CORE.

`check(proof, theory)` re-derives a sequent from an inert proof term. This is
the only code whose soundness everything depends on -- read it in full, it is
short. It accepts *data* (proof terms over syntax.py), not pre-made theorems,
so the in-process forgery holes that plague an opaque-Theorem design simply do
not apply: there is nothing to forge but a recipe, and a recipe that checks is
a proof.

Because its input is untrusted (possibly malformed, possibly deserialized from
elsewhere), `validate_proof` (in proof.py) runs one up-front structural pass
with EXACT-type checks -- not isinstance -- since a hostile __eq__-overriding
subclass is the attack. Once that passes, each proof term's own `derive` method
is pure logic and may trust `==`. The per-rule logic lives on the proof terms as
polymorphic methods; trust is the gate plus those methods plus each theory's
axioms.
"""

from __future__ import annotations

from typing import cast

from .proof import Pf, validate_proof
from .sequent import Sequent
from .syntax import Formula
from .theory import Signature, validate_theory


def sort_check_formula(f: Formula, sig: Signature) -> None:
    """A single formula is well-sorted and uses each variable name at one sort --
    exactly the rule invariant on the trivial sequent `|- f`."""
    Sequent(frozenset(), f).sort_check(sig)


def check(pf: object, theory: object) -> Sequent:
    """Re-derive the sequent proved by `pf` under `theory`, or raise.

    Validates the proof's structure once (the exact-type gate), then derives.
    Raises TypeError for a malformed proof and ValueError for an invalid
    derivation step. Inputs are typed `object`: the trusted checker validates
    them, it does not trust the caller's annotations.

    `check` is TOTAL: it returns a `Sequent` or raises `TypeError`/`ValueError`,
    nothing else. Every step it takes is iterative -- validation, derivation,
    substitution, sort-checking, and even `==`/`hash` on the syntax nodes walk a
    heap agenda, not the call stack -- so an arbitrarily deep proof or term is
    checked (or cleanly rejected) without a `RecursionError`. The only bound is
    memory, which already held the input.
    """
    checked_theory = validate_theory(theory)
    validate_proof(pf)  # exact-type gate; after this pf is a genuine Pf tree
    return cast(Pf, pf).derive(checked_theory)


__all__ = ["check", "sort_check_formula", "validate_proof"]
