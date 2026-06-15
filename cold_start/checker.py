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

from dataclasses import dataclass, field
from typing import cast

from .proof import Pf, validate_proof
from .sequent import Sequent
from .syntax import Formula, Term


@dataclass(frozen=True)
class Signature:
    """A many-sorted signature: the declared sort names and each function
    symbol's rank (argument sorts -> result sort). When a `Theory` carries one,
    the checker rejects ill-sorted terms and cross-sort instantiation.

    `ranks` stays a (hashable) tuple; an O(1) lookup dict is derived once and
    excluded from eq/hash so a Signature stays hashable.
    """

    sorts: frozenset  # frozenset[str]
    ranks: tuple  # tuple[(name: str, arg_sorts: tuple[str, ...], result: str), ...]
    _by_name: dict = field(default_factory=dict, init=False, compare=False, repr=False)

    def __post_init__(self) -> None:
        object.__setattr__(self, "_by_name", {n: (args, res) for n, args, res in self.ranks})

    def rank(self, name: str):
        return self._by_name.get(name)


@dataclass(frozen=True, slots=True)
class Theory:
    """A choice of axioms -- the mathematics we commit to, hence trusted.

    `axioms` are concrete formulas (with implicitly-universal free variables).
    `zero` and `succ` name the theory's induction structure: the base term and
    the successor function symbol used by the first-class `Induct` rule. A
    theory without them (both None) admits no induction.

    `signature` (optional) makes the theory many-sorted: when present, the
    checker sort-checks every term and forbids instantiating a variable with a
    term of a different sort. When None, no sort-checking happens at all.

    NB: induction is a *rule*, not an axiom formula. Asserting the schema
    `P[0] -> ((P -> P[Sx]) -> P)` as an axiom is UNSOUND here, because under the
    implicit-universal reading its free `x` quantifies over the whole
    implication rather than only the step -- which lets `P(n):=n=0`, x:=1 derive
    `1 = 0`. The `Induct` rule keeps the step quantified correctly and never
    exposes that formula as a standalone theorem.
    """

    axioms: frozenset  # frozenset[Formula]
    zero: Term | None = None
    succ: str | None = None  # successor function symbol
    signature: Signature | None = None

    def accepts(self, f: Formula) -> bool:
        return f in self.axioms


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
    if type(theory) is not Theory:
        raise TypeError(f"not a theory: {theory!r}")
    validate_proof(pf)  # exact-type gate; after this pf is a genuine Pf tree
    return cast(Pf, pf).derive(theory)


__all__ = ["Sequent", "Signature", "Theory", "check", "sort_check_formula", "validate_proof"]
