"""The derived judgement `hyps |- conclusion`.

A result value, not a proof step: `proof.py`'s inert rule data never mentions a
sequent, and `checker.py` alone builds one, by deriving it. The judgement gets
its own module because everything downstream of derivation -- `checker.py`,
`theory.py`, `certificate.py`, `codec.py`, `verify.py`, the Lean export --
needs to name the checker's result without importing the checker.

A `Sequent` is inert: holding one proves nothing -- authority comes only from
`check()` returning one without raising (the De Bruijn design: trust the
verifier, not the object).
"""

from __future__ import annotations

from dataclasses import dataclass

from .syntax import Formula, SignatureProtocol
from .work import WorkMeter


@dataclass(frozen=True, slots=True)
class Sequent:
    """A derived judgement ``hyps |- conclusion``.

    Deliberately has NO construction guard. Holding a Sequent proves nothing --
    you can build any Sequent you like. Authority comes only from `check()`
    returning one without raising.
    """

    hyps: frozenset[Formula]
    concl: Formula

    def __repr__(self) -> str:
        if self.hyps:
            ctx = ", ".join(sorted(map(repr, self.hyps)))
            return f"{ctx} |- {self.concl!r}"
        return f"|- {self.concl!r}"

    def sort_check(
        self, sig: SignatureProtocol, meter: WorkMeter | None = None
    ) -> None:
        """The rule invariant: every formula is structurally well-sorted, and a
        variable name has one sort across all hypotheses and the conclusion
        together (substitution targets names, so a name at two sorts would let
        instantiation rewrite positions of the wrong sort).

        Structural well-sortedness is the polymorphic `formula.sort_check(sig)`;
        this method just gathers the free `(name, sort)` pairs across the whole
        sequent and enforces consistency. `sig` is a many-sorted Signature."""
        self.concl.sort_check(sig, meter=meter)
        pairs = set(self.concl.free_var_sorts(meter))
        for h in self.hyps:
            if meter is not None:
                meter.consume("hypothesis_elements")
            h.sort_check(sig, meter=meter)
            discovered = h.free_var_sorts(meter)
            if meter is not None:
                meter.consume("hypothesis_elements", len(discovered))
            pairs |= discovered
        seen: dict[str, str] = {}
        for name, sort in pairs:
            prev = seen.get(name)
            if prev is not None and prev != sort:
                raise ValueError(f"variable {name!r} used at sorts {prev!r} and {sort!r}")
            seen[name] = sort
