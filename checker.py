"""THE TRUSTED CORE.

`check(proof, theory)` re-derives a sequent from an inert proof term. This is
the only code whose correctness soundness depends on -- read it in full, it is
short. It accepts *data* (proof terms over syntax.py), not pre-made theorems,
so the in-process forgery holes that plague an opaque-Theorem design simply do
not apply: there is nothing to forge but a recipe, and a recipe that checks is
a proof.

Because its input is untrusted (possibly malformed, possibly deserialized from
elsewhere), `validate_proof` runs one up-front structural pass with EXACT-type
checks -- not isinstance -- since a hostile __eq__-overriding subclass is the
attack. Once that passes, `_derive` is pure logic and may trust `==`.
"""

from __future__ import annotations

from dataclasses import dataclass

import proof as P
from syntax import (
    Eq,
    Formula,
    Fun,
    Implies,
    formula_free_vars,
    formula_subst,
    validate_formula,
    validate_term,
)


@dataclass(frozen=True, slots=True)
class Sequent:
    """A derived judgement ``hyps |- conclusion``.

    Deliberately has NO construction guard. Holding a Sequent proves nothing --
    you can build any Sequent you like. Authority comes only from `check()`
    returning one without raising. That is the whole point of the De Bruijn
    design: trust the verifier, not the object.
    """

    hyps: frozenset  # frozenset[Formula]
    concl: Formula

    def __repr__(self) -> str:
        if self.hyps:
            ctx = ", ".join(sorted(map(repr, self.hyps)))
            return f"{ctx} |- {self.concl!r}"
        return f"|- {self.concl!r}"


@dataclass(frozen=True, slots=True)
class Theory:
    """A choice of axioms -- the mathematics we commit to, hence trusted.

    `axioms` are concrete formulas (with implicitly-universal free variables).
    `schemas` are recognizer predicates for axiom *schemas* (e.g. induction),
    each returning True for a formula that is a legitimate instance. The
    recognizers are part of the trusted base; keep them small and obvious.
    """

    axioms: frozenset  # frozenset[Formula]
    schemas: tuple = ()  # tuple[Callable[[Formula], bool], ...]

    def accepts(self, f: Formula) -> bool:
        return f in self.axioms or any(rec(f) for rec in self.schemas)


def validate_proof(pf: object) -> None:
    """Structural well-formedness: every node is a known proof term, every
    embedded term/formula/label is a genuine canonical node (exact type, so a
    hostile __eq__-overriding subclass is rejected). Run once, up front, so the
    derivation below can trust Python `==` and stay pure logic.
    """
    if isinstance(pf, P.Axiom):
        validate_formula(pf.formula)
    elif isinstance(pf, P.Assume):
        validate_formula(pf.formula)
    elif isinstance(pf, P.Refl):
        validate_term(pf.term)
    elif isinstance(pf, P.Sym):
        validate_proof(pf.sub)
    elif isinstance(pf, P.Trans):
        validate_proof(pf.left)
        validate_proof(pf.right)
    elif isinstance(pf, P.Cong):
        if type(pf.fun) is not str:
            raise TypeError("Cong.fun must be a genuine str")
        if type(pf.args) is not tuple:
            raise TypeError("Cong.args must be a tuple")
        for a in pf.args:
            validate_proof(a)
    elif isinstance(pf, P.MP):
        validate_proof(pf.imp)
        validate_proof(pf.ant)
    elif isinstance(pf, P.ImpIntro):
        validate_formula(pf.hyp)
        validate_proof(pf.body)
    elif isinstance(pf, P.Inst):
        if type(pf.var) is not str:
            raise TypeError("Inst.var must be a genuine str")
        validate_term(pf.term)
        validate_proof(pf.sub)
    else:
        raise TypeError(f"not a proof term: {pf!r}")


def check(pf: object, theory: Theory) -> Sequent:
    """Re-derive the sequent proved by `pf` under `theory`, or raise.

    Validates the proof's structure once, then derives. Raises TypeError for a
    malformed proof and ValueError for an invalid derivation step.
    """
    if not isinstance(theory, Theory):
        raise TypeError(f"not a theory: {theory!r}")
    validate_proof(pf)
    return _derive(pf, theory)


def _derive(pf: object, theory: Theory) -> Sequent:
    """The pure logic core. Assumes `pf` already passed validate_proof, so `==`
    on any term/formula here is honest and no input-type guards are needed --
    only the logical side-conditions of each rule.
    """
    if isinstance(pf, P.Axiom):
        if not theory.accepts(pf.formula):
            raise ValueError(f"not an axiom of this theory: {pf.formula!r}")
        return Sequent(frozenset(), pf.formula)

    if isinstance(pf, P.Assume):
        return Sequent(frozenset({pf.formula}), pf.formula)

    if isinstance(pf, P.Refl):
        return Sequent(frozenset(), Eq(pf.term, pf.term))

    if isinstance(pf, P.Sym):
        s = _derive(pf.sub, theory)
        if not isinstance(s.concl, Eq):
            raise ValueError(f"sym needs an equality, got {s.concl!r}")
        return Sequent(s.hyps, Eq(s.concl.rhs, s.concl.lhs))

    if isinstance(pf, P.Trans):
        a = _derive(pf.left, theory)
        b = _derive(pf.right, theory)
        if not isinstance(a.concl, Eq) or not isinstance(b.concl, Eq):
            raise ValueError("trans needs two equalities")
        if a.concl.rhs != b.concl.lhs:
            raise ValueError(
                f"trans: middle terms differ: {a.concl.rhs!r} vs {b.concl.lhs!r}"
            )
        return Sequent(a.hyps | b.hyps, Eq(a.concl.lhs, b.concl.rhs))

    if isinstance(pf, P.Cong):
        hyps: frozenset = frozenset()
        lhs, rhs = [], []
        for sub in pf.args:
            s = _derive(sub, theory)
            if not isinstance(s.concl, Eq):
                raise ValueError(f"cong needs equalities, got {s.concl!r}")
            hyps |= s.hyps
            lhs.append(s.concl.lhs)
            rhs.append(s.concl.rhs)
        return Sequent(hyps, Eq(Fun(pf.fun, tuple(lhs)), Fun(pf.fun, tuple(rhs))))

    if isinstance(pf, P.MP):
        imp = _derive(pf.imp, theory)
        ant = _derive(pf.ant, theory)
        if not isinstance(imp.concl, Implies):
            raise ValueError(f"mp needs an implication, got {imp.concl!r}")
        if imp.concl.ant != ant.concl:
            raise ValueError(
                f"mp: antecedent mismatch:\n  needs: {imp.concl.ant!r}\n  has:   {ant.concl!r}"
            )
        return Sequent(imp.hyps | ant.hyps, imp.concl.con)

    if isinstance(pf, P.ImpIntro):
        body = _derive(pf.body, theory)
        return Sequent(body.hyps - {pf.hyp}, Implies(pf.hyp, body.concl))

    if isinstance(pf, P.Inst):
        s = _derive(pf.sub, theory)
        for h in s.hyps:
            if pf.var in formula_free_vars(h):
                raise ValueError(
                    f"cannot instantiate {pf.var!r}: free in hypothesis {h!r}"
                )
        return Sequent(s.hyps, formula_subst(s.concl, pf.var, pf.term))

    raise TypeError(f"not a proof term: {pf!r}")  # unreachable after validate_proof


__all__ = ["Sequent", "Theory", "check", "validate_proof"]
