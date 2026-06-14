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

from . import proof as P
from .syntax import (
    Eq,
    Formula,
    Fun,
    Implies,
    Term,
    Var,
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
    `zero` and `succ` name the theory's induction structure: the base term and
    the successor function symbol used by the first-class `Induct` rule. A
    theory without them (both None) admits no induction.

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

    def accepts(self, f: Formula) -> bool:
        return f in self.axioms


def validate_proof(pf: object) -> None:
    """Structural well-formedness: every node is a known proof term, every
    embedded term/formula/label is a genuine canonical node (exact type, so a
    hostile __eq__-overriding subclass is rejected). Run once, up front, so the
    derivation below can trust Python `==` and stay pure logic.
    """
    if type(pf) is P.Axiom:
        validate_formula(pf.formula)
    elif type(pf) is P.Assume:
        validate_formula(pf.formula)
    elif type(pf) is P.Refl:
        validate_term(pf.term)
    elif type(pf) is P.Sym:
        validate_proof(pf.sub)
    elif type(pf) is P.Trans:
        validate_proof(pf.left)
        validate_proof(pf.right)
    elif type(pf) is P.Cong:
        if type(pf.fun) is not str:
            raise TypeError("Cong.fun must be a genuine str")
        if type(pf.args) is not tuple:
            raise TypeError("Cong.args must be a tuple")
        for a in pf.args:
            validate_proof(a)
    elif type(pf) is P.MP:
        validate_proof(pf.imp)
        validate_proof(pf.ant)
    elif type(pf) is P.ImpIntro:
        validate_formula(pf.hyp)
        validate_proof(pf.body)
    elif type(pf) is P.Inst:
        if type(pf.var) is not str:
            raise TypeError("Inst.var must be a genuine str")
        validate_term(pf.term)
        validate_proof(pf.sub)
    elif type(pf) is P.Induct:
        if type(pf.var) is not str:
            raise TypeError("Induct.var must be a genuine str")
        validate_formula(pf.pred)
        validate_proof(pf.base)
        validate_proof(pf.step)
    else:
        raise TypeError(f"not a proof term: {pf!r}")


def check(pf: object, theory: object) -> Sequent:
    """Re-derive the sequent proved by `pf` under `theory`, or raise.

    Validates the proof's structure once, then derives. Raises TypeError for a
    malformed proof and ValueError for an invalid derivation step. Inputs are
    typed `object`: the trusted checker validates them, it does not trust the
    caller's annotations.
    """
    if type(theory) is not Theory:
        raise TypeError(f"not a theory: {theory!r}")
    validate_proof(pf)
    return _derive(pf, theory)


def _derive(pf: object, theory: Theory) -> Sequent:
    """The pure logic core. Assumes `pf` already passed validate_proof, so `==`
    on any term/formula here is honest and no input-type guards are needed --
    only the logical side-conditions of each rule.
    """
    if type(pf) is P.Axiom:
        if not theory.accepts(pf.formula):
            raise ValueError(f"not an axiom of this theory: {pf.formula!r}")
        return Sequent(frozenset(), pf.formula)

    if type(pf) is P.Assume:
        return Sequent(frozenset({pf.formula}), pf.formula)

    if type(pf) is P.Refl:
        return Sequent(frozenset(), Eq(pf.term, pf.term))

    if type(pf) is P.Sym:
        s = _derive(pf.sub, theory)
        if type(s.concl) is not Eq:
            raise ValueError(f"sym needs an equality, got {s.concl!r}")
        return Sequent(s.hyps, Eq(s.concl.rhs, s.concl.lhs))

    if type(pf) is P.Trans:
        a = _derive(pf.left, theory)
        b = _derive(pf.right, theory)
        if type(a.concl) is not Eq or type(b.concl) is not Eq:
            raise ValueError("trans needs two equalities")
        if a.concl.rhs != b.concl.lhs:
            raise ValueError(
                f"trans: middle terms differ: {a.concl.rhs!r} vs {b.concl.lhs!r}"
            )
        return Sequent(a.hyps | b.hyps, Eq(a.concl.lhs, b.concl.rhs))

    if type(pf) is P.Cong:
        hyps: frozenset = frozenset()
        lhs, rhs = [], []
        for sub in pf.args:
            s = _derive(sub, theory)
            if type(s.concl) is not Eq:
                raise ValueError(f"cong needs equalities, got {s.concl!r}")
            hyps |= s.hyps
            lhs.append(s.concl.lhs)
            rhs.append(s.concl.rhs)
        return Sequent(hyps, Eq(Fun(pf.fun, tuple(lhs)), Fun(pf.fun, tuple(rhs))))

    if type(pf) is P.MP:
        imp = _derive(pf.imp, theory)
        ant = _derive(pf.ant, theory)
        if type(imp.concl) is not Implies:
            raise ValueError(f"mp needs an implication, got {imp.concl!r}")
        if imp.concl.ant != ant.concl:
            raise ValueError(
                f"mp: antecedent mismatch:\n  needs: {imp.concl.ant!r}\n  has:   {ant.concl!r}"
            )
        return Sequent(imp.hyps | ant.hyps, imp.concl.con)

    if type(pf) is P.ImpIntro:
        body = _derive(pf.body, theory)
        return Sequent(body.hyps - {pf.hyp}, Implies(pf.hyp, body.concl))

    if type(pf) is P.Inst:
        s = _derive(pf.sub, theory)
        for h in s.hyps:
            if pf.var in formula_free_vars(h):
                raise ValueError(
                    f"cannot instantiate {pf.var!r}: free in hypothesis {h!r}"
                )
        return Sequent(s.hyps, formula_subst(s.concl, pf.var, pf.term))

    if type(pf) is P.Induct:
        # Mathematical induction as a first-class rule (NOT an axiom formula):
        #   base : G |- pred[var := 0]
        #   step : D |- pred -> pred[var := S var]
        #   var not free in G u D
        #   ---------------------------------------
        #   G u D |- pred
        # The side condition is what keeps the step universally quantified over
        # `var`; without it (or by citing the schema as an axiom) you can derive
        # 1 = 0. See Theory's docstring.
        if theory.zero is None or type(theory.succ) is not str:
            raise ValueError("theory defines no induction principle (no zero/succ)")
        validate_term(theory.zero)  # the trusted theory's base term must be canonical
        base = _derive(pf.base, theory)
        step = _derive(pf.step, theory)
        pred_zero = formula_subst(pf.pred, pf.var, theory.zero)
        pred_succ = formula_subst(pf.pred, pf.var, Fun(theory.succ, (Var(pf.var),)))
        if base.concl != pred_zero:
            raise ValueError(
                f"induction base must prove {pred_zero!r}, got {base.concl!r}"
            )
        if step.concl != Implies(pf.pred, pred_succ):
            raise ValueError(
                f"induction step must prove {Implies(pf.pred, pred_succ)!r}, "
                f"got {step.concl!r}"
            )
        hyps = base.hyps | step.hyps
        for h in hyps:
            if pf.var in formula_free_vars(h):
                raise ValueError(
                    f"induction variable {pf.var!r} is free in hypothesis {h!r}"
                )
        return Sequent(hyps, pf.pred)

    raise TypeError(f"not a proof term: {pf!r}")  # unreachable after validate_proof


__all__ = ["Sequent", "Theory", "check", "validate_proof"]
