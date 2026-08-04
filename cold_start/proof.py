"""Proof terms: the inert recipe an (untrusted) prover emits -- and the trusted
checking logic, carried as polymorphic methods on those terms.

A proof term is a tree of rule applications. As *data* it asserts nothing: you
can build any nonsense `Pf` you like, and the external codec can serialize it so
a proof can be written to disk and re-checked by a separate process. Authority
comes only from `check()` (in checker.py) driving `derive()` and getting a
`Sequent` back.

Why the checking lives here as methods (`_validate`, `_derive_rule`/`derive`)
rather than a type-switch in the checker: a rule's logic is an operation over the
proof tree, so it dispatches on the node's class -- that is what polymorphism is
for. Soundness is not weakened by this, because `validate_proof` is an EXACT-type
gate run first: a hostile `__eq__`-overriding subclass is rejected before any of
its methods could run, so by the time `derive` executes every node is a genuine
canonical proof term and `==` is honest. The gate is the one non-polymorphic
piece (a method could be overridden by exactly the subclass it must reject).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import cast

from .sequent import Sequent
from .syntax import (
    Bottom,
    Eq,
    Exists,
    Forall,
    Formula,
    Fun,
    Implies,
    Not,
    Term,
    Var,
    children,
    forall,
    instantiate,
    validate,
)


class Pf:
    """Base class for proof terms (inert data) and home of the trusted checking
    methods. `validate_proof` gates on exact type before any of these run."""

    __slots__ = ()

    def derive(self, theory) -> Sequent:
        """Re-derive this proof's sequent under `theory`, enforcing the sort
        invariant on each result when the theory is many-sorted. Assumes
        `validate_proof` has already run, so `==` on embedded nodes is honest.

        Iterative post-order: every sub-proof's sequent is computed bottom-up into
        a `id -> Sequent` map, so each rule reads its children's sequents by lookup
        instead of recursing. A proof nested thousands deep is checked without
        touching the call stack."""
        order: list = []
        stack: list = [self]
        while stack:
            p = stack.pop()
            order.append(p)
            stack.extend(c for c in children(p) if isinstance(c, Pf))
        sig = theory.signature
        results: dict = {}

        def derived(child: Pf) -> Sequent:  # a child's already-computed sequent
            return results[id(child)]

        for p in reversed(order):  # children precede parents, so lookups are ready
            seq = p._derive_rule(theory, derived)
            if sig is not None:
                seq.sort_check(sig)
            results[id(p)] = seq
        return results[id(self)]

    def _derive_rule(self, theory, derived) -> Sequent:  # overridden by every concrete rule
        raise TypeError(f"not a derivable proof term: {self!r}")  # unreachable post-validate

    def _validate(self) -> tuple:  # overridden by every concrete rule
        """Validate this node's own embedded terms/formulas/labels and return its
        sub-proof agenda (NOT recursing), so `validate_proof` walks iteratively."""
        raise TypeError(f"not a proof term: {self!r}")  # unreachable: gate checks exact type


@dataclass(frozen=True, slots=True)
class Axiom(Pf):
    formula: Formula  # must be accepted by the theory when checked

    def _validate(self) -> tuple:
        validate(self.formula)
        return ()

    def _derive_rule(self, theory, derived) -> Sequent:
        if not theory.accepts(self.formula):
            raise ValueError(f"not an axiom of this theory: {self.formula!r}")
        return Sequent(frozenset(), self.formula)


@dataclass(frozen=True, slots=True)
class Assume(Pf):
    formula: Formula

    def _validate(self) -> tuple:
        validate(self.formula)
        return ()

    def _derive_rule(self, theory, derived) -> Sequent:
        return Sequent(frozenset({self.formula}), self.formula)


@dataclass(frozen=True, slots=True)
class Refl(Pf):
    term: Term

    def _validate(self) -> tuple:
        validate(self.term)
        return ()

    def _derive_rule(self, theory, derived) -> Sequent:
        return Sequent(frozenset(), Eq(self.term, self.term))


@dataclass(frozen=True, slots=True)
class Sym(Pf):
    sub: Pf

    def _validate(self) -> tuple:
        return (self.sub,)

    def _derive_rule(self, theory, derived) -> Sequent:
        s = derived(self.sub)
        if type(s.concl) is not Eq:
            raise ValueError(f"sym needs an equality, got {s.concl!r}")
        return Sequent(s.hyps, Eq(s.concl.rhs, s.concl.lhs))


@dataclass(frozen=True, slots=True)
class Trans(Pf):
    left: Pf
    right: Pf

    def _validate(self) -> tuple:
        return (self.left, self.right)

    def _derive_rule(self, theory, derived) -> Sequent:
        a = derived(self.left)
        b = derived(self.right)
        if type(a.concl) is not Eq or type(b.concl) is not Eq:
            raise ValueError("trans needs two equalities")
        if a.concl.rhs != b.concl.lhs:
            raise ValueError(f"trans: middle terms differ: {a.concl.rhs!r} vs {b.concl.lhs!r}")
        return Sequent(a.hyps | b.hyps, Eq(a.concl.lhs, b.concl.rhs))


@dataclass(frozen=True, slots=True)
class Cong(Pf):
    fun: str
    args: tuple  # tuple[Pf, ...] -- one sub-proof of an equality per slot

    def _validate(self) -> tuple:
        if type(self.fun) is not str:
            raise TypeError("Cong.fun must be a genuine str")
        if type(self.args) is not tuple:
            raise TypeError("Cong.args must be a tuple")
        return self.args

    def _derive_rule(self, theory, derived) -> Sequent:
        hyps: frozenset = frozenset()
        lhs, rhs = [], []
        for sub in self.args:
            s = derived(sub)
            if type(s.concl) is not Eq:
                raise ValueError(f"cong needs equalities, got {s.concl!r}")
            hyps |= s.hyps
            lhs.append(s.concl.lhs)
            rhs.append(s.concl.rhs)
        return Sequent(hyps, Eq(Fun(self.fun, tuple(lhs)), Fun(self.fun, tuple(rhs))))


@dataclass(frozen=True, slots=True)
class MP(Pf):
    imp: Pf
    ant: Pf

    def _validate(self) -> tuple:
        return (self.imp, self.ant)

    def _derive_rule(self, theory, derived) -> Sequent:
        imp = derived(self.imp)
        ant = derived(self.ant)
        if type(imp.concl) is not Implies:
            raise ValueError(f"mp needs an implication, got {imp.concl!r}")
        if imp.concl.ant != ant.concl:
            raise ValueError(
                f"mp: antecedent mismatch:\n  needs: {imp.concl.ant!r}\n  has:   {ant.concl!r}"
            )
        return Sequent(imp.hyps | ant.hyps, imp.concl.con)


@dataclass(frozen=True, slots=True)
class ImpIntro(Pf):
    hyp: Formula
    body: Pf

    def _validate(self) -> tuple:
        validate(self.hyp)
        return (self.body,)

    def _derive_rule(self, theory, derived) -> Sequent:
        body = derived(self.body)
        return Sequent(body.hyps - {self.hyp}, Implies(self.hyp, body.concl))


@dataclass(frozen=True, slots=True)
class Inst(Pf):
    sub: Pf
    var: str
    term: Term

    def _validate(self) -> tuple:
        if type(self.var) is not str:
            raise TypeError("Inst.var must be a genuine str")
        validate(self.term)
        return (self.sub,)

    def _derive_rule(self, theory, derived) -> Sequent:
        s = derived(self.sub)
        for h in s.hyps:
            if self.var in h.free_vars():
                raise ValueError(f"cannot instantiate {self.var!r}: free in hypothesis {h!r}")
        sig = theory.signature
        if sig is not None:
            # the replacement's sort must match the variable's declared sort --
            # instantiating x:K with a V-term is a sort error even when the
            # resulting formula happens to be well-sorted.
            var_sorts = {sort for (name, sort) in s.concl.free_var_sorts() if name == self.var}
            if var_sorts:
                term_sort = self.term.sort_of(sig)
                if term_sort not in var_sorts:
                    raise ValueError(
                        f"cannot instantiate {self.var!r}:{var_sorts} "
                        f"with a term of sort {term_sort!r}"
                    )
        return Sequent(s.hyps, s.concl.subst(self.var, self.term))


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

    def _validate(self) -> tuple:
        if type(self.var) is not str:
            raise TypeError("Induct.var must be a genuine str")
        validate(self.pred)
        return (self.base, self.step)

    def _derive_rule(self, theory, derived) -> Sequent:
        # base : G |- pred[var := 0];  step : D |- pred -> pred[var := S var];
        # var not free in G u D  =>  G u D |- pred. The side condition keeps the
        # step universally quantified over `var`; without it you can derive 1 = 0.
        if theory.zero is None or type(theory.succ) is not str:
            raise ValueError("theory defines no induction principle (no zero/succ)")
        validate(theory.zero)  # the trusted theory's base term must be canonical
        base = derived(self.base)
        step = derived(self.step)
        pred_zero = self.pred.subst(self.var, theory.zero)
        pred_succ = self.pred.subst(self.var, Fun(theory.succ, (Var(self.var),)))
        if base.concl != pred_zero:
            raise ValueError(f"induction base must prove {pred_zero!r}, got {base.concl!r}")
        if step.concl != Implies(self.pred, pred_succ):
            raise ValueError(
                f"induction step must prove {Implies(self.pred, pred_succ)!r}, got {step.concl!r}"
            )
        hyps = base.hyps | step.hyps
        for h in hyps:
            if self.var in h.free_vars():
                raise ValueError(f"induction variable {self.var!r} is free in hypothesis {h!r}")
        return Sequent(hyps, self.pred)


@dataclass(frozen=True, slots=True)
class ExFalso(Pf):
    """Ex falso quodlibet: from a proof of Bottom, conclude any formula."""

    sub: Pf
    concl: Formula

    def _validate(self) -> tuple:
        validate(self.concl)
        return (self.sub,)

    def _derive_rule(self, theory, derived) -> Sequent:
        s = derived(self.sub)
        if type(s.concl) is not Bottom:
            raise ValueError(f"ex falso needs a proof of Bottom, got {s.concl!r}")
        return Sequent(s.hyps, self.concl)


@dataclass(frozen=True, slots=True)
class RAA(Pf):
    """Classical reductio: from a proof of Bottom under the hypothesis Not(goal),
    discharge that hypothesis and conclude goal."""

    goal: Formula
    sub: Pf

    def _validate(self) -> tuple:
        validate(self.goal)
        return (self.sub,)

    def _derive_rule(self, theory, derived) -> Sequent:
        s = derived(self.sub)
        if type(s.concl) is not Bottom:
            raise ValueError(f"reductio needs a proof of Bottom, got {s.concl!r}")
        return Sequent(s.hyps - {Not(self.goal)}, self.goal)


@dataclass(frozen=True, slots=True)
class ForallElim(Pf):
    """Universal instantiation: from a proof of `forall x. body`, conclude
    `body[x := term]` (capture-avoiding)."""

    sub: Pf
    term: Term

    def _validate(self) -> tuple:
        validate(self.term)
        return (self.sub,)

    def _derive_rule(self, theory, derived) -> Sequent:
        s = derived(self.sub)
        if type(s.concl) is not Forall:
            raise ValueError(f"forall-elim needs a universal, got {s.concl!r}")
        sig = theory.signature
        if sig is not None and s.concl.sort:
            t_sort = self.term.sort_of(sig)
            if t_sort != s.concl.sort:
                raise ValueError(
                    f"cannot instantiate forall :{s.concl.sort!r} with a term of sort {t_sort!r}"
                )
        return Sequent(s.hyps, instantiate(s.concl, self.term))


@dataclass(frozen=True, slots=True)
class ForallIntro(Pf):
    """Universal generalization: from a proof of `body` in which `var` is not
    free in any hypothesis (the eigenvariable condition), conclude
    `forall var. body`."""

    var: str
    sort: str
    sub: Pf

    def _validate(self) -> tuple:
        if type(self.var) is not str or type(self.sort) is not str:
            raise TypeError("ForallIntro.var and .sort must be genuine strs")
        return (self.sub,)

    def _derive_rule(self, theory, derived) -> Sequent:
        s = derived(self.sub)
        for h in s.hyps:
            if self.var in h.free_vars():
                raise ValueError(f"cannot generalize {self.var!r}: free in hypothesis {h!r}")
        return Sequent(s.hyps, forall(self.var, self.sort, s.concl))


@dataclass(frozen=True, slots=True)
class ExistsIntro(Pf):
    """Existential introduction: from a proof of `body[var := witness]`, conclude
    the existential `claim` (an Exists formula)."""

    claim: Formula
    witness: Term
    sub: Pf

    def _validate(self) -> tuple:
        validate(self.claim)
        validate(self.witness)
        return (self.sub,)

    def _derive_rule(self, theory, derived) -> Sequent:
        if type(self.claim) is not Exists:
            raise ValueError(f"exists-intro needs an existential claim, got {self.claim!r}")
        s = derived(self.sub)
        expected = instantiate(self.claim, self.witness)
        if s.concl != expected:
            raise ValueError(f"exists-intro: sub-proof must prove {expected!r}, got {s.concl!r}")
        sig = theory.signature
        if sig is not None and self.claim.sort:
            t_sort = self.witness.sort_of(sig)
            if t_sort != self.claim.sort:
                raise ValueError(
                    f"exists-intro witness has sort {t_sort!r}, expected {self.claim.sort!r}"
                )
        return Sequent(s.hyps, self.claim)


@dataclass(frozen=True, slots=True)
class ExistsElim(Pf):
    """Existential elimination: from a proof of `exists x. body` and a proof of
    `phi` that assumes `body[x := eigenvar]`, conclude `phi` -- provided the
    eigenvariable does not escape (not free in `phi` or any remaining
    hypothesis)."""

    eigenvar: str
    sub_ex: Pf
    sub_use: Pf

    def _validate(self) -> tuple:
        if type(self.eigenvar) is not str:
            raise TypeError("ExistsElim.eigenvar must be a genuine str")
        return (self.sub_ex, self.sub_use)

    def _derive_rule(self, theory, derived) -> Sequent:
        s_ex = derived(self.sub_ex)
        if type(s_ex.concl) is not Exists:
            raise ValueError(f"exists-elim needs an existential, got {s_ex.concl!r}")
        instance = instantiate(s_ex.concl, Var(self.eigenvar, s_ex.concl.sort))
        s_use = derived(self.sub_use)
        if instance not in s_use.hyps:
            raise ValueError(f"exists-elim: the using proof must assume the instance {instance!r}")
        phi = s_use.concl
        result_hyps = s_ex.hyps | (s_use.hyps - {instance})
        if self.eigenvar in phi.free_vars():
            raise ValueError(
                f"exists-elim eigenvariable {self.eigenvar!r} escapes into the conclusion {phi!r}"
            )
        for h in result_hyps:
            if self.eigenvar in h.free_vars():
                raise ValueError(
                    f"exists-elim eigenvariable {self.eigenvar!r} is free in hypothesis {h!r}"
                )
        return Sequent(result_hyps, phi)


# ---------------------------------------------------------------------------
# The trust gate
# ---------------------------------------------------------------------------

CANONICAL_PROOF_TYPES: frozenset[type] = frozenset(
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


def validate_proof(pf: object) -> None:
    """Structural well-formedness gate, run once up front. Rejects anything whose
    EXACT type is not a known proof term -- a hostile `__eq__`-overriding subclass
    is the attack, and a method could be overridden by exactly that subclass, so
    the gate is exact-type, not polymorphic. Each node's `_validate` checks its own
    embedded terms/formulas/labels and returns its sub-proof agenda; the gate
    re-confirms every sub-proof's exact type as it is popped. After this, `derive`
    may trust `==`.

    Iterative: the agenda is a heap list, so a proof nested thousands deep is
    validated without recursion."""
    stack: list = [pf]
    while stack:
        p = stack.pop()
        if type(p) not in CANONICAL_PROOF_TYPES:
            raise TypeError(f"not a proof term: {p!r}")
        stack.extend(cast(Pf, p)._validate())
