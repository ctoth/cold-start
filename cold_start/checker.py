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

from dataclasses import dataclass, field
from functools import lru_cache

from . import proof as P
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
    forall,
    instantiate,
    validate,
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


@dataclass(frozen=True)
class Signature:
    """A many-sorted signature: the declared sort names and each function
    symbol's rank (argument sorts -> result sort). When a `Theory` carries one,
    the checker rejects ill-sorted terms and cross-sort instantiation.

    `ranks` stays a (hashable) tuple so a Signature can be the lru_cache key on
    `sort_of`; an O(1) lookup dict is derived once and excluded from eq/hash.
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


@lru_cache(maxsize=8192)
def sort_of(t: object, sig: Signature) -> str:
    """The sort of a well-sorted term, or raise ValueError if ill-sorted.

    Memoized: `sort_of` is a pure function of (term, signature) -- both are
    immutable and hashable -- so each term's sort is computed once and reused.
    This is the SOUND form of "cache well-sortedness": the verifier memoizes its
    own computation. It never trusts a sort tag carried on an input term, which
    would be a forgeable token (and would be wrong anyway, since sort is
    relative to the signature). Exceptions are not cached, so ill-sorted terms
    still raise on every check.
    """
    if type(t) is Var:
        if t.sort not in sig.sorts:
            raise ValueError(f"variable {t!r} has undeclared sort {t.sort!r}")
        return t.sort
    if type(t) is Fun:
        r = sig.rank(t.name)
        if r is None:
            raise ValueError(f"undeclared function symbol {t.name!r}")
        arg_sorts, result = r
        if len(t.args) != len(arg_sorts):
            raise ValueError(f"{t.name!r} expects {len(arg_sorts)} args, got {len(t.args)}")
        for a, expected in zip(t.args, arg_sorts, strict=True):
            actual = sort_of(a, sig)
            if actual != expected:
                raise ValueError(f"{t.name!r} arg has sort {actual!r}, expected {expected!r}")
        return result
    raise TypeError(f"not a term: {t!r}")


def _sort_structure(f: object, sig: Signature) -> None:
    """Structural well-sortedness: each equality is between same-sort terms."""
    if type(f) is Eq:
        ls, rs = sort_of(f.lhs, sig), sort_of(f.rhs, sig)
        if ls != rs:
            raise ValueError(f"equality across sorts: {ls!r} = {rs!r} in {f!r}")
    elif type(f) is Implies:
        _sort_structure(f.ant, sig)
        _sort_structure(f.con, sig)
    elif type(f) is Bottom:
        pass  # the formula constant carries no sort
    else:
        raise TypeError(f"not a formula: {f!r}")


def _collect_consistent(obj: object, acc: dict) -> None:
    """Accumulate variable name -> sort, raising if a name appears at two sorts.

    Because substitution targets variables by name, a name must denote a single
    sort everywhere it occurs; otherwise instantiating it would rewrite
    positions of a different sort. This makes name-based substitution sound.
    """
    if type(obj) is Var:
        prev = acc.get(obj.name)
        if prev is not None and prev != obj.sort:
            raise ValueError(
                f"variable {obj.name!r} used at sorts {prev!r} and {obj.sort!r}"
            )
        acc[obj.name] = obj.sort
    elif type(obj) is Fun:
        for a in obj.args:
            _collect_consistent(a, acc)
    elif type(obj) is Eq:
        _collect_consistent(obj.lhs, acc)
        _collect_consistent(obj.rhs, acc)
    elif type(obj) is Implies:
        _collect_consistent(obj.ant, acc)
        _collect_consistent(obj.con, acc)


def sort_check_formula(f: object, sig: Signature) -> None:
    """A single formula is well-sorted and uses each variable name at one sort."""
    _sort_structure(f, sig)
    _collect_consistent(f, {})


def _sort_check_sequent(seq: Sequent, sig: Signature) -> None:
    """The rule invariant: every derived sequent is well-sorted, and a variable
    name has one sort across all of its hypotheses and conclusion together."""
    acc: dict = {}
    _sort_structure(seq.concl, sig)
    _collect_consistent(seq.concl, acc)
    for h in seq.hyps:
        _sort_structure(h, sig)
        _collect_consistent(h, acc)


def _sorts_of_var(obj: object, name: str, out: set) -> None:
    """Collect the sorts at which variable `name` occurs in a term/formula."""
    if type(obj) is Var:
        if obj.name == name:
            out.add(obj.sort)
    elif type(obj) is Fun:
        for a in obj.args:
            _sorts_of_var(a, name, out)
    elif type(obj) is Eq:
        _sorts_of_var(obj.lhs, name, out)
        _sorts_of_var(obj.rhs, name, out)
    elif type(obj) is Implies:
        _sorts_of_var(obj.ant, name, out)
        _sorts_of_var(obj.con, name, out)


def validate_proof(pf: object) -> None:
    """Structural well-formedness: every node is a known proof term, every
    embedded term/formula/label is a genuine canonical node (exact type, so a
    hostile __eq__-overriding subclass is rejected). Run once, up front, so the
    derivation below can trust Python `==` and stay pure logic.
    """
    if type(pf) is P.Axiom:
        validate(pf.formula)
    elif type(pf) is P.Assume:
        validate(pf.formula)
    elif type(pf) is P.Refl:
        validate(pf.term)
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
        validate(pf.hyp)
        validate_proof(pf.body)
    elif type(pf) is P.Inst:
        if type(pf.var) is not str:
            raise TypeError("Inst.var must be a genuine str")
        validate(pf.term)
        validate_proof(pf.sub)
    elif type(pf) is P.Induct:
        if type(pf.var) is not str:
            raise TypeError("Induct.var must be a genuine str")
        validate(pf.pred)
        validate_proof(pf.base)
        validate_proof(pf.step)
    elif type(pf) is P.ExFalso:
        validate(pf.concl)
        validate_proof(pf.sub)
    elif type(pf) is P.RAA:
        validate(pf.goal)
        validate_proof(pf.sub)
    elif type(pf) is P.ForallElim:
        validate(pf.term)
        validate_proof(pf.sub)
    elif type(pf) is P.ForallIntro:
        if type(pf.var) is not str or type(pf.sort) is not str:
            raise TypeError("ForallIntro.var and .sort must be genuine strs")
        validate_proof(pf.sub)
    elif type(pf) is P.ExistsIntro:
        validate(pf.claim)
        validate(pf.witness)
        validate_proof(pf.sub)
    elif type(pf) is P.ExistsElim:
        if type(pf.eigenvar) is not str:
            raise TypeError("ExistsElim.eigenvar must be a genuine str")
        validate_proof(pf.sub_ex)
        validate_proof(pf.sub_use)
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
    """Derive a sequent, then enforce the sort invariant on the result.

    Sort-checking is a *rule invariant*: instead of trusting each rule to
    preserve well-sortedness, we re-check every sequent a rule produces (when
    the theory is sorted) -- structural well-sortedness plus "one sort per
    variable name across the whole sequent". Single-sorted theories (signature
    None) skip it entirely, so their behaviour is byte-for-byte unchanged.
    """
    seq = _derive_rule(pf, theory)
    if theory.signature is not None:
        _sort_check_sequent(seq, theory.signature)
    return seq


def _derive_rule(pf: object, theory: Theory) -> Sequent:
    """The pure logic core. Assumes `pf` already passed validate_proof, so `==`
    on any term/formula here is honest. The `_derive` wrapper handles sorts; the
    only sort logic here is the Inst cross-sort guard, which needs the variable.
    """
    sig = theory.signature

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
            if pf.var in h.free_vars():
                raise ValueError(
                    f"cannot instantiate {pf.var!r}: free in hypothesis {h!r}"
                )
        if sig is not None:
            # the replacement's sort must match the variable's declared sort --
            # instantiating x:K with a V-term is a sort error even when the
            # resulting formula happens to be well-sorted.
            var_sorts: set = set()
            _sorts_of_var(s.concl, pf.var, var_sorts)
            if var_sorts:
                term_sort = sort_of(pf.term, sig)
                if term_sort not in var_sorts:
                    raise ValueError(
                        f"cannot instantiate {pf.var!r}:{var_sorts} with a "
                        f"term of sort {term_sort!r}"
                    )
        return Sequent(s.hyps, s.concl.subst(pf.var, pf.term))

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
        validate(theory.zero)  # the trusted theory's base term must be canonical
        base = _derive(pf.base, theory)
        step = _derive(pf.step, theory)
        pred_zero = pf.pred.subst(pf.var, theory.zero)
        pred_succ = pf.pred.subst(pf.var, Fun(theory.succ, (Var(pf.var),)))
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
            if pf.var in h.free_vars():
                raise ValueError(
                    f"induction variable {pf.var!r} is free in hypothesis {h!r}"
                )
        return Sequent(hyps, pf.pred)

    if type(pf) is P.ExFalso:
        # ex falso quodlibet: a proof of Bottom yields any (well-formed) formula.
        s = _derive(pf.sub, theory)
        if type(s.concl) is not Bottom:
            raise ValueError(f"ex falso needs a proof of Bottom, got {s.concl!r}")
        return Sequent(s.hyps, pf.concl)

    if type(pf) is P.RAA:
        # classical reductio: assuming Not(goal) leads to Bottom, so goal holds.
        s = _derive(pf.sub, theory)
        if type(s.concl) is not Bottom:
            raise ValueError(f"reductio needs a proof of Bottom, got {s.concl!r}")
        return Sequent(s.hyps - {Not(pf.goal)}, pf.goal)

    if type(pf) is P.ForallElim:
        # from `forall x. body` conclude body[x := term] (capture-avoiding).
        s = _derive(pf.sub, theory)
        if type(s.concl) is not Forall:
            raise ValueError(f"forall-elim needs a universal, got {s.concl!r}")
        if sig is not None and s.concl.sort:
            t_sort = sort_of(pf.term, sig)
            if t_sort != s.concl.sort:
                raise ValueError(
                    f"cannot instantiate forall :{s.concl.sort!r} with a term of sort {t_sort!r}"
                )
        return Sequent(s.hyps, instantiate(s.concl, pf.term))

    if type(pf) is P.ForallIntro:
        # generalize a schematic variable, provided it is not constrained by a
        # hypothesis (the eigenvariable condition).
        s = _derive(pf.sub, theory)
        for h in s.hyps:
            if pf.var in h.free_vars():
                raise ValueError(
                    f"cannot generalize {pf.var!r}: free in hypothesis {h!r}"
                )
        return Sequent(s.hyps, forall(pf.var, pf.sort, s.concl))

    if type(pf) is P.ExistsIntro:
        # from a witness proof of body[x := witness], conclude `exists x. body`.
        if type(pf.claim) is not Exists:
            raise ValueError(f"exists-intro needs an existential claim, got {pf.claim!r}")
        s = _derive(pf.sub, theory)
        expected = instantiate(pf.claim, pf.witness)
        if s.concl != expected:
            raise ValueError(
                f"exists-intro: sub-proof must prove {expected!r}, got {s.concl!r}"
            )
        if sig is not None and pf.claim.sort:
            t_sort = sort_of(pf.witness, sig)
            if t_sort != pf.claim.sort:
                raise ValueError(
                    f"exists-intro witness has sort {t_sort!r}, expected {pf.claim.sort!r}"
                )
        return Sequent(s.hyps, pf.claim)

    if type(pf) is P.ExistsElim:
        # from `exists x. body` and a proof of phi assuming body[x := eigenvar],
        # conclude phi -- provided the eigenvariable does not escape.
        s_ex = _derive(pf.sub_ex, theory)
        if type(s_ex.concl) is not Exists:
            raise ValueError(f"exists-elim needs an existential, got {s_ex.concl!r}")
        instance = instantiate(s_ex.concl, Var(pf.eigenvar, s_ex.concl.sort))
        s_use = _derive(pf.sub_use, theory)
        if instance not in s_use.hyps:
            raise ValueError(
                f"exists-elim: the using proof must assume the instance {instance!r}"
            )
        phi = s_use.concl
        result_hyps = s_ex.hyps | (s_use.hyps - {instance})
        if pf.eigenvar in phi.free_vars():
            raise ValueError(
                f"exists-elim eigenvariable {pf.eigenvar!r} escapes into the conclusion {phi!r}"
            )
        for h in result_hyps:
            if pf.eigenvar in h.free_vars():
                raise ValueError(
                    f"exists-elim eigenvariable {pf.eigenvar!r} is free in hypothesis {h!r}"
                )
        return Sequent(result_hyps, phi)

    raise TypeError(f"not a proof term: {pf!r}")  # unreachable after validate_proof


__all__ = ["Sequent", "Theory", "check", "validate_proof"]
