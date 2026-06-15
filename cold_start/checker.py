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

from collections.abc import Callable
from dataclasses import dataclass, field

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


# Sort-checking is structural, so it lives on the nodes as polymorphic methods
# (`term.sort_of(sig, scope)`, `formula.sort_check(sig, scope)`, `node.free_var_sorts()`
# in syntax.py) -- the same treatment as `free_vars`/`subst`, and safe because every
# node here already passed `validate`. The checker only assembles those results.


def _check_var_sort_consistency(pairs) -> None:
    """A variable *name* must denote a single sort everywhere it occurs: substitution
    targets names, so a name at two sorts would let instantiation rewrite positions
    of the wrong sort. `pairs` is a set of free `(name, sort)` pairs."""
    seen: dict = {}
    for name, sort in pairs:
        prev = seen.get(name)
        if prev is not None and prev != sort:
            raise ValueError(f"variable {name!r} used at sorts {prev!r} and {sort!r}")
        seen[name] = sort


def sort_check_formula(f: Formula, sig: Signature) -> None:
    """A single formula is well-sorted and uses each variable name at one sort."""
    f.sort_check(sig)
    _check_var_sort_consistency(f.free_var_sorts())


def _sort_check_sequent(seq: Sequent, sig: Signature) -> None:
    """The rule invariant: every derived sequent is well-sorted, and a variable name
    has one sort across all of its hypotheses and conclusion together."""
    seq.concl.sort_check(sig)
    pairs = set(seq.concl.free_var_sorts())
    for h in seq.hyps:
        h.sort_check(sig)
        pairs |= h.free_var_sorts()
    _check_var_sort_consistency(pairs)


# Per-rule structural validators, keyed by EXACT proof type below. Each checks
# that its node's embedded terms/formulas/labels are genuine canonical nodes and
# recurses into sub-proofs. Like `syntax.validate`, this is a trust gate, so it
# dispatches on exact type (a hostile subclass is rejected by being absent from
# the table) rather than polymorphically (a method could be the attack).


def _vp_axiom(pf: P.Axiom) -> None:
    validate(pf.formula)


def _vp_assume(pf: P.Assume) -> None:
    validate(pf.formula)


def _vp_refl(pf: P.Refl) -> None:
    validate(pf.term)


def _vp_sym(pf: P.Sym) -> None:
    validate_proof(pf.sub)


def _vp_trans(pf: P.Trans) -> None:
    validate_proof(pf.left)
    validate_proof(pf.right)


def _vp_cong(pf: P.Cong) -> None:
    if type(pf.fun) is not str:
        raise TypeError("Cong.fun must be a genuine str")
    if type(pf.args) is not tuple:
        raise TypeError("Cong.args must be a tuple")
    for a in pf.args:
        validate_proof(a)


def _vp_mp(pf: P.MP) -> None:
    validate_proof(pf.imp)
    validate_proof(pf.ant)


def _vp_impintro(pf: P.ImpIntro) -> None:
    validate(pf.hyp)
    validate_proof(pf.body)


def _vp_inst(pf: P.Inst) -> None:
    if type(pf.var) is not str:
        raise TypeError("Inst.var must be a genuine str")
    validate(pf.term)
    validate_proof(pf.sub)


def _vp_induct(pf: P.Induct) -> None:
    if type(pf.var) is not str:
        raise TypeError("Induct.var must be a genuine str")
    validate(pf.pred)
    validate_proof(pf.base)
    validate_proof(pf.step)


def _vp_exfalso(pf: P.ExFalso) -> None:
    validate(pf.concl)
    validate_proof(pf.sub)


def _vp_raa(pf: P.RAA) -> None:
    validate(pf.goal)
    validate_proof(pf.sub)


def _vp_forallelim(pf: P.ForallElim) -> None:
    validate(pf.term)
    validate_proof(pf.sub)


def _vp_forallintro(pf: P.ForallIntro) -> None:
    if type(pf.var) is not str or type(pf.sort) is not str:
        raise TypeError("ForallIntro.var and .sort must be genuine strs")
    validate_proof(pf.sub)


def _vp_existsintro(pf: P.ExistsIntro) -> None:
    validate(pf.claim)
    validate(pf.witness)
    validate_proof(pf.sub)


def _vp_existselim(pf: P.ExistsElim) -> None:
    if type(pf.eigenvar) is not str:
        raise TypeError("ExistsElim.eigenvar must be a genuine str")
    validate_proof(pf.sub_ex)
    validate_proof(pf.sub_use)


_VALIDATE_PROOF: dict[type, Callable[..., None]] = {
    P.Axiom: _vp_axiom,
    P.Assume: _vp_assume,
    P.Refl: _vp_refl,
    P.Sym: _vp_sym,
    P.Trans: _vp_trans,
    P.Cong: _vp_cong,
    P.MP: _vp_mp,
    P.ImpIntro: _vp_impintro,
    P.Inst: _vp_inst,
    P.Induct: _vp_induct,
    P.ExFalso: _vp_exfalso,
    P.RAA: _vp_raa,
    P.ForallElim: _vp_forallelim,
    P.ForallIntro: _vp_forallintro,
    P.ExistsIntro: _vp_existsintro,
    P.ExistsElim: _vp_existselim,
}


def validate_proof(pf: object) -> None:
    """Structural well-formedness: every node is a known proof term, every
    embedded term/formula/label is a genuine canonical node (exact type, so a
    hostile __eq__-overriding subclass is rejected). Run once, up front, so the
    derivation below can trust Python `==` and stay pure logic.
    """
    handler = _VALIDATE_PROOF.get(type(pf))
    if handler is None:
        raise TypeError(f"not a proof term: {pf!r}")
    handler(pf)


def check(pf: object, theory: object) -> Sequent:
    """Re-derive the sequent proved by `pf` under `theory`, or raise.

    Validates the proof's structure once, then derives. Raises TypeError for a
    malformed proof and ValueError for an invalid derivation step. Inputs are
    typed `object`: the trusted checker validates them, it does not trust the
    caller's annotations.

    `check` is TOTAL: it returns a `Sequent` or raises `TypeError`/`ValueError`,
    nothing else. The recursion is structural, so input deep enough to exhaust
    Python's call stack would raise `RecursionError`; we convert that to a
    `ValueError` here so totality holds for any input. (A pathologically deep
    proof is rejected, not crashed on -- real proofs are nowhere near the limit.)
    """
    if type(theory) is not Theory:
        raise TypeError(f"not a theory: {theory!r}")
    try:
        validate_proof(pf)
        return _derive(pf, theory)
    except RecursionError:
        raise ValueError("proof or term too deeply nested to check") from None


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


# Per-rule derivation, keyed by EXACT proof type below. Each assumes `pf` already
# passed `validate_proof` (so `==` is honest) and recurses via `_derive` (which
# re-applies the sort invariant per sequent). Trust stays here, in the checker --
# proof terms remain inert data; the dispatch is a table, not methods on them.


def _d_axiom(pf: P.Axiom, theory: Theory) -> Sequent:
    if not theory.accepts(pf.formula):
        raise ValueError(f"not an axiom of this theory: {pf.formula!r}")
    return Sequent(frozenset(), pf.formula)


def _d_assume(pf: P.Assume, theory: Theory) -> Sequent:
    return Sequent(frozenset({pf.formula}), pf.formula)


def _d_refl(pf: P.Refl, theory: Theory) -> Sequent:
    return Sequent(frozenset(), Eq(pf.term, pf.term))


def _d_sym(pf: P.Sym, theory: Theory) -> Sequent:
    s = _derive(pf.sub, theory)
    if type(s.concl) is not Eq:
        raise ValueError(f"sym needs an equality, got {s.concl!r}")
    return Sequent(s.hyps, Eq(s.concl.rhs, s.concl.lhs))


def _d_trans(pf: P.Trans, theory: Theory) -> Sequent:
    a = _derive(pf.left, theory)
    b = _derive(pf.right, theory)
    if type(a.concl) is not Eq or type(b.concl) is not Eq:
        raise ValueError("trans needs two equalities")
    if a.concl.rhs != b.concl.lhs:
        raise ValueError(f"trans: middle terms differ: {a.concl.rhs!r} vs {b.concl.lhs!r}")
    return Sequent(a.hyps | b.hyps, Eq(a.concl.lhs, b.concl.rhs))


def _d_cong(pf: P.Cong, theory: Theory) -> Sequent:
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


def _d_mp(pf: P.MP, theory: Theory) -> Sequent:
    imp = _derive(pf.imp, theory)
    ant = _derive(pf.ant, theory)
    if type(imp.concl) is not Implies:
        raise ValueError(f"mp needs an implication, got {imp.concl!r}")
    if imp.concl.ant != ant.concl:
        raise ValueError(
            f"mp: antecedent mismatch:\n  needs: {imp.concl.ant!r}\n  has:   {ant.concl!r}"
        )
    return Sequent(imp.hyps | ant.hyps, imp.concl.con)


def _d_impintro(pf: P.ImpIntro, theory: Theory) -> Sequent:
    body = _derive(pf.body, theory)
    return Sequent(body.hyps - {pf.hyp}, Implies(pf.hyp, body.concl))


def _d_inst(pf: P.Inst, theory: Theory) -> Sequent:
    s = _derive(pf.sub, theory)
    for h in s.hyps:
        if pf.var in h.free_vars():
            raise ValueError(f"cannot instantiate {pf.var!r}: free in hypothesis {h!r}")
    sig = theory.signature
    if sig is not None:
        # the replacement's sort must match the variable's declared sort --
        # instantiating x:K with a V-term is a sort error even when the resulting
        # formula happens to be well-sorted.
        var_sorts = {sort for (name, sort) in s.concl.free_var_sorts() if name == pf.var}
        if var_sorts:
            term_sort = pf.term.sort_of(sig)
            if term_sort not in var_sorts:
                raise ValueError(
                    f"cannot instantiate {pf.var!r}:{var_sorts} with a term of sort {term_sort!r}"
                )
    return Sequent(s.hyps, s.concl.subst(pf.var, pf.term))


def _d_induct(pf: P.Induct, theory: Theory) -> Sequent:
    # Mathematical induction as a first-class rule (NOT an axiom formula):
    #   base : G |- pred[var := 0]
    #   step : D |- pred -> pred[var := S var]
    #   var not free in G u D
    #   ---------------------------------------
    #   G u D |- pred
    # The side condition is what keeps the step universally quantified over `var`;
    # without it (or by citing the schema as an axiom) you can derive 1 = 0.
    if theory.zero is None or type(theory.succ) is not str:
        raise ValueError("theory defines no induction principle (no zero/succ)")
    validate(theory.zero)  # the trusted theory's base term must be canonical
    base = _derive(pf.base, theory)
    step = _derive(pf.step, theory)
    pred_zero = pf.pred.subst(pf.var, theory.zero)
    pred_succ = pf.pred.subst(pf.var, Fun(theory.succ, (Var(pf.var),)))
    if base.concl != pred_zero:
        raise ValueError(f"induction base must prove {pred_zero!r}, got {base.concl!r}")
    if step.concl != Implies(pf.pred, pred_succ):
        raise ValueError(
            f"induction step must prove {Implies(pf.pred, pred_succ)!r}, got {step.concl!r}"
        )
    hyps = base.hyps | step.hyps
    for h in hyps:
        if pf.var in h.free_vars():
            raise ValueError(f"induction variable {pf.var!r} is free in hypothesis {h!r}")
    return Sequent(hyps, pf.pred)


def _d_exfalso(pf: P.ExFalso, theory: Theory) -> Sequent:
    # ex falso quodlibet: a proof of Bottom yields any (well-formed) formula.
    s = _derive(pf.sub, theory)
    if type(s.concl) is not Bottom:
        raise ValueError(f"ex falso needs a proof of Bottom, got {s.concl!r}")
    return Sequent(s.hyps, pf.concl)


def _d_raa(pf: P.RAA, theory: Theory) -> Sequent:
    # classical reductio: assuming Not(goal) leads to Bottom, so goal holds.
    s = _derive(pf.sub, theory)
    if type(s.concl) is not Bottom:
        raise ValueError(f"reductio needs a proof of Bottom, got {s.concl!r}")
    return Sequent(s.hyps - {Not(pf.goal)}, pf.goal)


def _d_forallelim(pf: P.ForallElim, theory: Theory) -> Sequent:
    # from `forall x. body` conclude body[x := term] (capture-avoiding).
    s = _derive(pf.sub, theory)
    if type(s.concl) is not Forall:
        raise ValueError(f"forall-elim needs a universal, got {s.concl!r}")
    sig = theory.signature
    if sig is not None and s.concl.sort:
        t_sort = pf.term.sort_of(sig)
        if t_sort != s.concl.sort:
            raise ValueError(
                f"cannot instantiate forall :{s.concl.sort!r} with a term of sort {t_sort!r}"
            )
    return Sequent(s.hyps, instantiate(s.concl, pf.term))


def _d_forallintro(pf: P.ForallIntro, theory: Theory) -> Sequent:
    # generalize a schematic variable, provided it is not constrained by a
    # hypothesis (the eigenvariable condition).
    s = _derive(pf.sub, theory)
    for h in s.hyps:
        if pf.var in h.free_vars():
            raise ValueError(f"cannot generalize {pf.var!r}: free in hypothesis {h!r}")
    return Sequent(s.hyps, forall(pf.var, pf.sort, s.concl))


def _d_existsintro(pf: P.ExistsIntro, theory: Theory) -> Sequent:
    # from a witness proof of body[x := witness], conclude `exists x. body`.
    if type(pf.claim) is not Exists:
        raise ValueError(f"exists-intro needs an existential claim, got {pf.claim!r}")
    s = _derive(pf.sub, theory)
    expected = instantiate(pf.claim, pf.witness)
    if s.concl != expected:
        raise ValueError(f"exists-intro: sub-proof must prove {expected!r}, got {s.concl!r}")
    sig = theory.signature
    if sig is not None and pf.claim.sort:
        t_sort = pf.witness.sort_of(sig)
        if t_sort != pf.claim.sort:
            raise ValueError(
                f"exists-intro witness has sort {t_sort!r}, expected {pf.claim.sort!r}"
            )
    return Sequent(s.hyps, pf.claim)


def _d_existselim(pf: P.ExistsElim, theory: Theory) -> Sequent:
    # from `exists x. body` and a proof of phi assuming body[x := eigenvar],
    # conclude phi -- provided the eigenvariable does not escape.
    s_ex = _derive(pf.sub_ex, theory)
    if type(s_ex.concl) is not Exists:
        raise ValueError(f"exists-elim needs an existential, got {s_ex.concl!r}")
    instance = instantiate(s_ex.concl, Var(pf.eigenvar, s_ex.concl.sort))
    s_use = _derive(pf.sub_use, theory)
    if instance not in s_use.hyps:
        raise ValueError(f"exists-elim: the using proof must assume the instance {instance!r}")
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


_DERIVE: dict[type, Callable[..., Sequent]] = {
    P.Axiom: _d_axiom,
    P.Assume: _d_assume,
    P.Refl: _d_refl,
    P.Sym: _d_sym,
    P.Trans: _d_trans,
    P.Cong: _d_cong,
    P.MP: _d_mp,
    P.ImpIntro: _d_impintro,
    P.Inst: _d_inst,
    P.Induct: _d_induct,
    P.ExFalso: _d_exfalso,
    P.RAA: _d_raa,
    P.ForallElim: _d_forallelim,
    P.ForallIntro: _d_forallintro,
    P.ExistsIntro: _d_existsintro,
    P.ExistsElim: _d_existselim,
}


def _derive_rule(pf: object, theory: Theory) -> Sequent:
    """The pure logic core: dispatch on the proof's exact type to its rule handler.
    Assumes `pf` already passed validate_proof, so `==` is honest. The `_derive`
    wrapper applies the sort invariant to each produced sequent."""
    handler = _DERIVE.get(type(pf))
    if handler is None:
        raise TypeError(f"not a proof term: {pf!r}")  # unreachable after validate_proof
    return handler(pf, theory)


__all__ = ["Sequent", "Theory", "check", "validate_proof"]
