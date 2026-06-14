"""A tiny LCF-style proof kernel for first-order logic with equality.

The trust boundary is *this file and nothing else*. A `Theorem` is an opaque
sequent ``hyps |- conclusion``. The only way to obtain one is through the
inference-rule functions below; calling ``Theorem(...)`` directly raises. So if
you hold a `Theorem` object, its conclusion really is derivable from its
hypotheses using these rules (plus whatever you fed through the `axiom` door).

Convention: free variables in a theorem are implicitly universally quantified.
That is what makes `instantiate` sound, and it is the Boyer--Moore instinct --
no explicit quantifier connective is needed for the arithmetic we build here.

Logic for v0 is deliberately minimal: terms, equality, and implication. That is
exactly enough to bootstrap addition and prove ``0 + n = n`` by induction. Not,
And, Or, and explicit quantifiers are future work; see README.
"""

from __future__ import annotations

from dataclasses import dataclass


# ---------------------------------------------------------------------------
# Terms
# ---------------------------------------------------------------------------
# A term is either a variable or a function symbol applied to argument terms.
# Constants are just nullary functions, e.g. zero is Fun("0", ()).


class Term:
    """Base class for terms. Subclasses are frozen so terms are hashable."""

    __slots__ = ()


@dataclass(frozen=True, slots=True)
class Var(Term):
    name: str

    def __repr__(self) -> str:
        return self.name


@dataclass(frozen=True, slots=True)
class Fun(Term):
    name: str
    args: tuple  # tuple[Term, ...]

    def __repr__(self) -> str:
        if not self.args:
            return self.name
        inner = ", ".join(repr(a) for a in self.args)
        return f"{self.name}({inner})"


def term_free_vars(term: Term) -> frozenset:
    if isinstance(term, Var):
        return frozenset({term.name})
    if isinstance(term, Fun):
        out: frozenset = frozenset()
        for a in term.args:
            out |= term_free_vars(a)
        return out
    raise TypeError(f"not a term: {term!r}")


def term_subst(term: Term, var: str, repl: Term) -> Term:
    """Replace every Var(var) inside `term` with `repl`.

    There are no binders inside terms, so this cannot capture anything.
    """
    if isinstance(term, Var):
        return repl if term.name == var else term
    if isinstance(term, Fun):
        return Fun(term.name, tuple(term_subst(a, var, repl) for a in term.args))
    raise TypeError(f"not a term: {term!r}")


# ---------------------------------------------------------------------------
# Formulas
# ---------------------------------------------------------------------------


class Formula:
    """Base class for formulas."""

    __slots__ = ()


@dataclass(frozen=True, slots=True)
class Eq(Formula):
    lhs: Term
    rhs: Term

    def __repr__(self) -> str:
        return f"{self.lhs!r} = {self.rhs!r}"


@dataclass(frozen=True, slots=True)
class Implies(Formula):
    ant: Formula
    con: Formula

    def __repr__(self) -> str:
        return f"({self.ant!r} -> {self.con!r})"


def formula_free_vars(f: Formula) -> frozenset:
    if isinstance(f, Eq):
        return term_free_vars(f.lhs) | term_free_vars(f.rhs)
    if isinstance(f, Implies):
        return formula_free_vars(f.ant) | formula_free_vars(f.con)
    raise TypeError(f"not a formula: {f!r}")


def formula_subst(f: Formula, var: str, repl: Term) -> Formula:
    if isinstance(f, Eq):
        return Eq(term_subst(f.lhs, var, repl), term_subst(f.rhs, var, repl))
    if isinstance(f, Implies):
        return Implies(formula_subst(f.ant, var, repl), formula_subst(f.con, var, repl))
    raise TypeError(f"not a formula: {f!r}")


# ---------------------------------------------------------------------------
# Theorems  (the trust boundary)
# ---------------------------------------------------------------------------

_KERNEL_TOKEN = object()  # only this module owns it


class Theorem:
    """A proven sequent ``hyps |- conclusion``.

    Cannot be constructed outside the kernel: every inference rule below passes
    the private token. This is the whole soundness story -- if you have a
    Theorem, a kernel rule made it.
    """

    __slots__ = ("hyps", "concl")

    def __init__(self, hyps, concl: Formula, _token=None):
        if _token is not _KERNEL_TOKEN:
            raise PermissionError(
                "Theorems may only be minted by kernel inference rules, "
                "not constructed directly."
            )
        self.hyps = frozenset(hyps)
        self.concl = concl

    def __repr__(self) -> str:
        if self.hyps:
            ctx = ", ".join(sorted(repr(h) for h in self.hyps))
            return f"{ctx} |- {self.concl!r}"
        return f"|- {self.concl!r}"


def _mk(hyps, concl: Formula) -> Theorem:
    return Theorem(hyps, concl, _KERNEL_TOKEN)


# ---------------------------------------------------------------------------
# Inference rules
# ---------------------------------------------------------------------------


def axiom(formula: Formula) -> Theorem:
    """The trusted door: assert `formula` with no hypotheses.

    Everything asserted here is part of the trusted base, on the same footing
    as the inference rules. Keep the set of axioms small and visible. The Peano
    axioms in peano.py are introduced exclusively through this function.
    """
    return _mk(frozenset(), formula)


def assume(formula: Formula) -> Theorem:
    """``formula |- formula``. Introduces a hypothesis to later discharge."""
    return _mk(frozenset({formula}), formula)


def refl(term: Term) -> Theorem:
    """``|- term = term``."""
    return _mk(frozenset(), Eq(term, term))


def sym(thm: Theorem) -> Theorem:
    """From ``G |- a = b`` derive ``G |- b = a``."""
    if not isinstance(thm.concl, Eq):
        raise ValueError(f"sym expects an equality, got {thm.concl!r}")
    return _mk(thm.hyps, Eq(thm.concl.rhs, thm.concl.lhs))


def trans(t1: Theorem, t2: Theorem) -> Theorem:
    """From ``G |- a = b`` and ``D |- b = c`` derive ``G,D |- a = c``."""
    if not isinstance(t1.concl, Eq) or not isinstance(t2.concl, Eq):
        raise ValueError("trans expects two equalities")
    if t1.concl.rhs != t2.concl.lhs:
        raise ValueError(
            f"trans: middle terms differ: {t1.concl.rhs!r} vs {t2.concl.lhs!r}"
        )
    return _mk(t1.hyps | t2.hyps, Eq(t1.concl.lhs, t2.concl.rhs))


def cong(fun_name: str, arg_thms) -> Theorem:
    """Congruence. Given ``Gi |- a_i = b_i`` for each argument slot, derive
    ``union Gi |- f(a_1..a_n) = f(b_1..b_n)``.

    For an unchanged argument, pass ``refl(t)``.
    """
    arg_thms = list(arg_thms)
    hyps: frozenset = frozenset()
    lhs_args = []
    rhs_args = []
    for t in arg_thms:
        if not isinstance(t.concl, Eq):
            raise ValueError(f"cong expects equalities, got {t.concl!r}")
        hyps |= t.hyps
        lhs_args.append(t.concl.lhs)
        rhs_args.append(t.concl.rhs)
    return _mk(hyps, Eq(Fun(fun_name, tuple(lhs_args)), Fun(fun_name, tuple(rhs_args))))


def mp(t_imp: Theorem, t_ant: Theorem) -> Theorem:
    """Modus ponens. From ``G |- A -> B`` and ``D |- A`` derive ``G,D |- B``."""
    if not isinstance(t_imp.concl, Implies):
        raise ValueError(f"mp expects an implication, got {t_imp.concl!r}")
    if t_imp.concl.ant != t_ant.concl:
        raise ValueError(
            f"mp: antecedent mismatch:\n  needs: {t_imp.concl.ant!r}\n  has:   {t_ant.concl!r}"
        )
    return _mk(t_imp.hyps | t_ant.hyps, t_imp.concl.con)


def implies_intro(hyp: Formula, thm: Theorem) -> Theorem:
    """Discharge a hypothesis. From ``G |- B`` derive ``G\\{hyp} |- hyp -> B``."""
    return _mk(thm.hyps - {hyp}, Implies(hyp, thm.concl))


def instantiate(thm: Theorem, var: str, term: Term) -> Theorem:
    """Universal instantiation. From ``G |- P`` derive ``G |- P[var := term]``.

    Sound because free variables are implicitly universally quantified -- but
    only for variables that are NOT free in the hypotheses (instantiating a
    variable a hypothesis still constrains would be unsound). We enforce that.
    """
    for h in thm.hyps:
        if var in formula_free_vars(h):
            raise ValueError(
                f"cannot instantiate {var!r}: it is free in hypothesis {h!r}"
            )
    return _mk(thm.hyps, formula_subst(thm.concl, var, term))
