"""The object language: first-order terms and formulas.

This module is NOT trusted. It is pure, immutable data plus structural helpers
(free variables, substitution, serialization). Anyone may build any term or
formula they like -- a formula is just a claim, not a proof. Trust lives in
checker.py, which re-derives conclusions from proof terms over this language.

Logic for v0 is minimal: equality and implication, with free variables read as
implicitly universally quantified. Exactly enough to bootstrap arithmetic.
"""

from __future__ import annotations

from dataclasses import dataclass

# ---------------------------------------------------------------------------
# Terms
# ---------------------------------------------------------------------------


class Term:
    __slots__ = ()


@dataclass(frozen=True, slots=True)
class Var(Term):
    name: str
    sort: str = ""  # "" means unsorted (single-sorted theories ignore it)

    def __repr__(self) -> str:
        return f"{self.name}:{self.sort}" if self.sort else self.name


@dataclass(frozen=True, slots=True)
class Fun(Term):
    name: str
    args: tuple  # tuple[Term, ...]

    def __post_init__(self) -> None:
        # Snapshot args into an immutable tuple. Without this, a caller's
        # mutable list is aliased into the term, so mutating it later would
        # retroactively rewrite a term already used in a proof. (Elements are
        # themselves immutable terms, so a shallow snapshot is deep enough.)
        if type(self.args) is not tuple:
            object.__setattr__(self, "args", tuple(self.args))

    def __repr__(self) -> str:
        if not self.args:
            return self.name
        return f"{self.name}({', '.join(map(repr, self.args))})"


def term_free_vars(t: Term) -> frozenset:
    if isinstance(t, Var):
        return frozenset({t.name})
    if isinstance(t, Fun):
        out: frozenset = frozenset()
        for a in t.args:
            out |= term_free_vars(a)
        return out
    raise TypeError(f"not a term: {t!r}")


def term_subst(t: Term, var: str, repl: Term) -> Term:
    """Replace Var(var) with repl. No binders inside terms, so no capture."""
    if isinstance(t, Var):
        return repl if t.name == var else t
    if isinstance(t, Fun):
        return Fun(t.name, tuple(term_subst(a, var, repl) for a in t.args))
    raise TypeError(f"not a term: {t!r}")


# ---------------------------------------------------------------------------
# Formulas
# ---------------------------------------------------------------------------


class Formula:
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


@dataclass(frozen=True, slots=True)
class Bottom(Formula):
    """Absurdity (falsum). Negation is sugar: Not(A) == Implies(A, Bottom())."""

    def __repr__(self) -> str:
        return "⊥"  # ⊥


def Not(a: Formula) -> Formula:  # noqa: N802 -- reads as the logical connective
    return Implies(a, Bottom())


@dataclass(frozen=True, slots=True)
class Forall(Formula):
    """Universal quantifier: binds `var` (of `sort`) in `body`."""

    var: str
    sort: str
    body: Formula

    def __repr__(self) -> str:
        v = f"{self.var}:{self.sort}" if self.sort else self.var
        return f"(forall {v}. {self.body!r})"


@dataclass(frozen=True, slots=True)
class Exists(Formula):
    """Existential quantifier: binds `var` (of `sort`) in `body`."""

    var: str
    sort: str
    body: Formula

    def __repr__(self) -> str:
        v = f"{self.var}:{self.sort}" if self.sort else self.var
        return f"(exists {v}. {self.body!r})"


def formula_free_vars(f: Formula) -> frozenset:
    if isinstance(f, Eq):
        return term_free_vars(f.lhs) | term_free_vars(f.rhs)
    if isinstance(f, Implies):
        return formula_free_vars(f.ant) | formula_free_vars(f.con)
    if isinstance(f, Bottom):
        return frozenset()
    if isinstance(f, (Forall, Exists)):
        return formula_free_vars(f.body) - {f.var}
    raise TypeError(f"not a formula: {f!r}")


def formula_subst(f: Formula, var: str, repl: Term) -> Formula:
    if isinstance(f, Eq):
        return Eq(term_subst(f.lhs, var, repl), term_subst(f.rhs, var, repl))
    if isinstance(f, Implies):
        return Implies(formula_subst(f.ant, var, repl), formula_subst(f.con, var, repl))
    if isinstance(f, Bottom):
        return f
    if isinstance(f, (Forall, Exists)):
        cls = type(f)
        if f.var == var:
            return f  # the binder shadows `var`; nothing free to substitute
        if f.var in term_free_vars(repl):
            # capture would occur: alpha-rename the bound variable to a fresh
            # name (the fresh name can't be captured, so the rename is safe),
            # then substitute into the renamed body.
            fresh = _fresh(f.var, term_free_vars(repl) | formula_free_vars(f.body) | {var})
            renamed = formula_subst(f.body, f.var, Var(fresh, f.sort))
            return cls(fresh, f.sort, formula_subst(renamed, var, repl))
        return cls(f.var, f.sort, formula_subst(f.body, var, repl))
    raise TypeError(f"not a formula: {f!r}")


def _fresh(base: str, avoid: frozenset) -> str:
    candidate = base
    while candidate in avoid:
        candidate += "'"
    return candidate


# ---------------------------------------------------------------------------
# Well-formedness validation  (the trust boundary's first gate)
# ---------------------------------------------------------------------------
# The checker compares terms and formulas with Python `==`. That is only sound
# if every value is a genuine canonical node: a hostile Term/str subclass can
# override __eq__ to return True for unequal things and derive `1 = 0` from
# reflexivity alone. So before trusting `==`, we verify EXACT types (not
# isinstance -- subclasses are exactly the attack) all the way down, including
# the str fields, which also feed equality.


def _check_str(s: object, what: str) -> None:
    if type(s) is not str:
        raise TypeError(f"{what} must be a genuine str, got {type(s).__name__}")


def validate_term(t: object) -> None:
    if type(t) is Var:
        _check_str(t.name, "Var.name")
        _check_str(t.sort, "Var.sort")
        return
    if type(t) is Fun:
        _check_str(t.name, "Fun.name")
        if type(t.args) is not tuple:
            raise TypeError("Fun.args must be a tuple")
        for a in t.args:
            validate_term(a)
        return
    raise TypeError(f"non-canonical term: {type(t).__name__}")


def validate_formula(f: object) -> None:
    if type(f) is Eq:
        validate_term(f.lhs)
        validate_term(f.rhs)
        return
    if type(f) is Implies:
        validate_formula(f.ant)
        validate_formula(f.con)
        return
    if type(f) is Bottom:
        return
    if type(f) is Forall or type(f) is Exists:
        _check_str(f.var, "quantifier var")
        _check_str(f.sort, "quantifier sort")
        validate_formula(f.body)
        return
    raise TypeError(f"non-canonical formula: {type(f).__name__}")


# ---------------------------------------------------------------------------
# Serialization  (so proofs can cross a process boundary as plain JSON)
# ---------------------------------------------------------------------------
# from_dict validates rigorously: deserialized data is untrusted input.


def term_to_dict(t: Term) -> dict:
    if isinstance(t, Var):
        return {"k": "Var", "name": t.name, "sort": t.sort}
    if isinstance(t, Fun):
        return {"k": "Fun", "name": t.name, "args": [term_to_dict(a) for a in t.args]}
    raise TypeError(f"not a term: {t!r}")


def term_from_dict(d: object) -> Term:
    if not isinstance(d, dict) or "k" not in d:
        raise ValueError(f"not a term node: {d!r}")
    kind = d["k"]
    if kind == "Var":
        name = d["name"]
        sort = d.get("sort", "")
        if not isinstance(name, str) or not isinstance(sort, str):
            raise ValueError("Var.name and Var.sort must be strings")
        return Var(name, sort)
    if kind == "Fun":
        name, args = d["name"], d["args"]
        if not isinstance(name, str) or not isinstance(args, list):
            raise ValueError("malformed Fun node")
        return Fun(name, tuple(term_from_dict(a) for a in args))
    raise ValueError(f"unknown term kind: {kind!r}")


def formula_to_dict(f: Formula) -> dict:
    if isinstance(f, Eq):
        return {"k": "Eq", "lhs": term_to_dict(f.lhs), "rhs": term_to_dict(f.rhs)}
    if isinstance(f, Implies):
        return {"k": "Implies", "ant": formula_to_dict(f.ant), "con": formula_to_dict(f.con)}
    if isinstance(f, Bottom):
        return {"k": "Bottom"}
    raise TypeError(f"not a formula: {f!r}")


def formula_from_dict(d: object) -> Formula:
    if not isinstance(d, dict) or "k" not in d:
        raise ValueError(f"not a formula node: {d!r}")
    kind = d["k"]
    if kind == "Eq":
        return Eq(term_from_dict(d["lhs"]), term_from_dict(d["rhs"]))
    if kind == "Implies":
        return Implies(formula_from_dict(d["ant"]), formula_from_dict(d["con"]))
    if kind == "Bottom":
        return Bottom()
    raise ValueError(f"unknown formula kind: {kind!r}")
