"""The object language: first-order terms and formulas.

This module is NOT trusted. It is pure, immutable data plus structural helpers
(free variables, substitution, serialization). Anyone may build any term or
formula they like -- a formula is just a claim, not a proof. Trust lives in
checker.py, which re-derives conclusions from proof terms over this language.

Logic for v0 is minimal: equality and implication, with free variables read as
implicitly universally quantified. Exactly enough to bootstrap arithmetic.
"""

from __future__ import annotations

from dataclasses import dataclass, fields, is_dataclass

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
        if var not in formula_free_vars(f.body):
            return f
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
# Serialization  (generic, by reflection over the frozen-dataclass fields)
# ---------------------------------------------------------------------------
# Every node is a frozen dataclass whose fields are strings, tuples, or other
# nodes -- so we serialize generically rather than hand-coding a branch per
# node: tag each node with its class name, recurse on fields, and reconstruct
# from a class registry. Adding a node needs no serialization code. Deserialized
# data is untrusted, but the checker re-validates every term/formula, so the
# parser need only refuse unknown kinds and mismatched field sets.


def encode_node(node: object) -> dict:
    """Encode a node (a frozen dataclass) to a tagged dict, recursing on fields."""
    if not is_dataclass(node) or isinstance(node, type):
        raise TypeError(f"cannot serialize {type(node).__name__}")
    body = {f.name: _encode_value(getattr(node, f.name)) for f in fields(node)}
    return {"k": type(node).__name__, **body}


def _encode_value(v: object) -> object:
    if isinstance(v, str):
        return v
    if isinstance(v, (tuple, list)):
        return [_encode_value(x) for x in v]
    if is_dataclass(v) and not isinstance(v, type):
        return encode_node(v)
    raise TypeError(f"cannot serialize value of type {type(v).__name__}")


def decode_node(raw: object, registry: dict) -> object:
    if isinstance(raw, str):
        return raw
    if isinstance(raw, list):
        return tuple(decode_node(x, registry) for x in raw)
    if isinstance(raw, dict):
        cls = registry.get(raw.get("k"))
        if cls is None:
            raise ValueError(f"unknown node kind: {raw.get('k')!r}")
        names = [f.name for f in fields(cls)]
        got = sorted(set(raw) - {"k"})
        if got != sorted(names):
            raise ValueError(f"{cls.__name__}: bad fields {got} (want {names})")
        return cls(*(decode_node(raw[n], registry) for n in names))
    raise ValueError(f"not a serializable node: {raw!r}")


SYNTAX_REGISTRY = {c.__name__: c for c in (Var, Fun, Eq, Implies, Bottom, Forall, Exists)}


def term_to_dict(t: Term) -> dict:
    return encode_node(t)


def term_from_dict(d: object) -> Term:
    node = decode_node(d, SYNTAX_REGISTRY)
    if not isinstance(node, Term):
        raise ValueError(f"expected a term, got {type(node).__name__}")
    return node


def formula_to_dict(f: Formula) -> dict:
    return encode_node(f)


def formula_from_dict(d: object) -> Formula:
    node = decode_node(d, SYNTAX_REGISTRY)
    if not isinstance(node, Formula):
        raise ValueError(f"expected a formula, got {type(node).__name__}")
    return node
