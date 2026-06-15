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


@dataclass(frozen=True, slots=True)
class BVar(Term):
    """A bound variable, as a de Bruijn index (0 = nearest enclosing binder).

    Bound variables carry no name, so alpha-equivalent formulas are *identical*
    data: `==` is alpha-equivalence, with no fresh names and no separate alpha
    relation. The binder (Forall/Exists) records the sort.
    """

    index: int

    def __repr__(self) -> str:
        return f"#{self.index}"


def term_free_vars(t: Term) -> frozenset:
    if isinstance(t, Var):
        return frozenset({t.name})
    if isinstance(t, BVar):
        return frozenset()  # bound variables are nameless, never free
    if isinstance(t, Fun):
        out: frozenset = frozenset()
        for a in t.args:
            out |= term_free_vars(a)
        return out
    raise TypeError(f"not a term: {t!r}")


def term_subst(t: Term, var: str, repl: Term) -> Term:
    """Replace the free variable Var(var) with repl. Capture is impossible: free
    variables are named, binders are nameless (de Bruijn), so nothing captures."""
    if isinstance(t, Var):
        return repl if t.name == var else t
    if isinstance(t, BVar):
        return t
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
    """Universal quantifier (locally nameless). `body` refers to the bound
    variable via BVar(0); the bound name is gone, so `==` is alpha-equivalence.
    Build with `forall(name, sort, body)`, which abstracts the named variable."""

    sort: str
    body: Formula

    def __repr__(self) -> str:
        return f"(forall :{self.sort}. {self.body!r})" if self.sort else f"(forall. {self.body!r})"


@dataclass(frozen=True, slots=True)
class Exists(Formula):
    """Existential quantifier (locally nameless); see Forall."""

    sort: str
    body: Formula

    def __repr__(self) -> str:
        return f"(exists :{self.sort}. {self.body!r})" if self.sort else f"(exists. {self.body!r})"


# --- binding operations (locally nameless) --------------------------------
# `abstract` turns a free variable into a bound one (close a binder); `instantiate`
# replaces the outermost bound variable with a term (open a binder). Smart
# constructors `forall`/`exists` let us still WRITE named binders at the surface.


def _abstract_term(name: str, t: Term, depth: int) -> Term:
    if isinstance(t, Var):
        return BVar(depth) if t.name == name else t
    if isinstance(t, BVar):
        return t
    if isinstance(t, Fun):
        return Fun(t.name, tuple(_abstract_term(name, a, depth) for a in t.args))
    raise TypeError(f"not a term: {t!r}")


def _abstract(name: str, f: Formula, depth: int) -> Formula:
    if isinstance(f, Eq):
        return Eq(_abstract_term(name, f.lhs, depth), _abstract_term(name, f.rhs, depth))
    if isinstance(f, Implies):
        return Implies(_abstract(name, f.ant, depth), _abstract(name, f.con, depth))
    if isinstance(f, Bottom):
        return f
    if isinstance(f, (Forall, Exists)):
        return type(f)(f.sort, _abstract(name, f.body, depth + 1))
    raise TypeError(f"not a formula: {f!r}")


def _instantiate_term(t: Term, repl: Term, depth: int) -> Term:
    if isinstance(t, BVar):
        if t.index == depth:
            return repl
        return BVar(t.index - 1) if t.index > depth else t
    if isinstance(t, Var):
        return t
    if isinstance(t, Fun):
        return Fun(t.name, tuple(_instantiate_term(a, repl, depth) for a in t.args))
    raise TypeError(f"not a term: {t!r}")


def _instantiate(f: Formula, repl: Term, depth: int) -> Formula:
    if isinstance(f, Eq):
        return Eq(_instantiate_term(f.lhs, repl, depth), _instantiate_term(f.rhs, repl, depth))
    if isinstance(f, Implies):
        return Implies(_instantiate(f.ant, repl, depth), _instantiate(f.con, repl, depth))
    if isinstance(f, Bottom):
        return f
    if isinstance(f, (Forall, Exists)):
        return type(f)(f.sort, _instantiate(f.body, repl, depth + 1))
    raise TypeError(f"not a formula: {f!r}")


def forall(name: str, sort: str, body: Formula) -> Formula:  # noqa: N802 -- connective
    return Forall(sort, _abstract(name, body, 0))


def exists(name: str, sort: str, body: Formula) -> Formula:  # noqa: N802 -- connective
    return Exists(sort, _abstract(name, body, 0))


def instantiate(binder: Formula, repl: Term) -> Formula:
    """Open the outermost binder of `binder` (a Forall/Exists) with `repl`."""
    if not isinstance(binder, (Forall, Exists)):
        raise TypeError(f"not a quantifier: {binder!r}")
    return _instantiate(binder.body, repl, 0)


# ---------------------------------------------------------------------------
# Generic traversal  (one fold; the hand-rolled walkers are derived from it)
# ---------------------------------------------------------------------------
# A node is a frozen dataclass; its CHILDREN are the dataclass-valued fields (and
# dataclass elements of tuple fields). Because bound variables are nameless
# (locally nameless), no binder is special to free-vars/substitution, so a
# single uniform fold suffices -- no per-node walker, no binding-scope tracking.


def is_a(node: object, kind) -> bool:
    """Exact concrete-node test (the trust-correct choice; subclasses do not
    match). `kind` may be a class or a tuple of classes. Use plain `isinstance`
    only for the abstract bases Term/Formula/Pf, where subclass membership is the
    point."""
    return type(node) is kind if isinstance(kind, type) else type(node) in kind


def _is_node(v: object) -> bool:
    return is_dataclass(v) and not isinstance(v, type)


def children(node: object) -> list:
    """Immediate sub-nodes of `node`, in field order (tuple fields flattened)."""
    if not is_dataclass(node) or isinstance(node, type):
        raise TypeError(f"not a node: {type(node).__name__}")
    out: list = []
    for f in fields(node):
        v = getattr(node, f.name)
        if _is_node(v):
            out.append(v)
        elif isinstance(v, tuple):
            out.extend(x for x in v if _is_node(x))
    return out


def map_children(node, fn):
    """Rebuild `node`, replacing each immediate sub-node with `fn(sub-node)`."""
    if not is_dataclass(node) or isinstance(node, type):
        raise TypeError(f"not a node: {type(node).__name__}")
    new = {}
    for f in fields(node):
        v = getattr(node, f.name)
        if is_dataclass(v) and not isinstance(v, type):
            new[f.name] = fn(v)
        elif isinstance(v, tuple):
            new[f.name] = tuple(
                fn(x) if (is_dataclass(x) and not isinstance(x, type)) else x for x in v
            )
        else:
            new[f.name] = v
    return type(node)(**new)


def free_vars(node: object) -> frozenset:
    """Free variable names in a term or formula -- a uniform fold over children.
    Var contributes its name; BVar (nameless) contributes nothing."""
    if type(node) is Var:  # exact + narrows for the .name access
        return frozenset({node.name})
    acc: frozenset = frozenset()
    for c in children(node):
        acc |= free_vars(c)
    return acc


def subst(node, var: str, repl: Term):
    """Substitute the free variable `var` with `repl` in a term or formula -- a
    uniform map over children. Only Var is special; nameless binders, being
    indices, need no capture-avoidance."""
    if type(node) is Var:
        return repl if node.name == var else node
    return map_children(node, lambda c: subst(c, var, repl))


def formula_free_vars(f: Formula) -> frozenset:
    if isinstance(f, Eq):
        return term_free_vars(f.lhs) | term_free_vars(f.rhs)
    if isinstance(f, Implies):
        return formula_free_vars(f.ant) | formula_free_vars(f.con)
    if isinstance(f, Bottom):
        return frozenset()
    if isinstance(f, (Forall, Exists)):
        return formula_free_vars(f.body)  # bound vars are nameless; all names are free
    raise TypeError(f"not a formula: {f!r}")


def formula_subst(f: Formula, var: str, repl: Term) -> Formula:
    """Substitute a free variable. No capture-avoidance needed: free variables
    are named and binders are nameless, so a substituted free variable can never
    be captured by a binder."""
    if isinstance(f, Eq):
        return Eq(term_subst(f.lhs, var, repl), term_subst(f.rhs, var, repl))
    if isinstance(f, Implies):
        return Implies(formula_subst(f.ant, var, repl), formula_subst(f.con, var, repl))
    if isinstance(f, Bottom):
        return f
    if isinstance(f, (Forall, Exists)):
        return type(f)(f.sort, formula_subst(f.body, var, repl))
    raise TypeError(f"not a formula: {f!r}")


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


def validate_term(t: object, depth: int = 0) -> None:
    if type(t) is Var:
        _check_str(t.name, "Var.name")
        _check_str(t.sort, "Var.sort")
        return
    if type(t) is BVar:
        if type(t.index) is not int or not (0 <= t.index < depth):
            raise TypeError(f"dangling bound variable {t.index!r} at binder depth {depth}")
        return
    if type(t) is Fun:
        _check_str(t.name, "Fun.name")
        if type(t.args) is not tuple:
            raise TypeError("Fun.args must be a tuple")
        for a in t.args:
            validate_term(a, depth)
        return
    raise TypeError(f"non-canonical term: {type(t).__name__}")


def validate_formula(f: object, depth: int = 0) -> None:
    # `depth` counts enclosing binders; a BVar is well-formed only if its index
    # is below it (local closure: no dangling bound variable).
    if type(f) is Eq:
        validate_term(f.lhs, depth)
        validate_term(f.rhs, depth)
        return
    if type(f) is Implies:
        validate_formula(f.ant, depth)
        validate_formula(f.con, depth)
        return
    if type(f) is Bottom:
        return
    if type(f) is Forall or type(f) is Exists:
        _check_str(f.sort, "quantifier sort")
        validate_formula(f.body, depth + 1)
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
    if isinstance(v, str) or (isinstance(v, int) and not isinstance(v, bool)):
        return v  # str labels, or int de Bruijn indices
    if isinstance(v, (tuple, list)):
        return [_encode_value(x) for x in v]
    if is_dataclass(v) and not isinstance(v, type):
        return encode_node(v)
    raise TypeError(f"cannot serialize value of type {type(v).__name__}")


def decode_node(raw: object, registry: dict) -> object:
    if isinstance(raw, str) or (isinstance(raw, int) and not isinstance(raw, bool)):
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


SYNTAX_REGISTRY = {c.__name__: c for c in (Var, BVar, Fun, Eq, Implies, Bottom, Forall, Exists)}


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
