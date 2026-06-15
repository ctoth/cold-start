"""The object language: first-order terms and formulas.

This module is NOT trusted. It is pure, immutable data plus structural helpers
(free variables, substitution, serialization). Anyone may build any term or
formula they like -- a formula is just a claim, not a proof. Trust lives in
checker.py, which re-derives conclusions from proof terms over this language.

Design: one `Node` root. Structural operations are *methods*, dispatched by
Python on the node's class -- the base `Node` carries the generic recursion over a
node's children, and only `Var` and the binders override. The single exception is
`validate`, the trust gate, which must reject hostile subclasses and so dispatches
on EXACT type (a method could be overridden by the subclass it must reject).

Binders are locally nameless: a bound variable is a de Bruijn index `BVar(i)` and
the binder records only the sort, so alpha-equivalence is literal `==`.
"""

from __future__ import annotations

from dataclasses import dataclass, fields, is_dataclass
from typing import ClassVar, cast


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
        if _is_node(v):
            new[f.name] = fn(v)
        elif isinstance(v, tuple):
            new[f.name] = tuple(fn(x) if _is_node(x) else x for x in v)
        else:
            new[f.name] = v
    return type(node)(**new)


class Node:
    """Base of every syntax node. Operations are methods here, dispatched by class.
    The generic versions recurse over a node's children; only `Var` and the binders
    override. `abstract`/`instantiate` thread the binder depth (the scope); `Var`
    and `BVar` are the leaves that read it, and the binders raise it.
    """

    __slots__ = ()

    def free_vars(self) -> frozenset:
        """Free variable names. Var contributes its name (override); bound
        variables are nameless; everything else is the union of its children."""
        out: frozenset = frozenset()
        for c in children(self):
            out |= c.free_vars()
        return out

    def subst(self, var: str, repl: Term) -> Node:
        """Replace the free variable `var` with `repl`. Locally nameless, so no
        capture-avoidance; only `Var` is special (override)."""
        return cast(Node, map_children(self, lambda c: c.subst(var, repl)))

    def abstract(self, name: str, depth: int) -> Node:
        """Close a binder: replace the free variable `name` with the bound index
        `depth`. `Var` makes the index; the binders raise `depth`."""
        return cast(Node, map_children(self, lambda c: c.abstract(name, depth)))

    def instantiate(self, repl: Term, depth: int) -> Node:
        """Open a binder: the bound variable at `depth` becomes `repl`. `BVar`
        reads the index; the binders raise `depth`."""
        return cast(Node, map_children(self, lambda c: c.instantiate(repl, depth)))

    def free_var_sorts(self) -> frozenset:
        """Free `(name, sort)` pairs -- like `free_vars` but keeping each variable's
        declared sort, so the checker can enforce one sort per name. Var overrides."""
        out: frozenset = frozenset()
        for c in children(self):
            out |= c.free_var_sorts()
        return out

    def _validate(self, depth: int) -> None:
        """Exact-type well-formedness of this node's own fields, recursing through
        the `validate` gate (which re-checks each child's exact type). Each concrete
        node overrides; `depth` counts enclosing binders, bounding legal `BVar`s.
        Only ever called after the gate confirms `type(self)` is canonical."""
        raise TypeError(f"non-canonical node: {type(self).__name__}")


# ---------------------------------------------------------------------------
# Terms
# ---------------------------------------------------------------------------


class Term(Node):
    __slots__ = ()

    def subst(self, var: str, repl: Term) -> Term:  # substituting in a term yields a term
        return cast(Term, super().subst(var, repl))

    def sort_of(self, sig, scope: tuple = ()) -> str:
        """The sort of this term under signature `sig`. `scope` is the stack of
        enclosing binders' sorts (a `BVar(i)` reads `scope[i]`). Each concrete term
        overrides; sorts and quantifiers coexist because descending under a binder
        pushes its sort onto `scope`."""
        raise TypeError(f"not a term: {self!r}")


@dataclass(frozen=True, slots=True)
class Var(Term):
    name: str
    sort: str = ""  # "" means unsorted (single-sorted theories ignore it)

    def __repr__(self) -> str:
        return f"{self.name}:{self.sort}" if self.sort else self.name

    def free_vars(self) -> frozenset:
        return frozenset({self.name})

    def free_var_sorts(self) -> frozenset:
        return frozenset({(self.name, self.sort)})

    def subst(self, var: str, repl: Term) -> Term:
        return repl if self.name == var else self

    def abstract(self, name: str, depth: int) -> Term:
        return BVar(depth) if self.name == name else self

    def sort_of(self, sig, scope: tuple = ()) -> str:
        if self.sort not in sig.sorts:
            raise ValueError(f"variable {self!r} has undeclared sort {self.sort!r}")
        return self.sort

    def _validate(self, depth: int) -> None:
        _check_str(self.name, "Var.name")
        _check_str(self.sort, "Var.sort")


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

    def sort_of(self, sig, scope: tuple = ()) -> str:
        rank = sig.rank(self.name)
        if rank is None:
            raise ValueError(f"undeclared function symbol {self.name!r}")
        arg_sorts, result = rank
        if len(self.args) != len(arg_sorts):
            raise ValueError(f"{self.name!r} expects {len(arg_sorts)} args, got {len(self.args)}")
        for a, expected in zip(self.args, arg_sorts, strict=True):
            actual = a.sort_of(sig, scope)
            if actual != expected:
                raise ValueError(f"{self.name!r} arg has sort {actual!r}, expected {expected!r}")
        return result

    def _validate(self, depth: int) -> None:
        _check_str(self.name, "Fun.name")
        if type(self.args) is not tuple:
            raise TypeError("Fun.args must be a tuple")
        for a in self.args:
            validate(a, depth)


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

    def instantiate(self, repl: Term, depth: int) -> Term:
        if self.index == depth:
            return repl
        return BVar(self.index - 1) if self.index > depth else self

    def sort_of(self, sig, scope: tuple = ()) -> str:
        if not (0 <= self.index < len(scope)):
            raise ValueError(f"dangling bound variable {self.index!r} (scope depth {len(scope)})")
        return scope[self.index]

    def _validate(self, depth: int) -> None:
        if type(self.index) is not int or not (0 <= self.index < depth):
            raise TypeError(f"dangling bound variable {self.index!r} at binder depth {depth}")


# ---------------------------------------------------------------------------
# Formulas
# ---------------------------------------------------------------------------


class Formula(Node):
    __slots__ = ()

    def subst(self, var: str, repl: Term) -> Formula:  # substituting in a formula yields a formula
        return cast(Formula, super().subst(var, repl))

    def sort_check(self, sig, scope: tuple = ()) -> None:
        """Structural well-sortedness under `sig`: each equality relates same-sort
        terms; a binder pushes its bound sort onto `scope`, so a quantified sorted
        formula checks (sorts and quantifiers coexist). Each formula overrides."""
        raise TypeError(f"not a formula: {self!r}")


@dataclass(frozen=True, slots=True)
class Eq(Formula):
    symbol: ClassVar[str] = "="

    lhs: Term
    rhs: Term

    def __repr__(self) -> str:
        return f"{self.lhs!r} = {self.rhs!r}"

    def sort_check(self, sig, scope: tuple = ()) -> None:
        ls, rs = self.lhs.sort_of(sig, scope), self.rhs.sort_of(sig, scope)
        if ls != rs:
            raise ValueError(f"equality across sorts: {ls!r} = {rs!r} in {self!r}")

    def _validate(self, depth: int) -> None:
        validate(self.lhs, depth)
        validate(self.rhs, depth)


@dataclass(frozen=True, slots=True)
class Implies(Formula):
    symbol: ClassVar[str] = "→"

    ant: Formula
    con: Formula

    def __repr__(self) -> str:
        return f"({self.ant!r} -> {self.con!r})"

    def sort_check(self, sig, scope: tuple = ()) -> None:
        self.ant.sort_check(sig, scope)
        self.con.sort_check(sig, scope)

    def _validate(self, depth: int) -> None:
        validate(self.ant, depth)
        validate(self.con, depth)


@dataclass(frozen=True, slots=True)
class Bottom(Formula):
    """Absurdity (falsum). Negation is sugar: Not(A) == Implies(A, Bottom())."""

    symbol: ClassVar[str] = "⊥"

    def __repr__(self) -> str:
        return self.symbol

    def sort_check(self, sig, scope: tuple = ()) -> None:
        pass  # the formula constant carries no sort

    def _validate(self, depth: int) -> None:
        pass  # no fields to check


def Not(a: Formula) -> Formula:  # noqa: N802 -- reads as the logical connective
    return Implies(a, Bottom())


# `Forall`/`Exists` override the binder-aware operations -- `abstract`/`instantiate`
# (raise the de Bruijn depth) and `sort_check` (push the bound sort onto the scope).
# `free_vars`/`subst`/`free_var_sorts` use the generic `Node` versions (correct,
# since a quantifier's only child node is `body` -- the `sort` is a str).


@dataclass(frozen=True, slots=True)
class Forall(Formula):
    """Universal quantifier (locally nameless). `body` refers to the bound
    variable via BVar(0); the bound name is gone, so `==` is alpha-equivalence.
    Build with `forall(name, sort, body)`, which abstracts the named variable."""

    symbol: ClassVar[str] = "∀"

    sort: str
    body: Formula

    def __repr__(self) -> str:
        return f"(forall :{self.sort}. {self.body!r})" if self.sort else f"(forall. {self.body!r})"

    def abstract(self, name: str, depth: int) -> Formula:
        return Forall(self.sort, cast(Formula, self.body.abstract(name, depth + 1)))

    def instantiate(self, repl: Term, depth: int) -> Formula:
        return Forall(self.sort, cast(Formula, self.body.instantiate(repl, depth + 1)))

    def sort_check(self, sig, scope: tuple = ()) -> None:
        self.body.sort_check(sig, (self.sort, *scope))

    def _validate(self, depth: int) -> None:
        _check_str(self.sort, "quantifier sort")
        validate(self.body, depth + 1)


@dataclass(frozen=True, slots=True)
class Exists(Formula):
    """Existential quantifier (locally nameless); see Forall."""

    symbol: ClassVar[str] = "∃"

    sort: str
    body: Formula

    def __repr__(self) -> str:
        return f"(exists :{self.sort}. {self.body!r})" if self.sort else f"(exists. {self.body!r})"

    def abstract(self, name: str, depth: int) -> Formula:
        return Exists(self.sort, cast(Formula, self.body.abstract(name, depth + 1)))

    def instantiate(self, repl: Term, depth: int) -> Formula:
        return Exists(self.sort, cast(Formula, self.body.instantiate(repl, depth + 1)))

    def sort_check(self, sig, scope: tuple = ()) -> None:
        self.body.sort_check(sig, (self.sort, *scope))

    def _validate(self, depth: int) -> None:
        _check_str(self.sort, "quantifier sort")
        validate(self.body, depth + 1)


# --- binder smart constructors --------------------------------------------
# `forall`/`exists` let us WRITE named binders at the surface; they `abstract` the
# named variable to a de Bruijn index. `instantiate` opens a binder with a term.


def forall(name: str, sort: str, body: Formula) -> Formula:  # noqa: N802 -- connective
    return Forall(sort, cast(Formula, body.abstract(name, 0)))


def exists(name: str, sort: str, body: Formula) -> Formula:  # noqa: N802 -- connective
    return Exists(sort, cast(Formula, body.abstract(name, 0)))


def instantiate(binder: Formula, repl: Term) -> Formula:
    """Open the outermost binder of `binder` (a Forall/Exists) with `repl`."""
    if not isinstance(binder, (Forall, Exists)):
        raise TypeError(f"not a quantifier: {binder!r}")
    return cast(Formula, binder.body.instantiate(repl, 0))


# ---------------------------------------------------------------------------
# Well-formedness validation  (the trust boundary's first gate)
# ---------------------------------------------------------------------------
# The checker compares terms and formulas with Python `==`. That is only sound if
# every value is a genuine canonical node: a hostile Term/str subclass can override
# __eq__ to return True for unequal things and derive `1 = 0` from reflexivity
# alone. So before trusting `==`, we verify EXACT types all the way down. The per-
# node field checks are the polymorphic `_validate` methods above; this `validate`
# is the GATE in front of them: it confirms `type(node)` is exactly a canonical
# class before calling the method. That ordering is the whole security argument -- a
# hostile subclass could override `_validate`, but it never runs, because its exact
# type is absent from `_CANONICAL` and the gate rejects it first.


def _check_str(s: object, what: str) -> None:
    if type(s) is not str:
        raise TypeError(f"{what} must be a genuine str, got {type(s).__name__}")


_CANONICAL: frozenset[type] = frozenset({Var, BVar, Fun, Eq, Implies, Bottom, Forall, Exists})


def validate(node: object, depth: int = 0) -> None:
    """Exact-type well-formedness for any term or formula. The trust gate: a
    hostile __eq__-overriding subclass is rejected because its exact type is not in
    `_CANONICAL`, so its `_validate` never runs. `depth` counts enclosing binders; a
    BVar is well-formed only if its index is below it (local closure: no dangling
    bound variable). Children are re-checked through this same gate."""
    if type(node) not in _CANONICAL:
        raise TypeError(f"non-canonical node: {type(node).__name__}")
    cast(Node, node)._validate(depth)


# ---------------------------------------------------------------------------
# Serialization  (generic, by reflection over the frozen-dataclass fields)
# ---------------------------------------------------------------------------
# Every node is a frozen dataclass whose fields are strings, tuples, or other
# nodes -- so we serialize generically rather than hand-coding a branch per node:
# tag each node with its class name, recurse on fields, reconstruct from a class
# registry. Adding a node needs no serialization code. Deserialized data is
# untrusted, but the checker re-validates every term/formula. `proof.py` reuses
# `encode_node`/`decode_node` with its own registry.


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
