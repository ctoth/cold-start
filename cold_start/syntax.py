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

import hamblin


def _is_node(v: object) -> bool:
    return is_dataclass(v) and not isinstance(v, type)


def node_fields(node: object):
    """The dataclass fields of a node (guarded, so callers can pass `object`)."""
    if not is_dataclass(node) or isinstance(node, type):
        raise TypeError(f"not a node: {type(node).__name__}")
    return fields(node)


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


def subnodes(node):
    """Yield every node in the tree rooted at `node` (itself first), pre-order and
    ITERATIVELY -- the agenda is a heap list, not the call stack, so a term or
    formula nested thousands deep is walked without recursion. The traversal order
    is unspecified beyond "parent before child", which is all any caller needs."""
    stack = [node]
    while stack:
        n = stack.pop()
        yield n
        stack.extend(children(n))


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


def _rebuild(root, start_depth: int, *, on_var=None, on_bvar=None):
    """Rebuild the tree rooted at `root`, ITERATIVELY (post-order via a heap agenda,
    no recursion). `on_var(node, depth)` / `on_bvar(node, depth)` transform those
    leaves (identity if None); every other node is reassembled from its already-
    rebuilt children. `depth` rises by one under each binder, so a leaf hook sees the
    de Bruijn depth at its position -- the scope, threaded without the call stack.

    Keyed by `(id, depth)`, so the same node occurring at two depths rebuilds
    correctly. Powers `subst`/`abstract`/`instantiate`; a term or formula nested
    thousands deep is rebuilt without recursion."""
    order: list = []
    stack: list = [(root, start_depth)]
    while stack:
        n, d = stack.pop()
        order.append((n, d))
        cd = d + 1 if isinstance(n, (Forall, Exists)) else d
        for c in children(n):
            stack.append((c, cd))
    done: dict = {}
    for n, d in reversed(order):
        if type(n) is Var and on_var is not None:
            done[(id(n), d)] = on_var(n, d)
        elif type(n) is BVar and on_bvar is not None:
            done[(id(n), d)] = on_bvar(n, d)
        else:
            cd = d + 1 if isinstance(n, (Forall, Exists)) else d
            done[(id(n), d)] = map_children(n, lambda c, _cd=cd: done[(id(c), _cd)])
    return done[(id(root), start_depth)]


class Node:
    """Base of every syntax node. Operations are methods here, dispatched by class.
    The generic versions recurse over a node's children; only `Var` and the binders
    override. `abstract`/`instantiate` thread the binder depth (the scope); `Var`
    and `BVar` are the leaves that read it, and the binders raise it.
    """

    __slots__ = ()

    def __eq__(self, other: object) -> bool:
        """Structural equality -- which, for locally-nameless binders, IS alpha-
        equivalence -- computed ITERATIVELY, so deeply nested terms compare without
        recursion. Equal iff same exact type and all fields match (sub-nodes
        structurally, scalars by `==`). Replaces the dataclass-generated `__eq__`,
        whose recursion blows the stack on deep terms (hence `eq=False` on the
        node dataclasses)."""
        if self is other:
            return True
        if type(self) is not type(other):
            return False
        stack: list[tuple[object, object]] = [(self, other)]
        while stack:
            a, b = stack.pop()
            if a is b:
                continue
            if type(a) is not type(b):
                return False
            for f in node_fields(a):
                va, vb = getattr(a, f.name), getattr(b, f.name)
                if _is_node(va):
                    stack.append((va, vb))
                elif isinstance(va, tuple):
                    if not isinstance(vb, tuple) or len(va) != len(vb):
                        return False
                    for xa, xb in zip(va, vb, strict=True):
                        if _is_node(xa):
                            stack.append((xa, xb))
                        elif xa != xb:
                            return False
                elif va != vb:
                    return False
        return True

    def __hash__(self) -> int:
        """Hash consistent with `__eq__`, computed ITERATIVELY (post-order over the
        children, each node's hash built from its children's), so deeply nested
        terms hash without recursion."""
        order: list = []
        stack: list = [self]
        while stack:
            n = stack.pop()
            order.append(n)
            stack.extend(children(n))
        hashes: dict = {}
        for n in reversed(order):
            parts: list = [type(n).__name__]
            for f in node_fields(n):
                v = getattr(n, f.name)
                if _is_node(v):
                    parts.append(hashes[id(v)])
                elif isinstance(v, tuple):
                    parts.append(tuple(hashes[id(x)] if _is_node(x) else x for x in v))
                else:
                    parts.append(v)
            hashes[id(n)] = hash(tuple(parts))
        return hashes[id(self)]

    def __repr__(self) -> str:
        """Structural repr, computed ITERATIVELY (post-order over the children, each
        node's repr built from its children's), so a deeply nested term or formula
        prints without recursion. Each concrete node overrides `_repr_with`, which
        renders the node from its children's already-computed reprs (looked up by
        id). Replaces the per-class recursive `__repr__` (hence `repr=False` on the
        node dataclasses), whose recursion blew the stack on deep terms."""
        order: list = []
        stack: list = [self]
        while stack:
            n = stack.pop()
            order.append(n)
            stack.extend(children(n))
        reprs: dict = {}
        for n in reversed(order):
            reprs[id(n)] = n._repr_with(reprs)
        return reprs[id(self)]

    def _repr_with(self, reprs: dict) -> str:
        """This node's repr given its children's already-computed reprs (by id).
        Each concrete node overrides."""
        raise NotImplementedError(f"cannot repr {type(self).__name__}")

    def free_vars(self) -> frozenset:
        """Free variable names. Locally nameless, so every `Var` in the tree is free
        (a bound variable is a nameless `BVar`) -- the free names are just the names
        of the `Var` subnodes. Iterative, so arbitrarily deep terms are safe."""
        return frozenset(n.name for n in subnodes(self) if type(n) is Var)

    def subst(self, var: str, repl: Term) -> Node:
        """Replace the free variable `var` with `repl`. Locally nameless, so no
        capture-avoidance: every `Var` named `var` in the tree is free."""
        return cast(Node, _rebuild(self, 0, on_var=lambda n, d: repl if n.name == var else n))

    def abstract(self, name: str, depth: int) -> Node:
        """Close a binder: replace the free variable `name` with the bound index for
        its position (`depth` rises under each binder; `Var` becomes `BVar(d)`)."""
        def to_index(n, d):
            return BVar(d) if n.name == name else n
        return cast(Node, _rebuild(self, depth, on_var=to_index))

    def instantiate(self, repl: Term, depth: int) -> Node:
        """Open a binder: the bound variable at the binder's depth becomes `repl`;
        deeper indices shift down by one. `depth` rises under each binder."""
        def open_bvar(n, d):
            if n.index == d:
                return repl
            return BVar(n.index - 1) if n.index > d else n
        return cast(Node, _rebuild(self, depth, on_bvar=open_bvar))

    def free_var_sorts(self) -> frozenset:
        """Free `(name, sort)` pairs -- like `free_vars` but keeping each variable's
        declared sort, so the checker can enforce one sort per name. Iterative."""
        return frozenset((n.name, n.sort) for n in subnodes(self) if type(n) is Var)

    def _validate(self, depth: int) -> tuple:
        """Check this node's own fields and return the `(child, depth)` agenda the
        gate must still validate -- it does NOT recurse, so the `validate` driver can
        walk arbitrarily deep iteratively. `depth` counts enclosing binders, bounding
        legal `BVar`s. Each concrete node overrides; only called after the gate
        confirms `type(self)` is canonical."""
        raise TypeError(f"non-canonical node: {type(self).__name__}")

    def format(self, ctx, parent_prec: int = 0) -> str:
        """Render this node to surface text, parenthesizing when this node's
        structural precedence is below `parent_prec`. `ctx` is a notation-side
        printer carrying the *lexical* concerns the core syntax must not own --
        name quoting, the infix-symbol table, the constant set, fresh-name choice,
        and the bound-name stack. Each concrete node overrides; the operator's
        precedence is intrinsic to the node, the spelling comes from `ctx`."""
        raise NotImplementedError(f"cannot format {type(self).__name__}")


# ---------------------------------------------------------------------------
# Terms
# ---------------------------------------------------------------------------


class Term(Node):
    __slots__ = ()

    def subst(self, var: str, repl: Term) -> Term:  # substituting in a term yields a term
        return cast(Term, super().subst(var, repl))

    def sort_of(self, sig, scope: tuple = ()) -> str:
        """The sort of this term under signature `sig`, or raise if ill-sorted.
        `scope` is the stack of enclosing binders' sorts (a `BVar(i)` reads
        `scope[i]`); a term has no binders of its own, so `scope` is constant
        through it -- sorts and quantifiers coexist because a quantifier pushes its
        sort onto `scope` before reaching here.

        Iterative: each subterm's sort is computed bottom-up into an `id -> sort`
        map, so a term nested thousands deep is sorted without recursion."""
        order: list = []
        stack: list = [self]
        while stack:
            t = stack.pop()
            order.append(t)
            stack.extend(children(t))
        sorts: dict = {}
        for t in reversed(order):
            sorts[id(t)] = t._sort_step(sig, scope, sorts)
        return sorts[id(self)]

    def _sort_step(self, sig, scope: tuple, sorts: dict) -> str:
        """This term's sort given its subterms' already-computed `sorts` (by id).
        Each concrete term overrides."""
        raise TypeError(f"not a term: {self!r}")


@dataclass(frozen=True, slots=True, eq=False, repr=False)
class Var(Term):
    name: str
    sort: str = ""  # "" means unsorted (single-sorted theories ignore it)

    def _repr_with(self, reprs: dict) -> str:
        return f"{self.name}:{self.sort}" if self.sort else self.name

    def _sort_step(self, sig, scope: tuple, sorts: dict) -> str:
        if self.sort not in sig.sorts:
            raise ValueError(f"variable {self!r} has undeclared sort {self.sort!r}")
        return self.sort

    def _validate(self, depth: int) -> tuple:
        _check_str(self.name, "Var.name")
        _check_str(self.sort, "Var.sort")
        return ()

    def format(self, ctx, parent_prec: int = 0) -> str:
        # a bound variable's sort is implied by its binder, so suppress it there
        sort = "" if ctx.bound.get(self.name) == self.sort else self.sort
        name = ctx.name(self.name)
        return f"{name}:{ctx.name(sort)}" if sort else name


@dataclass(frozen=True, slots=True, eq=False, repr=False)
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

    def _repr_with(self, reprs: dict) -> str:
        if not self.args:
            return self.name
        return f"{self.name}({', '.join(reprs[id(a)] for a in self.args)})"

    def _sort_step(self, sig, scope: tuple, sorts: dict) -> str:
        rank = sig.rank(self.name)
        if rank is None:
            raise ValueError(f"undeclared function symbol {self.name!r}")
        arg_sorts, result = rank
        if len(self.args) != len(arg_sorts):
            raise ValueError(f"{self.name!r} expects {len(arg_sorts)} args, got {len(self.args)}")
        for a, expected in zip(self.args, arg_sorts, strict=True):
            actual = sorts[id(a)]
            if actual != expected:
                raise ValueError(f"{self.name!r} arg has sort {actual!r}, expected {expected!r}")
        return result

    def _validate(self, depth: int) -> tuple:
        _check_str(self.name, "Fun.name")
        if type(self.args) is not tuple:
            raise TypeError("Fun.args must be a tuple")
        return tuple((a, depth) for a in self.args)

    def format(self, ctx, parent_prec: int = 0) -> str:
        prec = ctx.infix.get(self.name)
        if prec is not None and len(self.args) == 2:  # binary infix: a + b
            left = self.args[0].format(ctx, prec)
            right = self.args[1].format(ctx, prec + 1)  # left-assoc: right side binds tighter
            text = f"{left} {self.name} {right}"
            return f"({text})" if prec < parent_prec else text
        name = ctx.name(self.name)
        if not self.args and (self.name in ctx.constants or self.name.isdecimal()):
            return name  # a bare constant or numeral
        args = ", ".join(a.format(ctx) for a in self.args)
        return f"{name}({args})"


@dataclass(frozen=True, slots=True, eq=False, repr=False)
class BVar(Term):
    """A bound variable, as a de Bruijn index (0 = nearest enclosing binder).

    Bound variables carry no name, so alpha-equivalent formulas are *identical*
    data: `==` is alpha-equivalence, with no fresh names and no separate alpha
    relation. The binder (Forall/Exists) records the sort.
    """

    index: int

    def _repr_with(self, reprs: dict) -> str:
        return f"#{self.index}"

    def _sort_step(self, sig, scope: tuple, sorts: dict) -> str:
        if not (0 <= self.index < len(scope)):
            raise ValueError(f"dangling bound variable {self.index!r} (scope depth {len(scope)})")
        return scope[self.index]

    def _validate(self, depth: int) -> tuple:
        if type(self.index) is not int or not (0 <= self.index < depth):
            raise TypeError(f"dangling bound variable {self.index!r} at binder depth {depth}")
        return ()

    def format(self, ctx, parent_prec: int = 0) -> str:
        raise ValueError("cannot format a dangling bound variable outside a binder")


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
        formula checks (sorts and quantifiers coexist).

        Iterative: the agenda of `(subformula, scope)` still to check is a heap list,
        so a formula nested thousands deep is checked without recursion. Each
        formula's `_sort_check_step` checks its own equalities and returns the
        sub-formula agenda (with the scope its binders extend)."""
        stack: list = [(self, scope)]
        while stack:
            f, sc = stack.pop()
            stack.extend(f._sort_check_step(sig, sc))

    def _sort_check_step(self, sig, scope: tuple) -> tuple:
        """Check this formula's own equalities; return the `(subformula, scope)`
        agenda. Each concrete formula overrides."""
        raise TypeError(f"not a formula: {self!r}")


@dataclass(frozen=True, slots=True, eq=False, repr=False)
class Eq(Formula):
    symbol: ClassVar[str] = "="

    lhs: Term
    rhs: Term

    def _repr_with(self, reprs: dict) -> str:
        return f"{reprs[id(self.lhs)]} = {reprs[id(self.rhs)]}"

    def _sort_check_step(self, sig, scope: tuple) -> tuple:
        ls, rs = self.lhs.sort_of(sig, scope), self.rhs.sort_of(sig, scope)
        if ls != rs:
            raise ValueError(f"equality across sorts: {ls!r} = {rs!r} in {self!r}")
        return ()

    def _validate(self, depth: int) -> tuple:
        return ((self.lhs, depth), (self.rhs, depth))

    def format(self, ctx, parent_prec: int = 0) -> str:
        text = f"{self.lhs.format(ctx)} {self.symbol} {self.rhs.format(ctx)}"
        return f"({text})" if 40 < parent_prec else text


@dataclass(frozen=True, slots=True, eq=False, repr=False)
class Implies(Formula):
    symbol: ClassVar[str] = "→"

    ant: Formula
    con: Formula

    def _repr_with(self, reprs: dict) -> str:
        return f"({reprs[id(self.ant)]} -> {reprs[id(self.con)]})"

    def _sort_check_step(self, sig, scope: tuple) -> tuple:
        return ((self.ant, scope), (self.con, scope))

    def _validate(self, depth: int) -> tuple:
        return ((self.ant, depth), (self.con, depth))

    def format(self, ctx, parent_prec: int = 0) -> str:
        if type(self.con) is Bottom:  # Not(A) == Implies(A, Bottom): render as ¬A
            text = "¬" + self.ant.format(ctx, 35)
            return f"({text})" if 35 < parent_prec else text
        left = self.ant.format(ctx, 11)  # right-assoc: antecedent binds tighter
        right = self.con.format(ctx, 10)
        text = f"{left} {self.symbol} {right}"
        return f"({text})" if 10 < parent_prec else text


@dataclass(frozen=True, slots=True, eq=False, repr=False)
class Bottom(Formula):
    """Absurdity (falsum). Negation is sugar: Not(A) == Implies(A, Bottom())."""

    symbol: ClassVar[str] = "⊥"

    def _repr_with(self, reprs: dict) -> str:
        return self.symbol

    def _sort_check_step(self, sig, scope: tuple) -> tuple:
        return ()  # the formula constant carries no sort and no children

    def _validate(self, depth: int) -> tuple:
        return ()  # no fields, no children

    def format(self, ctx, parent_prec: int = 0) -> str:
        return self.symbol  # an atom (prec 50): never parenthesized


def Not(a: Formula) -> Formula:  # noqa: N802 -- reads as the logical connective
    return Implies(a, Bottom())


# `Forall`/`Exists` override the scope-threaded operations that need the bound sort
# -- `sort_check` (push the sort onto the scope) and `_validate` (raise the binder
# depth). `abstract`/`instantiate` need no override: `_rebuild` raises the depth at
# every binder generically. `free_vars`/`subst`/`free_var_sorts` are the generic
# `Node` versions (a quantifier's only child node is `body`; the `sort` is a str).


@dataclass(frozen=True, slots=True, eq=False)
class Forall(Formula):
    """Universal quantifier (locally nameless). `body` refers to the bound
    variable via BVar(0); the bound name is gone, so `==` is alpha-equivalence.
    Build with `forall(name, sort, body)`, which abstracts the named variable."""

    symbol: ClassVar[str] = "∀"

    sort: str
    body: Formula

    def _repr_with(self, reprs: dict) -> str:
        b = reprs[id(self.body)]
        return f"(forall :{self.sort}. {b})" if self.sort else f"(forall. {b})"

    def _sort_check_step(self, sig, scope: tuple) -> tuple:
        return ((self.body, (self.sort, *scope)),)

    def _validate(self, depth: int) -> tuple:
        _check_str(self.sort, "quantifier sort")
        return ((self.body, depth + 1),)

    def format(self, ctx, parent_prec: int = 0) -> str:
        return _format_binder(self, ctx, parent_prec)


@dataclass(frozen=True, slots=True, eq=False)
class Exists(Formula):
    """Existential quantifier (locally nameless); see Forall."""

    symbol: ClassVar[str] = "∃"

    sort: str
    body: Formula

    def _repr_with(self, reprs: dict) -> str:
        b = reprs[id(self.body)]
        return f"(exists :{self.sort}. {b})" if self.sort else f"(exists. {b})"

    def _sort_check_step(self, sig, scope: tuple) -> tuple:
        return ((self.body, (self.sort, *scope)),)

    def _validate(self, depth: int) -> tuple:
        _check_str(self.sort, "quantifier sort")
        return ((self.body, depth + 1),)

    def format(self, ctx, parent_prec: int = 0) -> str:
        return _format_binder(self, ctx, parent_prec)


def _format_binder(binder: Forall | Exists, ctx, parent_prec: int) -> str:
    """Shared rendering for Forall/Exists (identical but for the symbol): pick a
    fresh surface name, open the binder onto it, render the body, then restore the
    naming context. The quantifier's structural precedence is 5."""
    name = ctx.fresh(binder.body.free_vars() | ctx.used)
    ctx.bound[name] = binder.sort
    ctx.used.add(name)
    opened = instantiate(binder, Var(name, binder.sort))
    body = opened.format(ctx, 0)
    ctx.used.remove(name)
    del ctx.bound[name]
    sort = f":{ctx.name(binder.sort)}" if binder.sort else ""
    text = f"{binder.symbol}{ctx.name(name)}{sort}. {body}"  # binder.symbol: ∀ or ∃
    return f"({text})" if 5 < parent_prec else text


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
    bound variable).

    Iterative: the agenda of `(node, depth)` still to check is a heap list, so a
    term or formula nested thousands deep is validated without recursion. Each
    node's `_validate` checks its own fields and returns its children's agenda; the
    gate re-confirms every node's exact type as it is popped, before trusting it."""
    stack: list = [(node, depth)]
    while stack:
        n, d = stack.pop()
        if type(n) not in _CANONICAL:
            raise TypeError(f"non-canonical node: {type(n).__name__}")
        stack.extend(cast(Node, n)._validate(d))


# ---------------------------------------------------------------------------
# Serialization  (delegated to hamblin -- a recursion-free postfix codec)
# ---------------------------------------------------------------------------
# Every node is a frozen dataclass, which is exactly what hamblin serializes: a
# postfix opcode stream read back by a stack machine, so a term or formula nested
# arbitrarily deep encodes and decodes WITHOUT recursion -- there is no
# `json.loads` at the trust boundary to blow the call stack on a deep (or hostile)
# input. The wire form is bytes, not JSON. Deserialized data is untrusted, but the
# checker re-validates every term/formula, so the codec need only refuse unknown
# kinds and mismatched field sets -- which hamblin reports as `HamblinError` (a
# `ValueError`). `proof.py` reuses the same codec with its own registry.


SYNTAX_REGISTRY = {c.__name__: c for c in (Var, BVar, Fun, Eq, Implies, Bottom, Forall, Exists)}


def term_to_bytes(t: Term) -> bytes:
    return hamblin.encode(t)


def term_from_bytes(data: bytes) -> Term:
    node = hamblin.decode(data, SYNTAX_REGISTRY)
    if not isinstance(node, Term):
        raise ValueError(f"expected a term, got {type(node).__name__}")
    return node


def formula_to_bytes(f: Formula) -> bytes:
    return hamblin.encode(f)


def formula_from_bytes(data: bytes) -> Formula:
    node = hamblin.decode(data, SYNTAX_REGISTRY)
    if not isinstance(node, Formula):
        raise ValueError(f"expected a formula, got {type(node).__name__}")
    return node
