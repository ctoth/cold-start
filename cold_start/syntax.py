"""The object language: first-order terms and formulas.

This module is NOT trusted. It is pure, immutable data plus structural helpers
(free variables and substitution). Anyone may build any term or
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

from collections.abc import Callable, Iterator
from dataclasses import Field, dataclass, fields, is_dataclass
from typing import ClassVar, Protocol, TypeAlias, cast, overload

from .work import WorkMeter


class SignatureProtocol(Protocol):
    @property
    def sorts(self) -> frozenset[str]: ...

    def rank(self, name: str) -> tuple[tuple[str, ...], str] | None: ...

    def relation(self, name: str) -> tuple[str, ...] | None: ...


Scope: TypeAlias = tuple[str, ...]
SortResults: TypeAlias = dict[int, str]
ReprItem: TypeAlias = tuple[str, object]
ReprStack: TypeAlias = list[ReprItem]


def _is_node(v: object) -> bool:
    return is_dataclass(v) and not isinstance(v, type)


def node_fields(node: object) -> tuple[Field[object], ...]:
    """The dataclass fields of a node (guarded, so callers can pass `object`)."""
    if not is_dataclass(node) or isinstance(node, type):
        raise TypeError(f"not a node: {type(node).__name__}")
    return cast(tuple[Field[object], ...], fields(node))


def children(node: object) -> list[object]:
    """Immediate sub-nodes of `node`, in field order (tuple fields flattened)."""
    if not is_dataclass(node) or isinstance(node, type):
        raise TypeError(f"not a node: {type(node).__name__}")
    out: list[object] = []
    for field_info in fields(node):
        v = cast(object, getattr(node, field_info.name))
        if _is_node(v):
            out.append(v)
        elif isinstance(v, tuple):
            out.extend(x for x in cast(tuple[object, ...], v) if _is_node(x))
    return out


@overload
def subnodes(node: Node) -> Iterator[Node]: ...


@overload
def subnodes(node: object) -> Iterator[object]: ...


def subnodes(node: object) -> Iterator[object]:
    """Yield every node in the tree rooted at `node` (itself first), pre-order and
    ITERATIVELY -- the agenda is a heap list, not the call stack, so a term or
    formula nested thousands deep is walked without recursion. The traversal order
    is unspecified beyond "parent before child", which is all any caller needs."""
    stack: list[object] = [node]
    while stack:
        n = stack.pop()
        yield n
        stack.extend(child for child in children(n) if _is_node(child))


def map_children(node: object, fn: Callable[[object], object]) -> object:
    """Rebuild `node`, replacing each immediate sub-node with `fn(sub-node)`."""
    if not is_dataclass(node) or isinstance(node, type):
        raise TypeError(f"not a node: {type(node).__name__}")
    new: dict[str, object] = {}
    for field_info in fields(node):
        v = cast(object, getattr(node, field_info.name))
        if _is_node(v):
            new[field_info.name] = fn(v)
        elif isinstance(v, tuple):
            values = cast(tuple[object, ...], v)
            new[field_info.name] = tuple(fn(x) if _is_node(x) else x for x in values)
        else:
            new[field_info.name] = v
    return type(node)(**new)


def _rebuild(
    root: Node,
    start_depth: int,
    *,
    on_var: Callable[[Var, int], Node] | None = None,
    on_bvar: Callable[[BVar, int], Node] | None = None,
    meter: WorkMeter | None = None,
) -> Node:
    """Rebuild the tree rooted at `root`, ITERATIVELY (post-order via a heap agenda,
    no recursion). `on_var(node, depth)` / `on_bvar(node, depth)` transform those
    leaves (identity if None); every other node is reassembled from its already-
    rebuilt children. `depth` rises by one under each binder, so a leaf hook sees the
    de Bruijn depth at its position -- the scope, threaded without the call stack.

    Keyed by `(id, depth)`, so the same node occurring at two depths rebuilds
    correctly. Powers `subst`/`abstract`/`instantiate`; a term or formula nested
    thousands deep is rebuilt without recursion."""
    order: list[tuple[Node, int]] = []
    stack: list[tuple[Node, int]] = [(root, start_depth)]
    while stack:
        n, d = stack.pop()
        if meter is not None:
            meter.consume("syntax_visits")
        order.append((n, d))
        cd = d + 1 if isinstance(n, (Forall, Exists)) else d
        for child in children(n):
            if _is_node(child):
                stack.append((cast(Node, child), cd))
    done: dict[tuple[int, int], Node] = {}
    for n, d in reversed(order):
        if type(n) is Var and on_var is not None:
            rebuilt = on_var(n, d)
            if meter is not None and rebuilt is not n:
                meter.consume("syntax_rebuilds")
            done[(id(n), d)] = rebuilt
        elif type(n) is BVar and on_bvar is not None:
            rebuilt = on_bvar(n, d)
            if meter is not None and rebuilt is not n:
                meter.consume("syntax_rebuilds")
            done[(id(n), d)] = rebuilt
        else:
            cd = d + 1 if isinstance(n, (Forall, Exists)) else d
            if meter is not None:
                meter.consume("syntax_rebuilds")
            done[(id(n), d)] = cast(
                Node,
                map_children(n, lambda child, _cd=cd: done[(id(child), _cd)]),
            )
    return done[(id(root), start_depth)]


def _emit_pieces(stack: ReprStack, pieces: list[ReprItem]) -> None:
    """Push `pieces` (a forward-order list of ``("emit", node)`` / ``("lit", text)``)
    so they pop left-to-right -- the shared helper for the O(n) emit-and-join repr."""
    stack.extend(reversed(pieces))


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
            for field_info in node_fields(a):
                field_name = field_info.name
                va = cast(object, getattr(a, field_name))
                vb = cast(object, getattr(b, field_name))
                if _is_node(va):
                    stack.append((va, vb))
                elif isinstance(va, tuple):
                    left_values = cast(tuple[object, ...], va)
                    if not isinstance(vb, tuple):
                        return False
                    right_values = cast(tuple[object, ...], vb)
                    if len(left_values) != len(right_values):
                        return False
                    for xa, xb in zip(left_values, right_values, strict=True):
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
        order: list[Node] = []
        stack: list[Node] = [self]
        while stack:
            n = stack.pop()
            order.append(n)
            stack.extend(cast(Node, child) for child in children(n) if _is_node(child))
        hashes: dict[int, int] = {}
        for n in reversed(order):
            parts: list[object] = [type(n).__name__]
            for field_info in node_fields(n):
                field_name = field_info.name
                v = cast(object, getattr(n, field_name))
                if _is_node(v):
                    parts.append(hashes[id(v)])
                elif isinstance(v, tuple):
                    values = cast(tuple[object, ...], v)
                    parts.append(
                        tuple(hashes[id(x)] if _is_node(x) else x for x in values)
                    )
                else:
                    parts.append(v)
            hashes[id(n)] = hash(tuple(parts))
        return hashes[id(self)]

    def __repr__(self) -> str:
        """Structural repr, computed ITERATIVELY and in O(tree size): a pre-order walk
        emits string fragments left-to-right into `out`, joined once at the end. This
        avoids both recursion (deep terms don't blow the stack) and the O(n^2)
        character-copying of building the string by re-wrapping a growing accumulator.
        Each concrete node overrides `_repr_emit`, appending leaf text to `out` and/or
        pushing child `("emit", child)` and `("lit", text)` items onto `stack`. (The
        node dataclasses set `repr=False` so this drives instead of a generated one.)"""
        out: list[str] = []
        stack: ReprStack = [("emit", self)]
        while stack:
            item = stack.pop()
            if item[0] == "lit":
                out.append(cast(str, item[1]))
            else:
                cast(Node, item[1])._repr_emit(out, stack)
        return "".join(out)

    def _repr_emit(self, out: list[str], stack: ReprStack) -> None:
        """Append this node's repr fragments to `out`, pushing children as `("emit",
        child)` and literals as `("lit", text)` (in forward order via `_emit_pieces`).
        Each concrete node overrides."""
        raise NotImplementedError(f"cannot repr {type(self).__name__}")

    def free_vars(self, meter: WorkMeter | None = None) -> frozenset[str]:
        """Free variable names. Locally nameless, so every `Var` in the tree is free
        (a bound variable is a nameless `BVar`) -- the free names are just the names
        of the `Var` subnodes. Iterative, so arbitrarily deep terms are safe."""
        if meter is not None:
            return frozenset(name for name, _sort in self.free_var_sorts(meter))
        return frozenset(n.name for n in subnodes(self) if type(n) is Var)

    def subst(self, var: str, repl: Term, meter: WorkMeter | None = None) -> Node:
        """Replace the free variable `var` with `repl`. Locally nameless, so no
        capture-avoidance: every `Var` named `var` in the tree is free."""
        return _rebuild(
            self,
            0,
            on_var=lambda n, d: repl if n.name == var else n,
            meter=meter,
        )

    def abstract(
        self, name: str, depth: int, meter: WorkMeter | None = None
    ) -> Node:
        """Close a binder: replace the free variable `name` with the bound index for
        its position (`depth` rises under each binder; `Var` becomes `BVar(d)`)."""

        def to_index(n: Var, d: int) -> Node:
            return BVar(d) if n.name == name else n

        return _rebuild(self, depth, on_var=to_index, meter=meter)

    def instantiate(
        self, repl: Term, depth: int, meter: WorkMeter | None = None
    ) -> Node:
        """Open a binder: the bound variable at the binder's depth becomes `repl`;
        deeper indices shift down by one. `depth` rises under each binder."""

        def open_bvar(n: BVar, d: int) -> Node:
            if n.index == d:
                return repl
            return BVar(n.index - 1) if n.index >= d + 1 else n

        return _rebuild(self, depth, on_bvar=open_bvar, meter=meter)

    def free_var_sorts(
        self, meter: WorkMeter | None = None
    ) -> frozenset[tuple[str, str]]:
        """Free `(name, sort)` pairs -- like `free_vars` but keeping each variable's
        declared sort, so the checker can enforce one sort per name. Iterative."""
        if meter is None:
            return frozenset(
                (n.name, n.sort) for n in subnodes(self) if type(n) is Var
            )
        cached = meter.free_var_sorts(id(self))
        if cached is not None:
            return cached
        active: set[int] = set()
        stack: list[tuple[Node, bool]] = [(self, False)]
        while stack:
            node, leaving = stack.pop()
            identity = id(node)
            if leaving:
                active.remove(identity)
                if type(node) is Var:
                    pairs = frozenset({(node.name, node.sort)})
                else:
                    collected: set[tuple[str, str]] = set()
                    for child in children(node):
                        child_pairs = meter.free_var_sorts(id(child))
                        if child_pairs is None:
                            raise RuntimeError("missing child free-variable result")
                        collected.update(child_pairs)
                    pairs = frozenset(collected)
                meter.remember_free_var_sorts(identity, pairs)
                continue
            if meter.free_var_sorts(identity) is not None:
                continue
            if identity in active:
                raise TypeError("cyclic syntax graph")
            active.add(identity)
            meter.consume("syntax_visits")
            stack.append((node, True))
            stack.extend(
                (cast(Node, child), False) for child in reversed(children(node))
            )
        result = meter.free_var_sorts(id(self))
        if result is None:
            raise RuntimeError("missing root free-variable result")
        return result

    def validation_children(self, depth: int) -> tuple[tuple[Node, int], ...]:
        """Check this node's own fields and return the `(child, depth)` agenda the
        gate must still validate -- it does NOT recurse, so the `validate` driver can
        walk arbitrarily deep iteratively. `depth` counts enclosing binders, bounding
        legal `BVar`s. Each concrete node overrides; only called after the gate
        confirms `type(self)` is canonical."""
        raise TypeError(f"non-canonical node: {type(self).__name__}")


# ---------------------------------------------------------------------------
# Terms
# ---------------------------------------------------------------------------


class Term(Node):
    __slots__ = ()

    def subst(
        self, var: str, repl: Term, meter: WorkMeter | None = None
    ) -> Term:  # substituting in a term yields a term
        return cast(Term, super().subst(var, repl, meter))

    def sort_of(
        self,
        sig: SignatureProtocol,
        scope: Scope = (),
        meter: WorkMeter | None = None,
    ) -> str:
        """The sort of this term under signature `sig`, or raise if ill-sorted.
        `scope` is the stack of enclosing binders' sorts (a `BVar(i)` reads
        `scope[i]`); a term has no binders of its own, so `scope` is constant
        through it -- sorts and quantifiers coexist because a quantifier pushes its
        sort onto `scope` before reaching here.

        Iterative: each subterm's sort is computed bottom-up into an `id -> sort`
        map, so a term nested thousands deep is sorted without recursion."""
        signature_identity = id(sig)
        if meter is not None:
            cached = meter.term_sort(signature_identity, id(self), scope)
            if cached is not None:
                return cached
        active: set[int] = set()
        sorts: SortResults = {}
        stack: list[tuple[Term, bool]] = [(self, False)]
        while stack:
            t, leaving = stack.pop()
            identity = id(t)
            if leaving:
                active.remove(identity)
                if meter is not None and type(t) is Fun:
                    meter.consume("sort_steps")
                sort = t._sort_step(sig, scope, sorts)
                sorts[identity] = sort
                if meter is not None:
                    meter.remember_term_sort(
                        signature_identity,
                        identity,
                        scope,
                        sort,
                    )
                continue
            if identity in sorts:
                continue
            if meter is not None:
                cached = meter.term_sort(signature_identity, identity, scope)
                if cached is not None:
                    sorts[identity] = cached
                    continue
            if identity in active:
                raise TypeError("cyclic term graph")
            active.add(identity)
            if meter is not None:
                meter.consume("sort_steps")
                meter.consume("syntax_visits")
            stack.append((t, True))
            stack.extend(
                (cast(Term, child), False)
                for child in reversed(children(t))
                if _is_node(child)
            )
        return sorts[id(self)]

    def _sort_step(self, sig: SignatureProtocol, scope: Scope, sorts: SortResults) -> str:
        """This term's sort given its subterms' already-computed `sorts` (by id).
        Each concrete term overrides."""
        raise TypeError(f"not a term: {self!r}")


@dataclass(frozen=True, slots=True, eq=False, repr=False)
class Var(Term):
    name: str
    sort: str = ""  # "" means unsorted (single-sorted theories ignore it)

    def _repr_emit(self, out: list[str], stack: ReprStack) -> None:
        out.append(f"{self.name}:{self.sort}" if self.sort else self.name)

    def _sort_step(self, sig: SignatureProtocol, scope: Scope, sorts: SortResults) -> str:
        if self.sort not in sig.sorts:
            raise ValueError(f"variable {self!r} has undeclared sort {self.sort!r}")
        return self.sort

    def validation_children(self, depth: int) -> tuple[tuple[Node, int], ...]:
        _check_str(self.name, "Var.name")
        _check_str(self.sort, "Var.sort")
        return ()


@dataclass(frozen=True, slots=True, eq=False, repr=False)
class Fun(Term):
    name: str
    args: tuple[Term, ...]

    def __post_init__(self) -> None:
        # Snapshot args into an immutable tuple. Without this, a caller's
        # mutable list is aliased into the term, so mutating it later would
        # retroactively rewrite a term already used in a proof. (Elements are
        # themselves immutable terms, so a shallow snapshot is deep enough.)
        if type(self.args) is not tuple:
            object.__setattr__(self, "args", tuple(self.args))

    def _repr_emit(self, out: list[str], stack: ReprStack) -> None:
        if not self.args:
            out.append(self.name)
            return
        pieces: list[ReprItem] = [("lit", self.name), ("lit", "(")]
        for k, a in enumerate(self.args):
            if k:
                pieces.append(("lit", ", "))
            pieces.append(("emit", a))
        pieces.append(("lit", ")"))
        _emit_pieces(stack, pieces)

    def _sort_step(self, sig: SignatureProtocol, scope: Scope, sorts: SortResults) -> str:
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

    def validation_children(self, depth: int) -> tuple[tuple[Node, int], ...]:
        _check_str(self.name, "Fun.name")
        if type(self.args) is not tuple:
            raise TypeError("Fun.args must be a tuple")
        return tuple((a, depth) for a in self.args)


@dataclass(frozen=True, slots=True, eq=False, repr=False)
class BVar(Term):
    """A bound variable, as a de Bruijn index (0 = nearest enclosing binder).

    Bound variables carry no name, so alpha-equivalent formulas are *identical*
    data: `==` is alpha-equivalence, with no chosen binder names and no separate alpha
    relation. The binder (Forall/Exists) records the sort.
    """

    index: int

    def _repr_emit(self, out: list[str], stack: ReprStack) -> None:
        out.append(f"#{self.index}")

    def _sort_step(self, sig: SignatureProtocol, scope: Scope, sorts: SortResults) -> str:
        if not (0 <= self.index < len(scope)):
            raise ValueError(f"dangling bound variable {self.index!r} (scope depth {len(scope)})")
        return scope[self.index]

    def validation_children(self, depth: int) -> tuple[tuple[Node, int], ...]:
        if type(self.index) is not int or not (0 <= self.index < depth):
            raise TypeError(f"dangling bound variable {self.index!r} at binder depth {depth}")
        return ()


# ---------------------------------------------------------------------------
# Formulas
# ---------------------------------------------------------------------------


class Formula(Node):
    __slots__ = ()

    def subst(
        self, var: str, repl: Term, meter: WorkMeter | None = None
    ) -> Formula:  # substituting in a formula yields a formula
        return cast(Formula, super().subst(var, repl, meter))

    def sort_check(
        self,
        sig: SignatureProtocol,
        scope: Scope = (),
        meter: WorkMeter | None = None,
    ) -> None:
        """Structural well-sortedness under `sig`: each equality relates same-sort
        terms; a binder pushes its bound sort onto `scope`, so a quantified sorted
        formula checks (sorts and quantifiers coexist).

        Iterative: the agenda of `(subformula, scope)` still to check is a heap list,
        so a formula nested thousands deep is checked without recursion. Each
        formula's `_sort_check_step` checks its own equalities and returns the
        sub-formula agenda (with the scope its binders extend)."""
        stack: list[tuple[Formula, Scope]] = [(self, scope)]
        while stack:
            f, sc = stack.pop()
            if meter is not None:
                meter.consume("sort_steps")
                meter.consume("syntax_visits")
                if type(f) is Rel:
                    meter.consume("sort_steps")
            if type(f) is Eq:
                left_sort = f.lhs.sort_of(sig, sc, meter)
                right_sort = f.rhs.sort_of(sig, sc, meter)
                if left_sort != right_sort:
                    raise ValueError(
                        f"equality across sorts: {left_sort!r} = {right_sort!r} in {f!r}"
                    )
                continue
            if type(f) is Rel:
                arg_sorts = sig.relation(f.name)
                if arg_sorts is None:
                    raise ValueError(f"undeclared relation {f.name!r}")
                if len(f.args) != len(arg_sorts):
                    raise ValueError(
                        f"{f.name!r} expects {len(arg_sorts)} args, got {len(f.args)}"
                    )
                for arg, expected in zip(f.args, arg_sorts, strict=True):
                    actual = arg.sort_of(sig, sc, meter)
                    if actual != expected:
                        raise ValueError(
                            f"{f.name!r} arg has sort {actual!r}, expected {expected!r}"
                        )
                continue
            stack.extend(f._sort_check_step(sig, sc))

    def _sort_check_step(
        self,
        sig: SignatureProtocol,
        scope: Scope,
    ) -> tuple[tuple[Formula, Scope], ...]:
        """Check this formula's own equalities; return the `(subformula, scope)`
        agenda. Each concrete formula overrides."""
        raise TypeError(f"not a formula: {self!r}")


@dataclass(frozen=True, slots=True, eq=False, repr=False)
class Eq(Formula):
    symbol: ClassVar[str] = "="

    lhs: Term
    rhs: Term

    def _repr_emit(self, out: list[str], stack: ReprStack) -> None:
        _emit_pieces(stack, [("emit", self.lhs), ("lit", " = "), ("emit", self.rhs)])

    def validation_children(self, depth: int) -> tuple[tuple[Node, int], ...]:
        return ((self.lhs, depth), (self.rhs, depth))


@dataclass(frozen=True, slots=True, eq=False, repr=False)
class Rel(Formula):
    """An atomic relation application such as divisibility ``a | b``."""

    symbol: ClassVar[str] = "relation"

    name: str
    args: tuple[Term, ...]

    def __post_init__(self) -> None:
        # Relations have the same immutable argument ownership as functions.
        if type(self.args) is not tuple:
            object.__setattr__(self, "args", tuple(self.args))

    def _repr_emit(self, out: list[str], stack: ReprStack) -> None:
        if self.name == "|" and len(self.args) == 2:
            _emit_pieces(
                stack,
                [("emit", self.args[0]), ("lit", " | "), ("emit", self.args[1])],
            )
            return
        pieces: list[ReprItem] = [("lit", self.name), ("lit", "(")]
        for k, arg in enumerate(self.args):
            if k:
                pieces.append(("lit", ", "))
            pieces.append(("emit", arg))
        pieces.append(("lit", ")"))
        _emit_pieces(stack, pieces)

    def validation_children(self, depth: int) -> tuple[tuple[Node, int], ...]:
        _check_str(self.name, "Rel.name")
        if type(self.args) is not tuple:
            raise TypeError("Rel.args must be a tuple")
        return tuple((arg, depth) for arg in self.args)


@dataclass(frozen=True, slots=True, eq=False, repr=False)
class Implies(Formula):
    symbol: ClassVar[str] = "→"

    ant: Formula
    con: Formula

    def _repr_emit(self, out: list[str], stack: ReprStack) -> None:
        _emit_pieces(
            stack,
            [("lit", "("), ("emit", self.ant), ("lit", " -> "), ("emit", self.con), ("lit", ")")],
        )

    def _sort_check_step(
        self,
        sig: SignatureProtocol,
        scope: Scope,
    ) -> tuple[tuple[Formula, Scope], ...]:
        return ((self.ant, scope), (self.con, scope))

    def validation_children(self, depth: int) -> tuple[tuple[Node, int], ...]:
        return ((self.ant, depth), (self.con, depth))


@dataclass(frozen=True, slots=True, eq=False, repr=False)
class Bottom(Formula):
    """Absurdity (falsum). Negation is sugar: Not(A) == Implies(A, Bottom())."""

    symbol: ClassVar[str] = "⊥"

    def _repr_emit(self, out: list[str], stack: ReprStack) -> None:
        out.append(self.symbol)

    def _sort_check_step(
        self,
        sig: SignatureProtocol,
        scope: Scope,
    ) -> tuple[tuple[Formula, Scope], ...]:
        return ()  # the formula constant carries no sort and no children

    def validation_children(self, depth: int) -> tuple[tuple[Node, int], ...]:
        return ()  # no fields, no children


def Not(a: Formula) -> Formula:  # noqa: N802 -- reads as the logical connective
    return Implies(a, Bottom())


# `Forall`/`Exists` override the scope-threaded operations that need the bound sort
# -- `sort_check` (push the sort onto the scope) and `_validate` (raise the binder
# depth). `abstract`/`instantiate` need no override: `_rebuild` raises the depth at
# every binder generically. `free_vars`/`subst`/`free_var_sorts` are the generic
# `Node` versions (a quantifier's only child node is `body`; the `sort` is a str).


@dataclass(frozen=True, slots=True, eq=False, repr=False)
class Forall(Formula):
    """Universal quantifier (locally nameless). `body` refers to the bound
    variable via BVar(0); the bound name is gone, so `==` is alpha-equivalence.
    Build with `forall(name, sort, body)`, which abstracts the named variable."""

    symbol: ClassVar[str] = "∀"

    sort: str
    body: Formula

    def _repr_emit(self, out: list[str], stack: ReprStack) -> None:
        head = f"(forall :{self.sort}. " if self.sort else "(forall. "
        _emit_pieces(stack, [("lit", head), ("emit", self.body), ("lit", ")")])

    def _sort_check_step(
        self,
        sig: SignatureProtocol,
        scope: Scope,
    ) -> tuple[tuple[Formula, Scope], ...]:
        return ((self.body, (self.sort, *scope)),)

    def validation_children(self, depth: int) -> tuple[tuple[Node, int], ...]:
        _check_str(self.sort, "quantifier sort")
        return ((self.body, depth + 1),)


@dataclass(frozen=True, slots=True, eq=False, repr=False)
class Exists(Formula):
    """Existential quantifier (locally nameless); see Forall."""

    symbol: ClassVar[str] = "∃"

    sort: str
    body: Formula

    def _repr_emit(self, out: list[str], stack: ReprStack) -> None:
        head = f"(exists :{self.sort}. " if self.sort else "(exists. "
        _emit_pieces(stack, [("lit", head), ("emit", self.body), ("lit", ")")])

    def _sort_check_step(
        self,
        sig: SignatureProtocol,
        scope: Scope,
    ) -> tuple[tuple[Formula, Scope], ...]:
        return ((self.body, (self.sort, *scope)),)

    def validation_children(self, depth: int) -> tuple[tuple[Node, int], ...]:
        _check_str(self.sort, "quantifier sort")
        return ((self.body, depth + 1),)


# --- binder smart constructors --------------------------------------------
# `forall`/`exists` let us WRITE named binders at the surface; they `abstract` the
# named variable to a de Bruijn index. `instantiate` opens a binder with a term.


def forall(  # noqa: N802 -- connective
    name: str,
    sort: str,
    body: Formula,
    meter: WorkMeter | None = None,
) -> Formula:
    if meter is not None:
        meter.consume("syntax_rebuilds")
    return Forall(sort, cast(Formula, body.abstract(name, 0, meter)))


def exists(  # noqa: N802 -- connective
    name: str,
    sort: str,
    body: Formula,
    meter: WorkMeter | None = None,
) -> Formula:
    if meter is not None:
        meter.consume("syntax_rebuilds")
    return Exists(sort, cast(Formula, body.abstract(name, 0, meter)))


def instantiate(
    binder: Formula, repl: Term, meter: WorkMeter | None = None
) -> Formula:
    """Open the outermost binder of `binder` (a Forall/Exists) with `repl`."""
    if not isinstance(binder, (Forall, Exists)):
        raise TypeError(f"not a quantifier: {binder!r}")
    return cast(Formula, binder.body.instantiate(repl, 0, meter))


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
# type is absent from `CANONICAL_NODE_TYPES` and the gate rejects it first.


def _check_str(s: object, what: str) -> None:
    if type(s) is not str:
        raise TypeError(f"{what} must be a genuine str, got {type(s).__name__}")


CANONICAL_NODE_TYPES: frozenset[type[Node]] = frozenset(
    {Var, BVar, Fun, Eq, Rel, Implies, Bottom, Forall, Exists}
)


def _validation_strings(node: Node) -> tuple[str, ...]:
    """Return scalar strings with exact-type dispatch at the trust gate."""
    match node:
        case Var(name=name, sort=sort):
            return (name, sort)
        case Fun(name=name):
            return (name,)
        case Rel(name=name):
            return (name,)
        case Forall(sort=sort) | Exists(sort=sort):
            return (sort,)
        case BVar() | Eq() | Implies() | Bottom():
            return ()
        case _:
            raise TypeError(f"non-canonical node: {type(node).__name__}")


def validate(
    node: object,
    depth: int = 0,
    meter: WorkMeter | None = None,
) -> None:
    """Exact-type well-formedness for any term or formula. The trust gate: a
    hostile __eq__-overriding subclass is rejected because its exact type is not in
    `CANONICAL_NODE_TYPES`, so its `_validate` never runs. `depth` counts enclosing binders; a
    BVar is well-formed only if its index is below it (local closure: no dangling
    bound variable).

    Iterative: the agenda of `(node, depth)` still to check is a heap list, so a
    term or formula nested thousands deep is validated without recursion. Each
    node's `_validate` checks its own fields and returns its children's agenda; the
    gate re-confirms every node's exact type as it is popped, before trusting it."""
    stack: list[tuple[object, int]] = [(node, depth)]
    while stack:
        n, d = stack.pop()
        if type(n) not in CANONICAL_NODE_TYPES:
            raise TypeError(f"non-canonical node: {type(n).__name__}")
        canonical = cast(Node, n)
        agenda = canonical.validation_children(d)
        if meter is not None:
            meter.consume("syntax_visits")
            if meter.input_syntax(id(canonical), len(agenda)):
                for value in _validation_strings(canonical):
                    meter.inspect_string(value)
        stack.extend(agenda)
