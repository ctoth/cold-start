"""k-dimensional quotient interpretations -- the general TMR bridge.

`interp.py` handles the special case that carried the campaign so far: one
target element per source element, source equality staying absolute. The full
Tarski-Mostowski-Robinson notion is wider on both axes, and this module owns
the general form:

  - a source element is a k-TUPLE of target elements (dimension k);
  - source equality translates to a DEFINED formula ~ (the quotient), which
    the artifact must PROVE is an equivalence relation;
  - every translated function symbol must RESPECT ~: equivalent arguments
    force equivalent results. Respect at identical arguments is uniqueness,
    so definedness here is totality plus respect.

The translation is the same unnested graph discipline as `interp.py`, lifted
to vectors: a nested application hoists through a block of k universal
quantifiers guarded by its graph, and an equality atom between fully hoisted
sides becomes their ~. Source formulas stay quantifier-free; a binder is
rejected rather than mistranslated.

A component of the vector for `x` is the variable `x.i`. Canonical names --
argument slots `x!0..`, primed slots `y!0..`, results `c!`/`d!`, equivalence
slots `x!`/`y!`/`z!` -- follow `interp.py`'s convention so payments can be
prepared against stable obligation shapes.

Nothing here is trusted: `verify` drives every offered payment through the
trusted `check`, and an unpaid obligation is reported open, never hidden. The
report types are shared with `interp.py`, so the ledger reads both kinds of
artifact with one eye.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import TypeAlias, cast

from .interp import (
    BridgeReport,
    InterpError,
    Obligation,
    ObligationKey,
    Payment,
    fresh_name,
    replace_term,
    translate_quantifier_free,
    validate_payments,
    verify_obligations,
)
from .proof import Pf
from .syntax import (
    Eq,
    Formula,
    Fun,
    Implies,
    Node,
    Term,
    Var,
    exists,
    forall,
    subnodes,
    validate,
)
from .theory import Theory, validate_theory

Vec: TypeAlias = tuple[Term, ...]
VecMap: TypeAlias = dict[str, "VecSymbol"]


def vec(base: str, dim: int) -> Vec:
    """The canonical variable vector for `base`: components `base.1` .. `base.k`."""
    if type(base) is not str or not base:
        raise InterpError("vector base must be a nonempty genuine str")
    if type(dim) is not int or dim <= 0:
        raise InterpError(f"quotient dimension must be a positive int, got {dim!r}")
    return tuple(Var(f"{base}.{i + 1}") for i in range(dim))


@dataclass(frozen=True)
class VecSymbol:
    """A source function symbol translated as a relation on vectors:
    `graph(args, result)` is the target formula asserting that the tuple
    `result` represents `fun(args)`."""

    fun: str
    arity: int
    graph: Callable[[tuple[Vec, ...], Vec], Formula]

    def __post_init__(self) -> None:
        if type(self.fun) is not str or not self.fun:
            raise InterpError("vector symbol name must be a nonempty genuine str")
        if type(self.arity) is not int or self.arity < 0:
            raise InterpError(f"vector symbol arity must be a nonnegative int, got {self.arity!r}")

    def instance(self, dim: int) -> Formula:
        """The graph at canonical fresh vectors -- the shape whose size counts
        toward the bridge, and the shape the definedness obligations use."""
        return self.graph(self.canonical_args(dim), vec("c!", dim))

    def canonical_args(self, dim: int) -> tuple[Vec, ...]:
        return tuple(vec(f"x!{i}", dim) for i in range(self.arity))

    def primed_args(self, dim: int) -> tuple[Vec, ...]:
        return tuple(vec(f"y!{i}", dim) for i in range(self.arity))


@dataclass(frozen=True)
class QuotientInterpretation:
    """The artifact: a named k-dimensional translation between two theories,
    its defined equivalence, and the payments offered against its obligations."""

    name: str
    source: Theory
    target: Theory
    dim: int
    equiv: Callable[[Vec, Vec], Formula]
    symbols: tuple[VecSymbol, ...]
    payments: tuple[Payment, ...] = ()

    def __post_init__(self) -> None:
        if type(self.name) is not str or not self.name:
            raise InterpError("quotient interpretation name must be a nonempty genuine str")
        validate_theory(self.source)
        validate_theory(self.target)
        if type(self.dim) is not int or self.dim <= 0:
            raise InterpError(
                f"quotient dimension must be a positive int, got {self.dim!r}"
            )
        if type(self.symbols) is not tuple or type(self.payments) is not tuple:
            raise InterpError("quotient symbols and payments must be tuples")
        validate_payments(self.payments)

        equivalence = self.equiv(vec("x!", self.dim), vec("y!", self.dim))
        _require_formula(equivalence, "quotient equivalence")
        seen: set[str] = set()
        by_name: VecMap = {}
        for symbol in self.symbols:
            if symbol.fun in seen:
                raise InterpError(f"duplicate vector symbol {symbol.fun!r}")
            seen.add(symbol.fun)
            by_name[symbol.fun] = symbol
            _require_formula(
                symbol.instance(self.dim),
                f"vector graph symbol {symbol.fun!r}",
            )

        signature = self.source.signature
        if signature is not None:
            for fun, args, _result in signature.ranks:
                symbol = by_name.get(fun)
                if symbol is None:
                    raise InterpError(f"missing disposition for source function {fun!r}")
                if symbol.arity != len(args):
                    raise InterpError(
                        f"source arity for {fun!r} is {len(args)}, disposition says "
                        f"{symbol.arity}"
                    )
            if signature.relations:
                rel = signature.relations[0][0]
                raise InterpError(f"missing disposition for source predicate {rel!r}")


def _require_formula(value: object, label: str) -> Formula:
    try:
        validate(value)
    except (TypeError, ValueError) as exc:
        raise InterpError(f"{label} must build a canonical formula: {exc}") from exc
    if not isinstance(value, Formula):
        raise InterpError(f"{label} must build a formula, got {value!r}")
    return value


# ---------------------------------------------------------------------------
# The translator
# ---------------------------------------------------------------------------


def _size(node: Node | Pf) -> int:
    return sum(1 for _ in subnodes(node))


def _bind_block(marker: str, dim: int, guard: Formula, body: Formula) -> Formula:
    """Wrap `guard -> body` in the k universal quantifiers of one hoist,
    first component outermost."""
    out = Implies(guard, body)
    for i in reversed(range(dim)):
        out = forall(f"{marker}.{i + 1}", "", out)
    return out


def _innermost_app(term: Term) -> Fun | None:
    """A deepest function application whose arguments are all variables --
    hoisting it leaves no application behind inside it."""
    pre: list[Term] = []
    stack: list[Term] = [term]
    while stack:
        t = stack.pop()
        pre.append(t)
        if type(t) is Fun:
            stack.extend(t.args)
    for t in reversed(pre):  # children before parents: innermost first
        if type(t) is Fun and all(type(a) is Var for a in t.args):
            return t
    return None


def _translate_eq(
    eq: Eq,
    names: VecMap,
    equiv: Callable[[Vec, Vec], Formula],
    dim: int,
) -> Formula:
    """One atom. Hoist every application out of both sides through k-quantifier
    guard blocks; the fully hoisted equality is the defined equivalence of the
    two remaining variable vectors."""
    guards: list[tuple[str, Formula]] = []
    avoid = set(eq.free_vars())
    vectors: dict[str, Vec] = {name: vec(name, dim) for name in avoid}

    def hoist(t: Term) -> Term:
        node = _innermost_app(t)
        if node is None:
            raise InterpError(f"cannot translate {t!r}: not reducible to a variable")
        symbol = names.get(node.name)
        if symbol is None:
            raise InterpError(f"no translation for source symbol {node.name!r}")
        args = tuple(vectors[cast(Var, arg).name] for arg in node.args)  # all Vars, by choice
        marker = fresh_name(avoid)
        avoid.add(marker)
        vectors[marker] = vec(marker, dim)
        guards.append((marker, symbol.graph(args, vectors[marker])))
        return replace_term(t, node, Var(marker))

    rhs = eq.rhs
    while type(rhs) is not Var:
        rhs = hoist(rhs)
    lhs = eq.lhs
    while type(lhs) is not Var:
        lhs = hoist(lhs)
    atom = equiv(vectors[lhs.name], vectors[rhs.name])
    for marker, guard in reversed(guards):
        atom = _bind_block(marker, dim, guard, atom)
    return atom


def translate(
    f: Formula,
    symbols: tuple[VecSymbol, ...],
    equiv: Callable[[Vec, Vec], Formula],
    dim: int,
) -> Formula:
    """Translate a quantifier-free source formula through the vector graphs.
    Structure is preserved; only atoms change."""
    names = {s.fun: s for s in symbols}

    return translate_quantifier_free(
        f,
        lambda equality: _translate_eq(equality, names, equiv, dim),
    )


# ---------------------------------------------------------------------------
# Obligations and verification
# ---------------------------------------------------------------------------


def obligations(interp: QuotientInterpretation) -> tuple[Obligation, ...]:
    """Everything the quotient interpretation owes: the equivalence laws for ~,
    totality and respect per translated symbol, and one translated axiom per
    source axiom. Labels are stable, so payments can be prepared independently
    of iteration order."""
    dim, equiv = interp.dim, interp.equiv
    a, b, c = vec("x!", dim), vec("y!", dim), vec("z!", dim)
    obs: list[Obligation] = [
        Obligation(ObligationKey.equivalence("refl"), equiv(a, a)),
        Obligation(
            ObligationKey.equivalence("sym"),
            Implies(equiv(a, b), equiv(b, a)),
        ),
        Obligation(
            ObligationKey.equivalence("trans"),
            Implies(equiv(a, b), Implies(equiv(b, c), equiv(a, c))),
        ),
    ]
    for ax in sorted(interp.source.axioms, key=repr):
        obs.append(
            Obligation(
                ObligationKey.axiom(ax),
                translate(ax, interp.symbols, equiv, dim),
            )
        )
    result, other = vec("c!", dim), vec("d!", dim)
    for s in interp.symbols:
        args = s.canonical_args(dim)
        tot: Formula = s.graph(args, result)
        for i in reversed(range(dim)):
            tot = exists(f"c!.{i + 1}", "", tot)
        obs.append(Obligation(ObligationKey.totality(s.fun), tot))
        primed = s.primed_args(dim)
        resp: Formula = Implies(
            s.graph(args, result),
            Implies(s.graph(primed, other), equiv(result, other)),
        )
        for old, new in reversed(tuple(zip(args, primed, strict=True))):
            resp = Implies(equiv(old, new), resp)
        obs.append(Obligation(ObligationKey.respect(s.fun), resp))
    return tuple(obs)


def verify(interp: QuotientInterpretation) -> BridgeReport:
    """Check every offered payment through the trusted checker and measure the
    bridge. A payment must derive EXACTLY its obligation, with no hypotheses,
    in the TARGET theory. Unpaid obligations are reported open, not failed."""
    statuses = verify_obligations(obligations(interp), interp.payments, interp.target)
    dim = interp.dim
    bridge_size = _size(interp.equiv(vec("x!", dim), vec("y!", dim))) + sum(
        _size(s.instance(dim)) for s in interp.symbols
    )
    return BridgeReport(name=interp.name, bridge_size=bridge_size, statuses=statuses)


__all__ = [
    "QuotientInterpretation",
    "Vec",
    "VecSymbol",
    "obligations",
    "translate",
    "vec",
    "verify",
]
