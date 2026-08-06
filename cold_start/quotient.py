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
from typing import cast

from .checker import check
from .interp import BridgeReport, InterpError, Obligation, ObligationStatus
from .proof import Pf
from .syntax import (
    Bottom,
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
)
from .theory import Theory

Vec = tuple[Term, ...]


def vec(base: str, dim: int) -> Vec:
    """The canonical variable vector for `base`: components `base.1` .. `base.k`."""
    return tuple(Var(f"{base}.{i + 1}") for i in range(dim))


@dataclass(frozen=True)
class VecSymbol:
    """A source function symbol translated as a relation on vectors:
    `graph(args, result)` is the target formula asserting that the tuple
    `result` represents `fun(args)`."""

    fun: str
    arity: int
    graph: Callable[[tuple[Vec, ...], Vec], Formula]

    def instance(self, dim: int) -> Formula:
        """The graph at canonical fresh vectors -- the shape whose size counts
        toward the bridge, and the shape the definedness obligations use."""
        return self.graph(self._args(dim), vec("c!", dim))

    def _args(self, dim: int) -> tuple[Vec, ...]:
        return tuple(vec(f"x!{i}", dim) for i in range(self.arity))

    def _primed(self, dim: int) -> tuple[Vec, ...]:
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
    payments: tuple[tuple[str, Pf], ...] = ()


# ---------------------------------------------------------------------------
# The translator
# ---------------------------------------------------------------------------


def _size(node: Node | Pf) -> int:
    return sum(1 for _ in subnodes(node))


def _fresh(avoid: set) -> str:
    k = 0
    name = "u!"
    while name in avoid:
        k += 1
        name = f"u!{k}"
    return name


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
    pre: list = []
    stack: list = [term]
    while stack:
        t = stack.pop()
        pre.append(t)
        if type(t) is Fun:
            stack.extend(t.args)
    for t in reversed(pre):  # children before parents: innermost first
        if type(t) is Fun and all(type(a) is Var for a in t.args):
            return t
    return None


def _replace_equal(term: Term, old: Term, new: Term) -> Term:
    order: list = []
    stack: list = [term]
    while stack:
        t = stack.pop()
        order.append(t)
        if type(t) is Fun:
            stack.extend(t.args)
    done: dict = {}
    for t in reversed(order):
        if t == old:
            done[id(t)] = new
        elif type(t) is Fun:
            done[id(t)] = Fun(t.name, tuple(done[id(a)] for a in t.args))
        else:
            done[id(t)] = t
    return done[id(term)]


def _translate_eq(
    eq: Eq,
    names: dict,
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
        marker = _fresh(avoid)
        avoid.add(marker)
        vectors[marker] = vec(marker, dim)
        guards.append((marker, symbol.graph(args, vectors[marker])))
        return _replace_equal(t, node, Var(marker))

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

    def tr(g: Formula) -> Formula:
        if type(g) is Implies:
            return Implies(tr(g.ant), tr(g.con))
        if type(g) is Bottom:
            return g
        if type(g) is Eq:
            return _translate_eq(g, names, equiv, dim)
        raise InterpError(
            f"cannot translate {type(g).__name__}: source formulas must be quantifier-free"
        )

    return tr(f)


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
        Obligation("equivalence:refl", equiv(a, a)),
        Obligation("equivalence:sym", Implies(equiv(a, b), equiv(b, a))),
        Obligation(
            "equivalence:trans",
            Implies(equiv(a, b), Implies(equiv(b, c), equiv(a, c))),
        ),
    ]
    for ax in sorted(interp.source.axioms, key=repr):
        obs.append(
            Obligation(
                f"axiom:{ax!r}",
                translate(ax, interp.symbols, equiv, dim),
            )
        )
    result, other = vec("c!", dim), vec("d!", dim)
    for s in interp.symbols:
        args = s._args(dim)
        tot: Formula = s.graph(args, result)
        for i in reversed(range(dim)):
            tot = exists(f"c!.{i + 1}", "", tot)
        obs.append(Obligation(f"totality:{s.fun}", tot))
        primed = s._primed(dim)
        resp: Formula = Implies(
            s.graph(args, result),
            Implies(s.graph(primed, other), equiv(result, other)),
        )
        for old, new in reversed(tuple(zip(args, primed, strict=True))):
            resp = Implies(equiv(old, new), resp)
        obs.append(Obligation(f"respect:{s.fun}", resp))
    return tuple(obs)


def verify(interp: QuotientInterpretation) -> BridgeReport:
    """Check every offered payment through the trusted checker and measure the
    bridge. A payment must derive EXACTLY its obligation, with no hypotheses,
    in the TARGET theory. Unpaid obligations are reported open, not failed."""
    obs = obligations(interp)
    known = {o.label for o in obs}
    payments = dict(interp.payments)
    for label in payments:
        if label not in known:
            raise InterpError(f"payment against unknown obligation {label!r}")
    statuses: list[ObligationStatus] = []
    for o in obs:
        pf = payments.get(o.label)
        if pf is None:
            statuses.append(ObligationStatus(o, paid=False, toll=0))
            continue
        try:
            seq = check(pf, interp.target)
        except (TypeError, ValueError) as exc:
            raise InterpError(f"payment for {o.label!r} rejected by the checker: {exc}") from exc
        if seq.hyps:
            raise InterpError(
                f"payment for {o.label!r} is conditional: hypotheses {sorted(map(repr, seq.hyps))}"
            )
        if seq.concl != o.formula:
            raise InterpError(
                f"payment for {o.label!r} proves the wrong thing:\n"
                f"  owed: {o.formula!r}\n  paid: {seq.concl!r}"
            )
        statuses.append(ObligationStatus(o, paid=True, toll=_size(pf)))
    dim = interp.dim
    bridge_size = _size(interp.equiv(vec("x!", dim), vec("y!", dim))) + sum(
        _size(s.instance(dim)) for s in interp.symbols
    )
    return BridgeReport(name=interp.name, bridge_size=bridge_size, statuses=tuple(statuses))


__all__ = [
    "QuotientInterpretation",
    "Vec",
    "VecSymbol",
    "obligations",
    "translate",
    "vec",
    "verify",
]
