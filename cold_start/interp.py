"""Interpretations between theories, as checked artifacts -- the bridge layer.

An *interpretation* carries one theory's language into another's: each source
function symbol either survives verbatim or is translated RELATIONALLY, through
a graph formula in the target ("x + y = z" becomes Robinson's bridge identity,
which mentions only S and multiplication). The artifact then owes obligations:

  - one per source axiom -- its translation must be a target theorem;
  - totality and uniqueness per relational symbol -- the graph must really be
    the graph of a function on the target's domain.

`verify` drives every offered payment through the trusted `check` and returns a
`BridgeReport`: which obligations are paid, at what toll (proof-term size), and
how big the bridge itself is (the translation's node count). An unpaid
obligation is REPORTED, never hidden -- an interpretation with open obligations
is a conjecture with a ledger, not a theorem.

Nothing here is trusted. This module emits and totals proof terms; `check` in
`checker.py` remains the only judge of them. The translation is the standard
unnested graph form (Tarski-Mostowski-Robinson): an equation whose head is a
relational symbol becomes the graph atom itself, and a nested application is
hoisted through a universally quantified guard, so

    a + S(b) = S(a + b)   ↦   ∀u (bridge(a,b,u) → bridge(a, S b, S u)).

Under the totality and uniqueness obligations this is equivalent to the
existential form, which is why those two obligations are not optional extras:
they are what LICENSE reading the graph as a function.

Source formulas are quantifier-free (free variables implicitly universal, as
everywhere in this repo); a binder in a source axiom is rejected rather than
mistranslated.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from .checker import Theory, check
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


class InterpError(Exception):
    """An interpretation could not be built or verified. Distinct from the
    checker's own rejection: `verify` re-raises those with the obligation
    named, so a failed payment says which debt it failed to pay."""


@dataclass(frozen=True)
class GraphSymbol:
    """A source function symbol translated as a relation: `graph(args, result)`
    is the target formula asserting `fun(args) = result`."""

    fun: str
    arity: int
    graph: Callable[[tuple[Term, ...], Term], Formula]

    def instance(self) -> Formula:
        """The graph at canonical fresh variables -- the shape whose size IS
        the bridge's size, and the shape the definedness obligations quantify."""
        return self.graph(self._args(), Var("c!"))

    def _args(self) -> tuple[Term, ...]:
        return tuple(Var(f"x!{i}") for i in range(self.arity))


@dataclass(frozen=True)
class Obligation:
    label: str
    formula: Formula


@dataclass(frozen=True)
class ObligationStatus:
    obligation: Obligation
    paid: bool
    toll: int  # proof-term node count; 0 when the obligation is open


@dataclass(frozen=True)
class BridgeReport:
    """What `verify` returns: the bridge measured. `bridge_size` counts the
    translation itself (graph formula nodes); `total_toll` counts the proof
    nodes paid to cross. The aesthetic question -- how small is the bridge? --
    is answered by the first number; the second measures the labor it cost."""

    name: str
    bridge_size: int
    statuses: tuple[ObligationStatus, ...]

    @property
    def complete(self) -> bool:
        return all(s.paid for s in self.statuses)

    @property
    def total_toll(self) -> int:
        return sum(s.toll for s in self.statuses)

    def open_labels(self) -> tuple[str, ...]:
        return tuple(s.obligation.label for s in self.statuses if not s.paid)


@dataclass(frozen=True)
class Interpretation:
    """The artifact: a named translation between two theories plus the payments
    offered against its obligations. `payments` maps obligation labels to proof
    terms; it is a tuple of pairs so the artifact stays hashable data."""

    name: str
    source: Theory
    target: Theory
    symbols: tuple[GraphSymbol, ...]
    payments: tuple[tuple[str, Pf], ...] = ()


# ---------------------------------------------------------------------------
# The translator
# ---------------------------------------------------------------------------


def _size(node: Node | Pf) -> int:
    """Node count of any syntax or proof tree -- the common measure."""
    return sum(1 for _ in subnodes(node))


def _has_relational(node: Node, names: dict) -> bool:
    return any(type(n) is Fun and n.name in names for n in subnodes(node))


def _innermost_relational(term: Term, names: dict) -> Fun:
    """A deepest relational application in `term` -- its arguments are clean,
    so it can be hoisted without leaving relational symbols behind."""
    pre: list = []
    stack: list = [term]
    while stack:
        t = stack.pop()
        pre.append(t)
        if type(t) is Fun:
            stack.extend(t.args)
    for t in reversed(pre):  # children before parents: innermost first
        if type(t) is Fun and t.name in names and not _has_relational_args(t, names):
            return t
    raise InterpError(f"no relational application in {term!r}")  # caller checked


def _has_relational_args(app: Fun, names: dict) -> bool:
    return any(_has_relational(a, names) for a in app.args)


def _replace_equal(term: Term, old: Term, new: Term) -> Term:
    """Replace every structurally-equal occurrence of `old` in `term`.
    Iterative rebuild, children before parents."""
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


def _fresh(avoid: set) -> str:
    k = 0
    name = "u!"
    while name in avoid:
        k += 1
        name = f"u!{k}"
    return name


def _translate_eq(eq: Eq, names: dict) -> Formula:
    """One atom. Hoist nested relational applications out of both sides through
    ∀-guards; if what remains on the left is a bare relational application, the
    atom is the graph itself (the witness form), else it stays an equality."""
    guards: list[tuple[str, Formula]] = []
    avoid = set(eq.free_vars())

    def hoist(t: Term) -> Term:
        node = _innermost_relational(t, names)
        name = _fresh(avoid)
        avoid.add(name)
        v = Var(name)
        guards.append((name, names[node.name].graph(node.args, v)))
        return _replace_equal(t, node, v)

    rhs = eq.rhs
    while _has_relational(rhs, names):
        rhs = hoist(rhs)
    lhs = eq.lhs
    while True:
        if type(lhs) is Fun and lhs.name in names and not _has_relational_args(lhs, names):
            atom: Formula = names[lhs.name].graph(lhs.args, rhs)
            break
        if not _has_relational(lhs, names):
            atom = Eq(lhs, rhs)
            break
        lhs = hoist(lhs)
    for name, guard in reversed(guards):
        atom = forall(name, "", Implies(guard, atom))
    return atom


def translate(f: Formula, symbols: tuple[GraphSymbol, ...]) -> Formula:
    """Translate a quantifier-free source formula through the graph symbols.
    Structure is preserved; only atoms change. Source axioms are shallow by
    nature, so the structural recursion here is harmless."""
    names = {s.fun: s for s in symbols}

    def tr(g: Formula) -> Formula:
        if type(g) is Implies:
            return Implies(tr(g.ant), tr(g.con))
        if type(g) is Bottom:
            return g
        if type(g) is Eq:
            return _translate_eq(g, names)
        raise InterpError(
            f"cannot translate {type(g).__name__}: source formulas must be quantifier-free"
        )

    return tr(f)


# ---------------------------------------------------------------------------
# Obligations and verification
# ---------------------------------------------------------------------------


def obligations(source: Theory, symbols: tuple[GraphSymbol, ...]) -> tuple[Obligation, ...]:
    """Everything the interpretation owes: translated axioms, then totality and
    uniqueness per relational symbol. Labels are stable (the axiom's repr), so
    payments can be prepared independently of iteration order."""
    obs: list[Obligation] = []
    for ax in sorted(source.axioms, key=repr):
        obs.append(Obligation(f"axiom:{ax!r}", translate(ax, symbols)))
    for s in symbols:
        args = s._args()
        c, d = Var("c!"), Var("d!")
        obs.append(Obligation(f"totality:{s.fun}", exists("c!", "", s.graph(args, c))))
        obs.append(
            Obligation(
                f"uniqueness:{s.fun}",
                Implies(s.graph(args, c), Implies(s.graph(args, d), Eq(c, d))),
            )
        )
    return tuple(obs)


def verify(interp: Interpretation) -> BridgeReport:
    """Check every offered payment through the trusted checker and measure the
    bridge. A payment must derive EXACTLY its obligation, with no hypotheses,
    in the TARGET theory; anything else raises `InterpError`. Unpaid
    obligations are reported open, not failed -- the report says so."""
    obs = obligations(interp.source, interp.symbols)
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
    bridge_size = sum(_size(s.instance()) for s in interp.symbols)
    return BridgeReport(name=interp.name, bridge_size=bridge_size, statuses=tuple(statuses))


__all__ = [
    "BridgeReport",
    "GraphSymbol",
    "Interpretation",
    "InterpError",
    "Obligation",
    "ObligationStatus",
    "obligations",
    "translate",
    "verify",
]
