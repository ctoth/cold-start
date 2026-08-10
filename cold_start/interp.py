"""Interpretations between theories, as checked artifacts -- the bridge layer.

An *interpretation* carries one theory's language into another's: each source
function symbol either survives verbatim or is translated RELATIONALLY through
a graph formula in the target ("x + y = z" becomes Robinson's bridge identity),
and each source predicate can be replaced by a target formula. The artifact then
owes obligations:

  - one per source axiom -- its translation must be a target theorem;
  - totality and uniqueness per translated function -- the graph must really be
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

from collections.abc import Callable, Iterable
from dataclasses import dataclass
from typing import Literal, TypeAlias, cast

from .checker import check
from .proof import Pf
from .prop import And
from .syntax import (
    Bottom,
    Eq,
    Formula,
    Fun,
    Implies,
    Node,
    Rel,
    Term,
    Var,
    exists,
    forall,
    node_size,
    subnodes,
    validate,
)
from .theory import Theory, validate_theory


class InterpError(Exception):
    """An interpretation could not be built or verified. Distinct from the
    checker's own rejection: `verify` re-raises those with the obligation
    named, so a failed payment says which debt it failed to pay."""


GraphMap: TypeAlias = dict[str, "GraphSymbol"]
PredicateMap: TypeAlias = dict[str, "PredicateSymbol"]
TermMap: TypeAlias = dict[str, "TermSymbol"]
ObligationKind: TypeAlias = Literal[
    "axiom",
    "totality",
    "uniqueness",
    "respect",
    "equivalence",
    "domain",
    "closure",
]
ObligationSubject: TypeAlias = Formula | Term | str
Payment: TypeAlias = tuple["ObligationKey", Pf]


def _require_name(value: object, label: str) -> str:
    if type(value) is not str or not value:
        raise InterpError(f"{label} must be a nonempty genuine str")
    return value


def _require_formula(value: object, label: str) -> Formula:
    try:
        validate(value)
    except (TypeError, ValueError) as exc:
        raise InterpError(f"{label} must build a canonical formula: {exc}") from exc
    if not isinstance(value, Formula):
        raise InterpError(f"{label} must build a formula, got {value!r}")
    return value


@dataclass(frozen=True)
class GraphSymbol:
    """A source function symbol translated as a relation: `graph(args, result)`
    is the target formula asserting `fun(args) = result`."""

    fun: str
    arity: int
    graph: Callable[[tuple[Term, ...], Term], Formula]

    def __post_init__(self) -> None:
        _require_name(self.fun, "graph symbol")
        if type(self.arity) is not int or self.arity < 0:
            raise InterpError(f"graph symbol arity must be a nonnegative int, got {self.arity!r}")
        _require_formula(self.instance(), f"graph symbol {self.fun!r}")

    def instance(self) -> Formula:
        """The graph at canonical fresh variables -- the shape whose size IS
        the bridge's size, and the shape the definedness obligations quantify."""
        return self.graph(self.canonical_args(), Var("c!"))

    def canonical_args(self) -> tuple[Term, ...]:
        return tuple(Var(f"x!{i}") for i in range(self.arity))


@dataclass(frozen=True)
class PredicateSymbol:
    """A source relation translated directly to a target formula.

    Predicates incur no totality or uniqueness debt: unlike a function graph,
    their interpretation need not select a result. Their formula still counts
    toward the measured bridge size.
    """

    rel: str
    arity: int
    formula: Callable[[tuple[Term, ...]], Formula]

    def __post_init__(self) -> None:
        _require_name(self.rel, "predicate symbol")
        if type(self.arity) is not int or self.arity < 0:
            raise InterpError(
                f"predicate symbol arity must be a nonnegative int, got {self.arity!r}"
            )
        _require_formula(self.instance(), f"predicate symbol {self.rel!r}")

    def instance(self) -> Formula:
        return self.formula(tuple(Var(f"x!{i}") for i in range(self.arity)))


@dataclass(frozen=True)
class TermSymbol:
    """A source function translated directly to a target term."""

    fun: str
    arity: int
    term: Callable[[tuple[Term, ...]], Term]

    def __post_init__(self) -> None:
        _require_name(self.fun, "term symbol")
        if type(self.arity) is not int or self.arity < 0:
            raise InterpError(f"term symbol arity must be a nonnegative int, got {self.arity!r}")
        value = cast(
            object,
            self.term(tuple(Var(f"x!{i}") for i in range(self.arity))),
        )
        try:
            validate(value)
        except (TypeError, ValueError) as exc:
            raise InterpError(
                f"term symbol {self.fun!r} must build a canonical term: {exc}"
            ) from exc
        if not isinstance(value, Term):
            raise InterpError(f"term symbol {self.fun!r} must build a term, got {value!r}")

    def instance(self) -> Term:
        value = cast(
            object,
            self.term(tuple(Var(f"x!{i}") for i in range(self.arity))),
        )
        if not isinstance(value, Term):
            raise InterpError(f"term symbol {self.fun!r} must build a term, got {value!r}")
        return value


@dataclass(frozen=True, slots=True)
class ObligationKey:
    """Structural payment identity; ``label`` is reporting output only."""

    kind: ObligationKind
    subject: ObligationSubject

    def __post_init__(self) -> None:
        allowed = {
            "axiom",
            "totality",
            "uniqueness",
            "respect",
            "equivalence",
            "domain",
            "closure",
        }
        if self.kind not in allowed:
            raise InterpError(f"unknown obligation kind {self.kind!r}")
        if self.kind == "axiom":
            _require_formula(self.subject, "axiom obligation subject")
        elif not isinstance(self.subject, (str, Term)):
            raise InterpError(
                f"{self.kind} obligation subject must be a name or term, got {self.subject!r}"
            )
        elif isinstance(self.subject, str) and not self.subject:
            raise InterpError(f"{self.kind} obligation subject must not be empty")

    @classmethod
    def axiom(cls, formula: Formula) -> ObligationKey:
        return cls("axiom", formula)

    @classmethod
    def totality(cls, symbol: str) -> ObligationKey:
        return cls("totality", symbol)

    @classmethod
    def uniqueness(cls, symbol: str) -> ObligationKey:
        return cls("uniqueness", symbol)

    @classmethod
    def respect(cls, symbol: str) -> ObligationKey:
        return cls("respect", symbol)

    @classmethod
    def equivalence(cls, law: str) -> ObligationKey:
        return cls("equivalence", law)

    @classmethod
    def domain(cls, law: str) -> ObligationKey:
        return cls("domain", law)

    @classmethod
    def closure(cls, symbol: str | Term) -> ObligationKey:
        return cls("closure", symbol)

    @property
    def label(self) -> str:
        subject = repr(self.subject) if isinstance(self.subject, (Formula, Term)) else self.subject
        return f"{self.kind}:{subject}"


@dataclass(frozen=True)
class Obligation:
    key: ObligationKey
    formula: Formula

    @property
    def label(self) -> str:
        return self.key.label


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
    predicates: tuple[PredicateSymbol, ...] = ()
    terms: tuple[TermSymbol, ...] = ()
    payments: tuple[Payment, ...] = ()

    # Relativization: when `domain` is set, the interpretation lands on the
    # δ-elements of the target, not all of it. Translated axioms guard their
    # (implicitly universal) free variables and their hoisted quantifiers with
    # δ, and the artifact owes more: δ must be nonempty, closed under each
    # retained function symbol, and hold of each retained constant -- else the
    # "domain" is not a structure at all. `retained_funs` lists (symbol, arity)
    # pairs that cross verbatim; `retained_consts` lists constant terms.
    domain: Callable[[Term], Formula] | None = None
    retained_funs: tuple[tuple[str, int], ...] = ()
    retained_consts: tuple[Term, ...] = ()
    retained_predicates: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        _require_name(self.name, "interpretation name")
        validate_theory(self.source)
        validate_theory(self.target)
        if (
            type(self.symbols) is not tuple
            or type(self.predicates) is not tuple
            or type(self.terms) is not tuple
        ):
            raise InterpError("interpretation graph, predicate, and term symbols must be tuples")
        if type(self.payments) is not tuple:
            raise InterpError("interpretation payments must be a tuple")
        if type(self.retained_funs) is not tuple or type(self.retained_consts) is not tuple:
            raise InterpError("retained function and constant declarations must be tuples")
        if type(self.retained_predicates) is not tuple:
            raise InterpError("retained predicate declarations must be a tuple")

        graph_names = _unique_names((symbol.fun for symbol in self.symbols), "graph symbol")
        predicate_names = _unique_names(
            (predicate.rel for predicate in self.predicates), "predicate symbol"
        )
        term_names = _unique_names((symbol.fun for symbol in self.terms), "term symbol")
        retained: dict[str, int] = {}
        for item in self.retained_funs:
            if type(item) is not tuple or len(item) != 2:
                raise InterpError("each retained function must be a (name, arity) tuple")
            name, arity = item
            _require_name(name, "retained function")
            if type(arity) is not int or arity < 0:
                raise InterpError(f"retained function arity must be nonnegative, got {arity!r}")
            if name in retained:
                raise InterpError(f"duplicate retained function {name!r}")
            retained[name] = arity
        retained_relations = _unique_names(self.retained_predicates, "retained predicate")
        overlap = (graph_names & retained.keys()) | (term_names & retained.keys())
        if overlap:
            raise InterpError(f"source function has two dispositions: {min(overlap)!r}")
        translated_overlap = graph_names & term_names
        if translated_overlap:
            raise InterpError(
                f"source function has two translations: {min(translated_overlap)!r}"
            )
        predicate_overlap = predicate_names & retained_relations
        if predicate_overlap:
            raise InterpError(f"source predicate has two dispositions: {min(predicate_overlap)!r}")

        validate_payments(self.payments)
        for const in cast(tuple[object, ...], self.retained_consts):
            if not isinstance(const, Term):
                raise InterpError(f"retained constant is not a term: {const!r}")
            validate(const)
        if self.domain is not None:
            _require_formula(self.domain(Var("x!")), "interpretation domain")

        signature = self.source.signature
        if signature is not None:
            for fun, args, _result in signature.ranks:
                disposition_arity = (
                    next((s.arity for s in self.symbols if s.fun == fun), None)
                    if fun in graph_names
                    else (
                        next((s.arity for s in self.terms if s.fun == fun), None)
                        if fun in term_names
                        else retained.get(fun)
                    )
                )
                if disposition_arity is None:
                    raise InterpError(f"missing disposition for source function {fun!r}")
                if disposition_arity != len(args):
                    raise InterpError(
                        f"source arity for {fun!r} is {len(args)}, disposition says "
                        f"{disposition_arity}"
                    )
            for rel, args in signature.relations:
                predicate = next((p for p in self.predicates if p.rel == rel), None)
                if predicate is None and rel not in retained_relations:
                    raise InterpError(f"missing disposition for source predicate {rel!r}")
                if predicate is not None and predicate.arity != len(args):
                    raise InterpError(
                        f"source arity for predicate {rel!r} is {len(args)}, disposition says "
                        f"{predicate.arity}"
                    )


def _unique_names(names: Iterable[object], label: str) -> set[str]:
    seen: set[str] = set()
    for name in names:
        valid = _require_name(name, label)
        if valid in seen:
            raise InterpError(f"duplicate {label} {valid!r}")
        seen.add(valid)
    return seen


def validate_payments(payments: tuple[Payment, ...]) -> None:
    seen: set[ObligationKey] = set()
    for raw in cast(tuple[object, ...], payments):
        if type(raw) is not tuple:
            raise InterpError("each payment must be an (ObligationKey, proof) tuple")
        item = cast(tuple[object, ...], raw)
        if len(item) != 2:
            raise InterpError("each payment must be an (ObligationKey, proof) tuple")
        key, proof = item
        if type(key) is not ObligationKey:
            raise InterpError(f"payment key is not an ObligationKey: {key!r}")
        if key in seen:
            raise InterpError(f"duplicate payment key {key.label!r}")
        if not isinstance(proof, Pf):
            raise InterpError(f"payment value is not a proof term: {proof!r}")
        seen.add(key)


# ---------------------------------------------------------------------------
# The translator
# ---------------------------------------------------------------------------


def _has_relational(node: Node, names: GraphMap) -> bool:
    return any(type(n) is Fun and n.name in names for n in subnodes(node))


def _innermost_relational(term: Term, names: GraphMap) -> Fun:
    """A deepest relational application in `term` -- its arguments are clean,
    so it can be hoisted without leaving relational symbols behind."""
    pre: list[Term] = []
    stack: list[Term] = [term]
    while stack:
        t = stack.pop()
        pre.append(t)
        if type(t) is Fun:
            stack.extend(t.args)
    for t in reversed(pre):  # children before parents: innermost first
        if type(t) is Fun and t.name in names and not _has_relational_args(t, names):
            return t
    raise InterpError(f"no relational application in {term!r}")  # caller checked


def _has_relational_args(app: Fun, names: GraphMap) -> bool:
    return any(_has_relational(a, names) for a in app.args)


def replace_term(term: Term, old: Term, new: Term) -> Term:
    """Replace every structurally-equal occurrence of `old` in `term`.
    Iterative rebuild, children before parents."""
    order: list[Term] = []
    stack: list[Term] = [term]
    while stack:
        t = stack.pop()
        order.append(t)
        if type(t) is Fun:
            stack.extend(t.args)
    done: dict[int, Term] = {}
    for t in reversed(order):
        if t == old:
            done[id(t)] = new
        elif type(t) is Fun:
            done[id(t)] = Fun(t.name, tuple(done[id(a)] for a in t.args))
        else:
            done[id(t)] = t
    return done[id(term)]


def replace_term_symbols(term: Term, symbols: TermMap) -> Term:
    """Replace direct source symbols bottom-up with validated target terms."""
    order: list[Term] = []
    stack: list[Term] = [term]
    while stack:
        node = stack.pop()
        order.append(node)
        if type(node) is Fun:
            stack.extend(node.args)
    done: dict[int, Term] = {}
    for node in reversed(order):
        if type(node) is Fun:
            args = tuple(done[id(arg)] for arg in node.args)
            symbol = symbols.get(node.name)
            if symbol is not None:
                if len(args) != symbol.arity:
                    raise InterpError(
                        f"term symbol {node.name!r} expects {symbol.arity} args, got {len(args)}"
                    )
                value = cast(object, symbol.term(args))
                try:
                    validate(value)
                except (TypeError, ValueError) as exc:
                    raise InterpError(
                        f"term symbol {node.name!r} built a noncanonical term: {exc}"
                    ) from exc
                if not isinstance(value, Term):
                    raise InterpError(
                        f"term symbol {node.name!r} built a nonterm: {value!r}"
                    )
                done[id(node)] = value
            else:
                done[id(node)] = Fun(node.name, args)
        else:
            done[id(node)] = node
    return done[id(term)]


def fresh_name(avoid: set[str]) -> str:
    k = 0
    name = "u!"
    while name in avoid:
        k += 1
        name = f"u!{k}"
    return name


def _translate_eq(
    eq: Eq,
    names: GraphMap,
    terms: TermMap,
    domain: Callable[[Term], Formula] | None,
) -> Formula:
    """One atom. Hoist nested relational applications out of both sides through
    ∀-guards; if what remains on the left is a bare relational application, the
    atom is the graph itself (the witness form), else it stays an equality."""
    guards: list[tuple[str, Formula]] = []
    avoid = set(eq.free_vars())

    def hoist(t: Term) -> Term:
        node = _innermost_relational(t, names)
        name = fresh_name(avoid)
        avoid.add(name)
        v = Var(name)
        guards.append((name, names[node.name].graph(node.args, v)))
        return replace_term(t, node, v)

    rhs = replace_term_symbols(eq.rhs, terms)
    while _has_relational(rhs, names):
        rhs = hoist(rhs)
    lhs = replace_term_symbols(eq.lhs, terms)
    while True:
        if type(lhs) is Fun and lhs.name in names and not _has_relational_args(lhs, names):
            atom: Formula = names[lhs.name].graph(lhs.args, rhs)
            break
        if not _has_relational(lhs, names):
            atom = Eq(lhs, rhs)
            break
        lhs = hoist(lhs)
    for name, guard in reversed(guards):
        body = Implies(guard, atom)
        if domain is not None:  # a hoisted variable ranges over the domain only
            body = Implies(domain(Var(name)), body)
        atom = forall(name, "", body)
    return atom


def _translate_rel(
    rel: Rel,
    names: GraphMap,
    predicates: PredicateMap,
    terms: TermMap,
    domain: Callable[[Term], Formula] | None,
) -> Formula:
    """Translate a relation atom, hoisting translated functions in its args."""
    guards: list[tuple[str, Formula]] = []
    avoid = set(rel.free_vars())

    def hoist(t: Term) -> Term:
        node = _innermost_relational(t, names)
        name = fresh_name(avoid)
        avoid.add(name)
        value = Var(name)
        guards.append((name, names[node.name].graph(node.args, value)))
        return replace_term(t, node, value)

    args: list[Term] = []
    for original in rel.args:
        arg = replace_term_symbols(original, terms)
        while _has_relational(arg, names):
            arg = hoist(arg)
        args.append(arg)

    predicate = predicates.get(rel.name)
    if predicate is None:
        atom: Formula = Rel(rel.name, tuple(args))
    else:
        if len(args) != predicate.arity:
            raise InterpError(
                f"predicate {rel.name!r} expects {predicate.arity} args, got {len(args)}"
            )
        atom = predicate.formula(tuple(args))

    for name, guard in reversed(guards):
        body = Implies(guard, atom)
        if domain is not None:
            body = Implies(domain(Var(name)), body)
        atom = forall(name, "", body)
    return atom


def translate_quantifier_free(
    formula: Formula,
    translate_equality: Callable[[Eq], Formula],
    translate_relation: Callable[[Rel], Formula] | None = None,
) -> Formula:
    """Traverse the connective spine shared by interpretation families."""
    if type(formula) is Implies:
        return Implies(
            translate_quantifier_free(formula.ant, translate_equality, translate_relation),
            translate_quantifier_free(formula.con, translate_equality, translate_relation),
        )
    if type(formula) is Bottom:
        return formula
    if type(formula) is Eq:
        return translate_equality(formula)
    if type(formula) is Rel and translate_relation is not None:
        return translate_relation(formula)
    raise InterpError(
        f"cannot translate {type(formula).__name__}: source formulas must be "
        "quantifier-free"
    )


def translate(
    f: Formula,
    symbols: tuple[GraphSymbol, ...],
    domain: Callable[[Term], Formula] | None = None,
    *,
    predicates: tuple[PredicateSymbol, ...] = (),
    terms: tuple[TermSymbol, ...] = (),
) -> Formula:
    """Translate a quantifier-free source formula through the graph symbols.
    Structure is preserved; only atoms change. Source axioms are shallow by
    nature, so the structural recursion here is harmless."""
    names = {s.fun: s for s in symbols}
    predicate_names = {p.rel: p for p in predicates}
    term_names = {s.fun: s for s in terms}

    return translate_quantifier_free(
        f,
        lambda equality: _translate_eq(equality, names, term_names, domain),
        lambda relation: _translate_rel(
            relation,
            names,
            predicate_names,
            term_names,
            domain,
        ),
    )


def translate_axiom(
    f: Formula,
    symbols: tuple[GraphSymbol, ...],
    domain: Callable[[Term], Formula] | None = None,
    *,
    predicates: tuple[PredicateSymbol, ...] = (),
    terms: tuple[TermSymbol, ...] = (),
) -> Formula:
    """A source axiom's full obligation: its translation, with the implicitly
    universal free variables guarded into the domain when relativizing."""
    out = translate(f, symbols, domain, predicates=predicates, terms=terms)
    if domain is not None:
        for name in sorted(f.free_vars(), reverse=True):
            out = Implies(domain(Var(name)), out)
    return out


# ---------------------------------------------------------------------------
# Obligations and verification
# ---------------------------------------------------------------------------


def obligations(interp: Interpretation) -> tuple[Obligation, ...]:
    """Everything the interpretation owes: translated axioms, totality and
    uniqueness per relational symbol, and -- when relativized -- the domain
    obligations (nonempty, closed under retained symbols, holding of retained
    constants). Labels are stable (the axiom's repr), so payments can be
    prepared independently of iteration order."""
    symbols, predicates, terms, dom = (
        interp.symbols,
        interp.predicates,
        interp.terms,
        interp.domain,
    )
    obs: list[Obligation] = []
    for ax in sorted(interp.source.axioms, key=repr):
        obs.append(
            Obligation(
                ObligationKey.axiom(ax),
                translate_axiom(ax, symbols, dom, predicates=predicates, terms=terms),
            )
        )
    for s in symbols:
        args = s.canonical_args()
        c, d = Var("c!"), Var("d!")
        if dom is None:
            tot: Formula = exists("c!", "", s.graph(args, c))
            uniq: Formula = Implies(s.graph(args, c), Implies(s.graph(args, d), Eq(c, d)))
        else:
            tot = exists("c!", "", And(dom(c), s.graph(args, c)))
            for t in reversed(args):
                tot = Implies(dom(t), tot)
            uniq = Implies(s.graph(args, c), Implies(s.graph(args, d), Eq(c, d)))
            for t in reversed((*args, c, d)):
                uniq = Implies(dom(t), uniq)
        obs.append(Obligation(ObligationKey.totality(s.fun), tot))
        obs.append(Obligation(ObligationKey.uniqueness(s.fun), uniq))
    if dom is not None:
        obs.append(
            Obligation(
                ObligationKey.domain("nonempty"),
                exists("x!", "", dom(Var("x!"))),
            )
        )
        for fun, arity in interp.retained_funs:
            fargs = tuple(Var(f"x!{i}") for i in range(arity))
            closed: Formula = dom(Fun(fun, fargs))
            for t in reversed(fargs):
                closed = Implies(dom(t), closed)
            obs.append(Obligation(ObligationKey.closure(fun), closed))
        for const in interp.retained_consts:
            obs.append(Obligation(ObligationKey.closure(const), dom(const)))
    return tuple(obs)


def verify_obligations(
    obs: tuple[Obligation, ...],
    payments: tuple[Payment, ...],
    target: Theory,
) -> tuple[ObligationStatus, ...]:
    """Verify one structural payment ledger against exact closed conclusions."""
    validate_payments(payments)
    known = {obligation.key for obligation in obs}
    if len(known) != len(obs):
        raise InterpError("duplicate obligation key generated by artifact")
    payment_map = {key: proof for key, proof in payments}
    for key in payment_map:
        if key not in known:
            raise InterpError(f"payment against unknown obligation {key.label!r}")
    statuses: list[ObligationStatus] = []
    for o in obs:
        pf = payment_map.get(o.key)
        if pf is None:
            statuses.append(ObligationStatus(o, paid=False, toll=0))
            continue
        try:
            seq = check(pf, target)
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
        statuses.append(ObligationStatus(o, paid=True, toll=node_size(pf)))
    return tuple(statuses)


def verify(interp: Interpretation) -> BridgeReport:
    """Verify the artifact's structural ledger and measure its bridge."""
    statuses = verify_obligations(obligations(interp), interp.payments, interp.target)
    bridge_size = sum(
        node_size(symbol.instance())
        for symbol in (*interp.symbols, *interp.predicates, *interp.terms)
    )
    return BridgeReport(name=interp.name, bridge_size=bridge_size, statuses=statuses)


__all__ = [
    "BridgeReport",
    "GraphSymbol",
    "Interpretation",
    "InterpError",
    "Obligation",
    "ObligationKey",
    "ObligationStatus",
    "Payment",
    "PredicateSymbol",
    "TermSymbol",
    "fresh_name",
    "obligations",
    "replace_term",
    "replace_term_symbols",
    "translate",
    "translate_axiom",
    "translate_quantifier_free",
    "validate_payments",
    "verify",
    "verify_obligations",
]
