"""Tactics: the UNTRUSTED prover half of the De Bruijn split.

Nothing in this module is trusted, and nothing in the trusted core imports it.
It emits `proof.Pf` terms -- inert recipes -- and `checker.check` is the only
authority that decides whether they are proofs. That asymmetry is the whole
point of the architecture: this file may be arbitrarily clever, heuristic, or
outright buggy, and the worst it can produce is a proof term that `check`
rejects. So it is written for convenience (plain functions, local conditionals),
not for the polymorphism discipline the trusted core lives under.

The layer is a small equational engine:

    match(pattern, target)         first-order matching, pattern Vars are holes
    Rule                           a directed equation + the Pf that justifies it
    Rule(..., ordered=True)        a permutative rule, fired only downhill
    Rule.fire(sigma)               the rewritten term and its proof, together
    rewrite_step(term, rules)      rewrite the leftmost-outermost redex
    normalize(term, rules)         rewrite to a fixpoint, Trans-chained
    normalize_equality(eq, pf, rules) transport a proved equation to normal form
    prove_eq(goal, rules)          normalize both sides, join with Trans/Sym
    by_induction(var, pred, rules) base + step by prove_eq, closed by Induct
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from dataclasses import dataclass, is_dataclass
from typing import TypeAlias, cast

from .presburger import induction
from .proof import (
    MP,
    Assume,
    Axiom,
    Cong,
    ExistsElim,
    ExistsIntro,
    ForallElim,
    ForallIntro,
    ImpIntro,
    Inst,
    Pf,
    Refl,
    Sym,
    Trans,
)
from .syntax import (
    Bottom,
    Eq,
    Exists,
    Forall,
    Formula,
    Fun,
    Implies,
    Node,
    Term,
    Var,
    instantiate,
    node_fields,
)
from .vocabulary import ZERO, S


class TacticError(Exception):
    """A tactic could not build a proof term. Distinct from the checker's
    rejection: this means we never even produced a candidate."""


Substitution: TypeAlias = dict[str, Term]
TermPath: TypeAlias = tuple[int, ...]
SymbolKey: TypeAlias = tuple[str, ...]
OrderTail: TypeAlias = str | tuple["OrderKey", ...]
OrderKey: TypeAlias = tuple[int, str, str, OrderTail]
Redex: TypeAlias = tuple[TermPath, "Rule", Substitution]
RewriteResult: TypeAlias = tuple[Term, Pf]


def _is_node(v: object) -> bool:
    return is_dataclass(v) and not isinstance(v, type)


# ---------------------------------------------------------------------------
# First-order matching
# ---------------------------------------------------------------------------


def match(
    pattern: Node,
    target: Node,
    vars: frozenset[str] | None = None,
) -> Substitution | None:
    """Match `pattern` against `target`, returning `{name: Term}` or None.

    A `Var` whose name is in `vars` is a hole and binds to whatever term sits at
    that position; every other node (including a `Var` outside `vars`) must
    match literally. `vars` defaults to all of the pattern's free variables --
    pass `frozenset()` for a ground pattern, which is how an induction
    hypothesis is used (its variable is a fixed eigenvariable, not a hole).

    Works on terms and formulas alike: the walk is generic over dataclass
    fields, so `Eq`/`Implies`/binders match structurally without special cases.
    Iterative, like everything else here."""
    if vars is None:
        vars = pattern.free_vars()
    sigma: Substitution = {}
    stack: list[tuple[Node, Node]] = [(pattern, target)]
    while stack:
        p, t = stack.pop()
        if type(p) is Var and p.name in vars:
            if not isinstance(t, Term):
                return None
            bound = sigma.get(p.name)
            if bound is None:
                sigma[p.name] = t
            elif bound != t:
                return None  # non-linear pattern, two different witnesses
            continue
        if type(p) is not type(t):
            return None
        for f in node_fields(p):
            vp = cast(object, getattr(p, f.name))
            vt = cast(object, getattr(t, f.name))
            if _is_node(vp):
                if not _is_node(vt):
                    return None
                stack.append((cast(Node, vp), cast(Node, vt)))
            elif isinstance(vp, tuple):
                left_values = cast(tuple[object, ...], vp)
                if not isinstance(vt, tuple):
                    return None
                right_values = cast(tuple[object, ...], vt)
                if len(left_values) != len(right_values):
                    return None
                for a, b in zip(
                    left_values,
                    right_values,
                    strict=True,
                ):
                    if _is_node(a):
                        if not _is_node(b):
                            return None
                        stack.append((cast(Node, a), cast(Node, b)))
                    elif a != b:
                        return None
            elif vp != vt:
                return None
    return sigma


# ---------------------------------------------------------------------------
# Rules: a directed equation plus the proof term that justifies it
# ---------------------------------------------------------------------------


def _fresh(base: str, avoid: set[str]) -> str:
    k = 0
    name = f"{base}!"
    while name in avoid:
        k += 1
        name = f"{base}!{k}"
    return name


def _subst_all(term: Term, sigma: Substitution) -> Term:
    """Simultaneous substitution of a match into a rule's right-hand side.
    Iterative (post-order over an explicit agenda). Rule equations are
    quantifier-free, so only `Var` and `Fun` occur."""
    if not sigma:
        return term
    order: list[Term] = []
    stack: list[Term] = [term]
    while stack:
        t = stack.pop()
        order.append(t)
        if type(t) is Fun:
            stack.extend(t.args)
    done: dict[int, Term] = {}
    for t in reversed(order):
        if type(t) is Var and t.name in sigma:
            done[id(t)] = sigma[t.name]
        elif type(t) is Fun:
            done[id(t)] = Fun(t.name, tuple(done[id(a)] for a in t.args))
        else:
            done[id(t)] = t
    return done[id(term)]


def _walk(term: Term) -> list[Term]:
    """`term`'s nodes in post-order -- children before parents. The shared spine
    of the two term measures below, both of which are folds up the tree."""
    order: list[Term] = []
    stack: list[Term] = [term]
    while stack:
        t = stack.pop()
        if type(t) is Var:
            order.append(t)
        elif type(t) is Fun:
            order.append(t)
            stack.extend(t.args)
        else:
            raise TacticError(f"an ordered rule measures terms; {t!r} is not one")
    order.reverse()
    return order


def _symbols(term: Term) -> tuple[SymbolKey, ...]:
    """The multiset of symbols in `term`, as a sorted tuple. Two terms with the
    same one are the same size -- which is what makes an equation between them
    *permutative*, the only kind ordered rewriting can tame."""
    out: list[SymbolKey] = []
    for t in _walk(term):
        if type(t) is Var:
            out.append(("v", t.name, t.sort))
        elif type(t) is Fun:
            out.append(("f", t.name))
        else:  # `_walk` admits nothing else
            raise AssertionError(f"unexpected term type: {type(t).__name__}")
    return tuple(sorted(out))


def _order_key(term: Term) -> OrderKey:
    """The key of the term order `ordered` rules are measured against: SIZE
    first, then the head symbol, then the arguments left to right.

    Size first is what makes the order agree with the directed rules it shares a
    rule set with. Associativity read as `(x*y)*z -> x*(y*z)` keeps the size and
    moves the bigger argument to the right, so it goes downhill here -- under a
    plain lexicographic reading of the symbols it would go UP, and re-nesting
    would fight argument-sorting forever. (It did; that is why this is a fold
    and not a flat comparison.)

    The order is total, and it survives being put into a context: a step that
    shrinks a subterm shrinks the whole, and a size-preserving one is compared
    at exactly the argument where it happened. Those two facts, plus finitely
    many terms of a given size, are the termination argument."""
    keys: dict[int, OrderKey] = {}
    for t in _walk(term):
        if type(t) is Var:
            keys[id(t)] = (1, "v", t.name, t.sort)
        elif type(t) is Fun:
            sub = tuple(keys[id(a)] for a in t.args)
            keys[id(t)] = (1 + sum(k[0] for k in sub), "f", t.name, sub)
        else:  # `_walk` admits nothing else
            raise AssertionError(f"unexpected term type: {type(t).__name__}")
    return keys[id(term)]


@dataclass(frozen=True)
class Rule:
    """A rewrite rule: read `eq` left-to-right, justified by `proof`.

    `proof` derives `eq` itself -- with no hypotheses for an axiom or a lemma,
    or under the single hypothesis `eq` for an assumption. `vars` are the names
    in `eq` that act as holes; every other variable is literal. `instance(sigma)`
    specialises the proof to a match.

    `ordered` marks a PERMUTATIVE equation -- commutativity and friends, whose
    two sides carry the same multiset of symbols. Read naively such a rule never
    stops, because its own right-hand side matches it again. An ordered rule
    instead fires only where it takes the term strictly DOWNHILL in the term
    order `_order_key` induces, which both terminates (a permutative step keeps
    the size, so each step strictly lowers a well-founded key) and canonises:
    a sum reaches the one arrangement of its summands no rule can lower. This is
    a restriction on the SEARCH only -- the proof term is the same instance of
    the same lemma, and `check` remains the only judge of it."""

    eq: Eq
    proof: Pf
    vars: frozenset[str]
    ordered: bool = False

    def __post_init__(self) -> None:
        """Catch a malformed rule where it is built, not five frames deep.

        Nothing here is a soundness check -- `check` is still the only judge.
        It is diagnosability: without it, `vars={None}` surfaces as a TypeError
        from `sorted()` inside `instance`, which names neither the rule nor the
        mistake."""
        _equation(self.eq)
        if not isinstance(cast(object, self.proof), Pf):
            raise TacticError(f"a rewrite rule needs a proof term, got {self.proof!r}")
        if not isinstance(cast(object, self.vars), frozenset):
            raise TacticError(f"a rule's holes must be a frozenset of names, got {self.vars!r}")
        for v in self.vars:
            if type(v) is not str:
                raise TacticError(f"a rule's holes must be variable names, got {v!r}")
        if self.ordered and _symbols(self.lhs) != _symbols(self.rhs):
            raise TacticError(
                f"only a permutative equation may be ordered; {self.eq!r} does not "
                f"carry the same symbols on both sides"
            )

    @property
    def lhs(self) -> Term:
        return self.eq.lhs

    @property
    def rhs(self) -> Term:
        return self.eq.rhs

    @property
    def flipped(self) -> Rule:
        """The same equation used right-to-left; the proof gains a `Sym`."""
        return Rule(Eq(self.rhs, self.lhs), Sym(self.proof), self.vars, self.ordered)

    def permits(self, target: Term, sigma: Substitution) -> bool:
        """May this rule fire at `target` under this match? Always, unless it is
        ordered -- then only where the result is strictly lower in the term
        order, which is what stops a permutative rule from cycling."""
        if not self.ordered:
            return True
        return _order_key(_subst_all(self.rhs, sigma)) < _order_key(target)

    def instance(self, sigma: Substitution) -> Pf:
        """A `Pf` of `eq` with every hole replaced per `sigma`.

        `Inst` substitutes *sequentially*, so instantiating x := y and then
        y := 0 would rewrite the `y` the first step introduced. We therefore
        rename all holes to fresh names first and only then substitute -- a
        simultaneous substitution, spelled in the trusted core's sequential
        primitive. Holes `sigma` does not mention are renamed back to
        themselves."""
        raw_sigma = cast(dict[object, object], cast(object, sigma))
        for name, term in raw_sigma.items():
            if type(name) is not str or not isinstance(term, Term):
                raise TacticError(f"a match must bind names to terms, got {name!r} -> {term!r}")
        if not self.vars:
            return self.proof
        sorts: dict[str, str] = {}
        for name, sort in self.eq.free_var_sorts():
            if sorts.setdefault(name, sort) != sort:
                raise TacticError(
                    f"variable {name!r} is used at two sorts ({sorts[name]!r} and {sort!r}) "
                    f"in {self.eq!r}"
                )
        avoid = set(self.eq.free_vars())
        for t in sigma.values():
            avoid |= set(t.free_vars())
        holes = sorted(self.vars)
        renaming: dict[str, str] = {}
        for v in holes:
            renaming[v] = _fresh(v, avoid)
            avoid.add(renaming[v])
        pf = self.proof
        for v in holes:
            pf = Inst(pf, v, Var(renaming[v], sorts.get(v, "")))
        for v in holes:
            pf = Inst(pf, renaming[v], sigma.get(v, Var(v, sorts.get(v, ""))))
        return pf

    def fire(self, sigma: Substitution) -> RewriteResult:
        """The rule applied at a match: `(rhs under sigma, Pf of lhs = rhs under
        sigma)`. Term and proof are produced together, in one place, so they
        cannot drift apart -- and if they ever did, `Trans` in the checker would
        be the one to notice."""
        pf = self.instance(sigma)  # validates sigma before it reaches _subst_all
        return _subst_all(self.rhs, sigma), pf


def _equation(f: Formula) -> Eq:
    """A rule needs an equation; anything else is a tactic-authoring mistake.
    (The axiom constants are typed `Formula`, so this is also the narrowing.)"""
    if type(f) is not Eq:
        raise TacticError(f"a rewrite rule needs an equation, got {f!r}")
    return f


def axiom_rule(eq: Formula, ordered: bool = False) -> Rule:
    """Rewrite by a theory axiom; its free variables are the holes."""
    e = _equation(eq)
    return Rule(e, Axiom(e), e.free_vars(), ordered)


def lemma_rule(eq: Formula, proof: Pf, ordered: bool = False) -> Rule:
    """Rewrite by an already-proved lemma. `proof` should derive `eq` with no
    hypotheses -- then instances stay hypothesis-free too, so a theorem built on
    lemmas comes back from `check` with an empty context.

    That precondition is NOT enforced, and cannot be here: deciding it means
    running `check` against a theory, which this module deliberately has no
    access to. Nothing is lost by that. If you pass a proof that leans on an
    assumption, the assumption rides along into every instance and surfaces in
    the sequent `check` returns -- you get a CONDITIONAL theorem where the name
    of this function promised an unconditional one, which is a disappointment,
    not a false theorem. (And if the assumed equation has free variables, `Inst`
    refuses to instantiate them at all -- it may not touch a variable free in a
    hypothesis -- so the proof term is rejected outright.) Both failure modes
    are pinned in tests/test_tactics.py."""
    e = _equation(eq)
    return Rule(e, proof, e.free_vars(), ordered)


def hypothesis_rule(eq: Formula) -> Rule:
    """Rewrite by an assumed equation -- the induction hypothesis. It is GROUND:
    its variables are fixed eigenvariables, not holes, because `Inst` may not
    instantiate a variable that is free in a hypothesis."""
    e = _equation(eq)
    return Rule(e, Assume(e), frozenset())


# ---------------------------------------------------------------------------
# Positional rewriting
# ---------------------------------------------------------------------------

DEFAULT_BUDGET = 200
"""Rewrite steps `normalize` will take before declaring the rule set looping."""


def _find_redex(term: Term, rules: Sequence[Rule]) -> Redex | None:
    """The LEFTMOST-OUTERMOST redex: `(path, rule, sigma)`, or None.

    `path` is the tuple of argument indices from `term` down to the redex. The
    search is a pre-order DFS pushing children right-to-left, so a node is tried
    before its arguments and an earlier argument before a later one; within one
    position the rules are tried in the order given. Deterministic, and the
    reason the tactics' output is reproducible.

    `rules` is re-read at every position visited, so it must be a re-iterable
    sequence; the public entry points materialize it before calling in."""
    stack: list[tuple[TermPath, Term]] = [((), term)]
    while stack:
        path, t = stack.pop()
        for rule in rules:
            sigma = match(rule.lhs, t, rule.vars)
            if sigma is not None and rule.permits(t, sigma):
                return path, rule, sigma
        if type(t) is Fun:
            for i in reversed(range(len(t.args))):
                stack.append(((*path, i), t.args[i]))
    return None


def _under_context(
    term: Term,
    path: TermPath,
    new_sub: Term,
    sub_pf: Pf,
) -> RewriteResult:
    """Lift a proof of `subterm = new_sub` at `path` to a proof about the whole
    `term`, returning the rebuilt term alongside it.

    Walking back up the path, each level becomes a `Cong` over the parent's
    function symbol whose slots are `Refl` for every argument that did not move
    and the proof so far for the one that did. That tower is "equals may be
    substituted for equals", spelled out in the primitives the checker knows."""
    spine: list[tuple[Fun, int]] = []
    node = term
    for i in path:
        if type(node) is not Fun:  # only a Fun has arguments, so only it has a path
            raise TacticError(f"cannot descend to argument {i} of {node!r}: not an application")
        spine.append((node, i))
        node = node.args[i]
    new, pf = new_sub, sub_pf
    for parent, i in reversed(spine):
        pf = Cong(parent.name, tuple(pf if j == i else Refl(a) for j, a in enumerate(parent.args)))
        new = Fun(parent.name, tuple(new if j == i else a for j, a in enumerate(parent.args)))
    return new, pf


def rewrite_step(term: Term, rules: Iterable[Rule]) -> RewriteResult | None:
    """Rewrite the leftmost-outermost redex once: `(new_term, Pf of term = new)`,
    or None if no rule applies.

    The rule proves only the redex's own equation; `_under_context` lifts that
    to the whole term."""
    found = _find_redex(term, tuple(rules))
    if found is None:
        return None
    path, rule, sigma = found
    new, pf = rule.fire(sigma)
    return _under_context(term, path, new, pf)


def normalize(
    term: Term,
    rules: Iterable[Rule],
    budget: int = DEFAULT_BUDGET,
) -> RewriteResult:
    """Rewrite to a fixpoint: `(normal_form, Pf of term = normal_form)`.

    Steps are joined with `Trans`; a term already in normal form gets `Refl`.
    `budget` bounds the number of rewrite steps actually taken -- reaching the
    fixpoint costs nothing, so a term already in normal form normalizes under a
    budget of 0, and a term needing exactly n steps normalizes under a budget of
    n. A non-terminating rule set (say, an equation used right-to-left) exceeds
    any budget and raises `TacticError` instead of hanging."""
    rules = tuple(rules)
    pf: Pf = Refl(term)
    current = term
    taken = 0
    while True:
        step = rewrite_step(current, rules)
        if step is None:
            return current, pf
        if taken == budget:
            raise TacticError(
                f"rewriting did not terminate within {budget} steps: {term!r} -> {current!r}"
            )
        current, step_pf = step
        pf = Trans(pf, step_pf)
        taken += 1


def normalize_equality(
    source: Formula,
    proof: Pf,
    rules: Iterable[Rule],
    budget: int = DEFAULT_BUDGET,
) -> Pf:
    """Transport a proof of ``lhs = rhs`` to the equality of its normal forms.

    If normalization emits ``lhs = lhs_nf`` and ``rhs = rhs_nf``, the returned
    recipe is ``lhs_nf = lhs = rhs = rhs_nf``.  This is the implication-facing
    twin of :func:`prove_eq`: it does not try to show that the two normal forms
    coincide.  Instead it preserves whatever hypotheses ``proof`` used while
    exposing the algebraic content of that equality for a later inference such
    as injectivity or cancellation.

    The caller supplies ``source`` because tactics are deliberately untrusted
    and do not derive proof conclusions.  A mismatch between it and ``proof``
    produces an invalid ``Trans`` node that the checker rejects.
    """
    eq = _equation(source)
    rules = tuple(rules)
    _, left_pf = normalize(eq.lhs, rules, budget)
    _, right_pf = normalize(eq.rhs, rules, budget)
    return Trans(Sym(left_pf), Trans(proof, right_pf))


# ---------------------------------------------------------------------------
# Transport: rewriting a whole formula along a proved equality
# ---------------------------------------------------------------------------


def _term_transport(tpat: Term, var: str, eq: Eq, eq_pf: Pf) -> Pf:
    """A recipe for ``tpat[var := eq.lhs] = tpat[var := eq.rhs]``: `eq_pf` at
    every hole, `Refl` elsewhere, `Cong` up the applications."""
    if type(tpat) is Var:
        return eq_pf if tpat.name == var else Refl(tpat)
    if type(tpat) is Fun:
        if var not in tpat.free_vars():
            return Refl(tpat)
        return Cong(tpat.name, tuple(_term_transport(a, var, eq, eq_pf) for a in tpat.args))
    raise TacticError(f"transport pattern holds {tpat!r} where a term was expected")


def transport(pattern: Formula, var: str, eq: Eq, eq_pf: Pf, pf: Pf) -> Pf:
    """Leibniz's law as a combinator: from ``pf : pattern[var := eq.lhs]`` and
    ``eq_pf : eq``, a recipe for ``pattern[var := eq.rhs]``.

    The primitives rewrite only inside equations (`Cong`/`Trans`), so moving a
    whole formula -- a divisibility, a domain membership, an induction
    predicate -- along an equality must be COMPILED: equalities bridge through
    `Cong`, implications re-introduce their rewritten antecedent (transporting
    it backwards along the flipped equality), and binders open at a fresh
    variable, move, and close again. Relation atoms have no congruence rule to
    compile into, so a pattern whose hole sits under `Rel` is rejected.

    Untrusted like every tactic: hypotheses of `pf` and `eq_pf` ride along
    honestly, and `check` remains the only judge of the result."""
    if var not in pattern.free_vars():
        return pf
    if type(pattern) is Eq:
        left = _term_transport(pattern.lhs, var, eq, eq_pf)
        right = _term_transport(pattern.rhs, var, eq, eq_pf)
        return Trans(Sym(left), Trans(pf, right))
    if type(pattern) is Implies:
        moved_ant = pattern.ant.subst(var, eq.rhs)
        back = transport(pattern.ant, var, Eq(eq.rhs, eq.lhs), Sym(eq_pf), Assume(moved_ant))
        return ImpIntro(moved_ant, transport(pattern.con, var, eq, eq_pf, MP(pf, back)))
    if type(pattern) is Forall:
        u = _fresh("t", set(pattern.free_vars()) | set(eq.free_vars()) | {var})
        opened = instantiate(pattern, Var(u, pattern.sort))
        inner = transport(opened, var, eq, eq_pf, ForallElim(pf, Var(u, pattern.sort)))
        return ForallIntro(u, pattern.sort, inner)
    if type(pattern) is Exists:
        u = _fresh("t", set(pattern.free_vars()) | set(eq.free_vars()) | {var})
        opened = instantiate(pattern, Var(u, pattern.sort))
        assumption = opened.subst(var, eq.lhs)
        moved = transport(opened, var, eq, eq_pf, Assume(assumption))
        target = pattern.subst(var, eq.rhs)
        return ExistsElim(u, pf, ExistsIntro(target, Var(u, pattern.sort), moved))
    if type(pattern) is Bottom:  # no free variables, but be total anyway
        return pf
    raise TacticError(f"cannot transport through {type(pattern).__name__}")


# ---------------------------------------------------------------------------
# Goal-directed tactics
# ---------------------------------------------------------------------------


def prove_eq(
    goal: Formula,
    rules: Iterable[Rule],
    budget: int = DEFAULT_BUDGET,
) -> Pf:
    """Prove an equation by normalizing both sides to a common normal form.

    `l = l_nf` and `r = r_nf` come from `normalize`; if the normal forms agree,
    the goal is `Trans(l = nf, Sym(r = nf))`. Otherwise the rule set does not
    decide this goal and we raise, naming both normal forms -- which is the
    single most useful thing to see when a tactic fails."""
    rules = tuple(rules)
    eq = _equation(goal)
    left_nf, left_pf = normalize(eq.lhs, rules, budget)
    right_nf, right_pf = normalize(eq.rhs, rules, budget)
    if left_nf != right_nf:
        raise TacticError(
            f"cannot prove {eq!r}: the sides have different normal forms "
            f"{left_nf!r} and {right_nf!r}"
        )
    return Trans(left_pf, Sym(right_pf))


def by_induction(
    var: str,
    pred: Formula,
    rules: Iterable[Rule],
    budget: int = DEFAULT_BUDGET,
    base: Term = ZERO,
) -> Pf:
    """Prove the equation `pred` by induction on `var`, based at `base`.

    `base` is the theory's induction base TERM -- Presburger's `ZERO` by
    default, `robinson.ONE` for the positive integers. The checker re-derives
    the base goal as `pred[var := theory.zero]`, so a mismatched `base` here
    surfaces as an honest rejection, never a false theorem.

    Base and step are each handed to `prove_eq`. The step gets one extra rule:
    the induction hypothesis, assumed as `pred` itself and therefore GROUND --
    `var` is an eigenvariable there, not a hole. `ImpIntro` then discharges that
    assumption, which is what lets `Induct` accept the result: its side
    condition forbids `var` free in any surviving hypothesis, and after the
    discharge there are none."""
    rules = tuple(rules)
    eq = _equation(pred)

    def case(label: str, goal: Formula, case_rules: Iterable[Rule]) -> Pf:
        try:
            return prove_eq(goal, case_rules, budget)
        except TacticError as exc:
            raise TacticError(f"induction on {var!r}: {label} case failed: {exc}") from exc

    base_pf = case("base", eq.subst(var, base), rules)
    step = case("step", eq.subst(var, S(Var(var))), (*rules, hypothesis_rule(eq)))
    return induction(var, eq, base_pf, ImpIntro(eq, step))


__all__ = [
    "DEFAULT_BUDGET",
    "Rule",
    "TacticError",
    "axiom_rule",
    "by_induction",
    "hypothesis_rule",
    "lemma_rule",
    "match",
    "normalize",
    "normalize_equality",
    "prove_eq",
    "rewrite_step",
    "transport",
]
