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
    Rule.fire(sigma)               the rewritten term and its proof, together
    rewrite_step(term, rules)      rewrite the leftmost-outermost redex
    normalize(term, rules)         rewrite to a fixpoint, Trans-chained
    prove_eq(goal, rules)          normalize both sides, join with Trans/Sym
    by_induction(var, pred, rules) base + step by prove_eq, closed by Induct
"""

from __future__ import annotations

from dataclasses import dataclass, is_dataclass

from .presburger import ZERO, S, induction
from .proof import Assume, Axiom, Cong, ImpIntro, Inst, Pf, Refl, Sym, Trans
from .syntax import Eq, Formula, Fun, Node, Term, Var, node_fields


class TacticError(Exception):
    """A tactic could not build a proof term. Distinct from the checker's
    rejection: this means we never even produced a candidate."""


def _is_node(v: object) -> bool:
    return is_dataclass(v) and not isinstance(v, type)


# ---------------------------------------------------------------------------
# First-order matching
# ---------------------------------------------------------------------------


def match(pattern: Node, target: Node, vars: frozenset[str] | None = None) -> dict | None:
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
    sigma: dict = {}
    stack: list = [(pattern, target)]
    while stack:
        p, t = stack.pop()
        if type(p) is Var and p.name in vars:
            bound = sigma.get(p.name)
            if bound is None:
                sigma[p.name] = t
            elif bound != t:
                return None  # non-linear pattern, two different witnesses
            continue
        if type(p) is not type(t):
            return None
        for f in node_fields(p):
            vp, vt = getattr(p, f.name), getattr(t, f.name)
            if _is_node(vp):
                stack.append((vp, vt))
            elif isinstance(vp, tuple):
                if not isinstance(vt, tuple) or len(vp) != len(vt):
                    return None
                for a, b in zip(vp, vt, strict=True):
                    if _is_node(a):
                        stack.append((a, b))
                    elif a != b:
                        return None
            elif vp != vt:
                return None
    return sigma


# ---------------------------------------------------------------------------
# Rules: a directed equation plus the proof term that justifies it
# ---------------------------------------------------------------------------


def _fresh(base: str, avoid: set) -> str:
    k = 0
    name = f"{base}!"
    while name in avoid:
        k += 1
        name = f"{base}!{k}"
    return name


def _subst_all(term: Term, sigma: dict) -> Term:
    """Simultaneous substitution of a match into a rule's right-hand side.
    Iterative (post-order over an explicit agenda). Rule equations are
    quantifier-free, so only `Var` and `Fun` occur."""
    if not sigma:
        return term
    order: list = []
    stack: list = [term]
    while stack:
        t = stack.pop()
        order.append(t)
        if type(t) is Fun:
            stack.extend(t.args)
    done: dict = {}
    for t in reversed(order):
        if type(t) is Var and t.name in sigma:
            done[id(t)] = sigma[t.name]
        elif type(t) is Fun:
            done[id(t)] = Fun(t.name, tuple(done[id(a)] for a in t.args))
        else:
            done[id(t)] = t
    return done[id(term)]


@dataclass(frozen=True)
class Rule:
    """A rewrite rule: read `eq` left-to-right, justified by `proof`.

    `proof` derives `eq` itself -- with no hypotheses for an axiom or a lemma,
    or under the single hypothesis `eq` for an assumption. `vars` are the names
    in `eq` that act as holes; every other variable is literal. `instance(sigma)`
    specialises the proof to a match.
    """

    eq: Eq
    proof: Pf
    vars: frozenset

    @property
    def lhs(self) -> Term:
        return self.eq.lhs

    @property
    def rhs(self) -> Term:
        return self.eq.rhs

    @property
    def flipped(self) -> Rule:
        """The same equation used right-to-left; the proof gains a `Sym`."""
        return Rule(Eq(self.rhs, self.lhs), Sym(self.proof), self.vars)

    def instance(self, sigma: dict) -> Pf:
        """A `Pf` of `eq` with every hole replaced per `sigma`.

        `Inst` substitutes *sequentially*, so instantiating x := y and then
        y := 0 would rewrite the `y` the first step introduced. We therefore
        rename all holes to fresh names first and only then substitute -- a
        simultaneous substitution, spelled in the trusted core's sequential
        primitive. Holes `sigma` does not mention are renamed back to
        themselves."""
        if not self.vars:
            return self.proof
        sorts = dict(self.eq.free_var_sorts())
        avoid = set(self.eq.free_vars())
        for t in sigma.values():
            avoid |= set(t.free_vars())
        holes = sorted(self.vars)
        renaming = {}
        for v in holes:
            renaming[v] = _fresh(v, avoid)
            avoid.add(renaming[v])
        pf = self.proof
        for v in holes:
            pf = Inst(pf, v, Var(renaming[v], sorts.get(v, "")))
        for v in holes:
            pf = Inst(pf, renaming[v], sigma.get(v, Var(v, sorts.get(v, ""))))
        return pf

    def fire(self, sigma: dict) -> tuple[Term, Pf]:
        """The rule applied at a match: `(rhs under sigma, Pf of lhs = rhs under
        sigma)`. Term and proof are produced together, in one place, so they
        cannot drift apart -- and if they ever did, `Trans` in the checker would
        be the one to notice."""
        return _subst_all(self.rhs, sigma), self.instance(sigma)


def _equation(f: Formula) -> Eq:
    """A rule needs an equation; anything else is a tactic-authoring mistake.
    (The axiom constants are typed `Formula`, so this is also the narrowing.)"""
    if type(f) is not Eq:
        raise TacticError(f"a rewrite rule needs an equation, got {f!r}")
    return f


def axiom_rule(eq: Formula) -> Rule:
    """Rewrite by a theory axiom; its free variables are the holes."""
    e = _equation(eq)
    return Rule(e, Axiom(e), e.free_vars())


def lemma_rule(eq: Formula, proof: Pf) -> Rule:
    """Rewrite by an already-proved lemma. `proof` must derive `eq` with no
    hypotheses -- then instances stay hypothesis-free too, so a theorem built on
    lemmas comes back from `check` with an empty context."""
    e = _equation(eq)
    return Rule(e, proof, e.free_vars())


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


def _find_redex(term: Term, rules) -> tuple | None:
    """The LEFTMOST-OUTERMOST redex: `(path, rule, sigma)`, or None.

    `path` is the tuple of argument indices from `term` down to the redex. The
    search is a pre-order DFS pushing children right-to-left, so a node is tried
    before its arguments and an earlier argument before a later one; within one
    position the rules are tried in the order given. Deterministic, and the
    reason the tactics' output is reproducible.

    `rules` is re-read at every position visited, so it must be a re-iterable
    sequence; the public entry points materialize it before calling in."""
    stack: list = [((), term)]
    while stack:
        path, t = stack.pop()
        for rule in rules:
            sigma = match(rule.lhs, t, rule.vars)
            if sigma is not None:
                return path, rule, sigma
        if type(t) is Fun:
            for i in reversed(range(len(t.args))):
                stack.append(((*path, i), t.args[i]))
    return None


def _under_context(term: Term, path: tuple, new_sub: Term, sub_pf: Pf) -> tuple[Term, Pf]:
    """Lift a proof of `subterm = new_sub` at `path` to a proof about the whole
    `term`, returning the rebuilt term alongside it.

    Walking back up the path, each level becomes a `Cong` over the parent's
    function symbol whose slots are `Refl` for every argument that did not move
    and the proof so far for the one that did. That tower is "equals may be
    substituted for equals", spelled out in the primitives the checker knows."""
    spine: list[tuple[Fun, int]] = []
    node = term
    for i in path:
        assert type(node) is Fun  # only a Fun has arguments, so only it has a path
        spine.append((node, i))
        node = node.args[i]
    new, pf = new_sub, sub_pf
    for parent, i in reversed(spine):
        pf = Cong(parent.name, tuple(pf if j == i else Refl(a) for j, a in enumerate(parent.args)))
        new = Fun(parent.name, tuple(new if j == i else a for j, a in enumerate(parent.args)))
    return new, pf


def rewrite_step(term: Term, rules) -> tuple | None:
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


def normalize(term: Term, rules, budget: int = DEFAULT_BUDGET) -> tuple:
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


# ---------------------------------------------------------------------------
# Goal-directed tactics
# ---------------------------------------------------------------------------


def prove_eq(goal: Formula, rules, budget: int = DEFAULT_BUDGET) -> Pf:
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


def by_induction(var: str, pred: Formula, rules, budget: int = DEFAULT_BUDGET) -> Pf:
    """Prove the equation `pred` by induction on `var`, over Presburger's 0/S.

    Base and step are each handed to `prove_eq`. The step gets one extra rule:
    the induction hypothesis, assumed as `pred` itself and therefore GROUND --
    `var` is an eigenvariable there, not a hole. `ImpIntro` then discharges that
    assumption, which is what lets `Induct` accept the result: its side
    condition forbids `var` free in any surviving hypothesis, and after the
    discharge there are none."""
    rules = tuple(rules)
    eq = _equation(pred)

    def case(label: str, goal: Formula, case_rules) -> Pf:
        try:
            return prove_eq(goal, case_rules, budget)
        except TacticError as exc:
            raise TacticError(f"induction on {var!r}: {label} case failed: {exc}") from exc

    base = case("base", eq.subst(var, ZERO), rules)
    step = case("step", eq.subst(var, S(Var(var))), (*rules, hypothesis_rule(eq)))
    return induction(var, eq, base, ImpIntro(eq, step))


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
    "prove_eq",
    "rewrite_step",
]
