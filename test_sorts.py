"""Many-sorted soundness and sort-checking (Hypothesis).

Sorts give a whole new family of invariants: every theorem stays well-sorted,
you cannot instantiate across sorts, ill-sorted terms are rejected, and proofs
hold in a *sorted* model with disjoint carriers per sort. Exercised on a monoid
M acting on a set X -- the shape that becomes scalars acting on vectors.
"""

from __future__ import annotations

from dataclasses import dataclass

from hypothesis import assume, given, settings
from hypothesis import strategies as st

import cold_start.proof as P
from cold_start.algebra import (
    ACT_ID,
    ACTION_SIG,
    M_LEFT_ID,
    MONOID_ACTION,
    E,
    act,
    mul,
)
from cold_start.checker import check, sort_check_formula
from cold_start.syntax import Eq, Fun, Implies, Term, Var

M_VARS = [Var("m", "M"), Var("n", "M"), Var("p", "M")]
X_VARS = [Var("x", "X"), Var("y", "X")]


# --- a sorted model: T_2 (transformations of {0,1}) acting on {0,1} --------


@dataclass
class SortedModel:
    name: str
    carriers: dict  # sort -> Hypothesis strategy
    interp: dict  # symbol -> callable


def _compose(g, f):  # (g o f)(i) = g(f(i)); transformations are tuples (h0, h1)
    return (g[f[0]], g[f[1]])


ACT_MODEL = SortedModel(
    "T_2 acting on {0,1}",
    carriers={
        "M": st.sampled_from([(0, 0), (0, 1), (1, 0), (1, 1)]),
        "X": st.sampled_from([0, 1]),
    },
    interp={"e": lambda: (0, 1), "*": _compose, "act": lambda f, x: f[x]},
)


def interp_term(t: Term, model: SortedModel, env: dict):
    if type(t) is Var:
        return env[t.name]
    if type(t) is Fun:
        return model.interp[t.name](*[interp_term(a, model, env) for a in t.args])
    raise TypeError(repr(t))


def interp_formula(f, model: SortedModel, env: dict) -> bool:
    if type(f) is Eq:
        return interp_term(f.lhs, model, env) == interp_term(f.rhs, model, env)
    if type(f) is Implies:
        return (not interp_formula(f.ant, model, env)) or interp_formula(f.con, model, env)
    raise TypeError(repr(f))


def _vars_with_sorts(obj, out: set) -> None:
    if type(obj) is Var:
        out.add((obj.name, obj.sort))
    elif type(obj) is Fun:
        for a in obj.args:
            _vars_with_sorts(a, out)
    elif type(obj) is Eq:
        _vars_with_sorts(obj.lhs, out)
        _vars_with_sorts(obj.rhs, out)
    elif type(obj) is Implies:
        _vars_with_sorts(obj.ant, out)
        _vars_with_sorts(obj.con, out)


def env_for(concl, model: SortedModel, data) -> dict:
    out: set = set()
    _vars_with_sorts(concl, out)
    return {name: data.draw(model.carriers[sort]) for name, sort in out}


@given(st.data())
@settings(max_examples=200)
def test_model_satisfies_action_axioms(data):
    for ax in MONOID_ACTION.axioms:
        env = env_for(ax, ACT_MODEL, data)
        assert interp_formula(ax, ACT_MODEL, env), f"model fails {ax!r}"


# --- a worked sorted proof ------------------------------------------------


def test_sorted_proof_checks():
    # act(e, act(e, x)) = x : inst ACT_ID at x := act(e,x), then trans with ACT_ID
    x = Var("x", "X")
    inner = act(E, x)
    step1 = P.Inst(P.Axiom(ACT_ID), "x", inner)  # act(e, act(e,x)) = act(e,x)
    step2 = P.Axiom(ACT_ID)  # act(e,x) = x
    seq = check(P.Trans(step1, step2), MONOID_ACTION)
    assert seq.concl == Eq(act(E, act(E, x)), x)
    assert seq.hyps == frozenset()


# --- sort-checking rejects malformed proofs -------------------------------


def test_cross_sort_instantiation_rejected():
    # M_LEFT_ID is `e*m = m` with m : M. Instantiating m with an X-term is a
    # sort error -- the heart of why sorts matter.
    bad = P.Inst(P.Axiom(M_LEFT_ID), "m", Var("x", "X"))
    try:
        check(bad, MONOID_ACTION)
    except ValueError:
        return
    raise AssertionError("instantiated an M-variable with an X-term")


def test_ill_sorted_term_rejected():
    # act expects (M, X); feeding (X, M) is ill-sorted.
    bad = P.Refl(Fun("act", (Var("x", "X"), Var("m", "M"))))
    try:
        check(bad, MONOID_ACTION)
    except ValueError:
        return
    raise AssertionError("accepted act(X, M) against rank act:(M,X)->X")


def test_equality_across_sorts_rejected():
    bad = P.Assume(Eq(Var("m", "M"), Var("x", "X")))
    try:
        check(bad, MONOID_ACTION)
    except ValueError:
        return
    raise AssertionError("accepted an equality between an M and an X")


def test_unknown_symbol_rejected():
    bad = P.Refl(Fun("bogus", ()))
    try:
        check(bad, MONOID_ACTION)
    except ValueError:
        return
    raise AssertionError("accepted an undeclared function symbol")


def test_wrong_arity_rejected():
    bad = P.Refl(Fun("act", (Var("m", "M"),)))  # act needs 2 args
    try:
        check(bad, MONOID_ACTION)
    except ValueError:
        return
    raise AssertionError("accepted act/1 against rank act:(M,X)->X")


# --- forward proofs: well-sorted and sound in the model -------------------


def m_terms():
    return st.recursive(
        st.one_of(st.sampled_from(M_VARS), st.just(E)),
        lambda kids: st.builds(mul, kids, kids),
        max_leaves=4,
    )


def x_terms():
    return st.recursive(
        st.sampled_from(X_VARS),
        lambda kids: st.builds(act, m_terms(), kids),
        max_leaves=4,
    )


@st.composite
def action_proofs(draw):
    facts: list[tuple] = []

    def add(pf) -> None:
        try:
            seq = check(pf, MONOID_ACTION)
        except (TypeError, ValueError):
            return
        facts.append((pf, seq))

    for ax in MONOID_ACTION.axioms:
        add(P.Axiom(ax))
    add(P.Refl(draw(m_terms())))
    add(P.Refl(draw(x_terms())))

    def pick():
        return draw(st.sampled_from(facts))[0]

    for _ in range(draw(st.integers(2, 8))):
        rule = draw(st.sampled_from(["sym", "trans", "cong*", "congact", "instM", "instX"]))
        if rule == "sym":
            add(P.Sym(pick()))
        elif rule == "trans":
            add(P.Trans(pick(), pick()))
        elif rule == "cong*":
            add(P.Cong("*", (pick(), pick())))
        elif rule == "congact":
            add(P.Cong("act", (pick(), pick())))
        elif rule == "instM":
            add(P.Inst(pick(), draw(st.sampled_from(M_VARS)).name, draw(m_terms())))
        elif rule == "instX":
            add(P.Inst(pick(), draw(st.sampled_from(X_VARS)).name, draw(x_terms())))

    return draw(st.sampled_from([pf for pf, _ in facts]))


@given(action_proofs())
@settings(deadline=None, max_examples=300)
def test_proofs_stay_well_sorted(pf):
    seq = check(pf, MONOID_ACTION)
    sort_check_formula(seq.concl, ACTION_SIG)  # must not raise
    for h in seq.hyps:
        sort_check_formula(h, ACTION_SIG)


@given(action_proofs(), st.data())
@settings(deadline=None, max_examples=300)
def test_proofs_sound_in_sorted_model(pf, data):
    seq = check(pf, MONOID_ACTION)
    assume(not seq.hyps)
    env = env_for(seq.concl, ACT_MODEL, data)
    assert interp_formula(seq.concl, ACT_MODEL, env), f"UNSOUND: {seq!r} at {env}"
