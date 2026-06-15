"""Abstract-algebra soundness via multiple models (Hypothesis).

The honesty principle, generalized from the N-evaluator: a theorem proved from a
theory's axioms must hold in *every* model of that theory. For monoids we
include NON-commutative models (string concatenation, transformations of a
2-element set), so a proof that wrongly derived `x*y = y*x` from the monoid
axioms alone would be caught -- the whole point of reaching toward Clifford.
"""

from __future__ import annotations

from dataclasses import dataclass

from hypothesis import assume, given, settings
from hypothesis import strategies as st
from semantics import evaluate

import cold_start.proof as P
from cold_start.algebra import (
    ASSOC,
    COMM,
    COMM_MONOID,
    LEFT_ID,
    MONOID,
    RIGHT_ID,
    E,
    mul,
)
from cold_start.checker import check
from cold_start.proof import Pf
from cold_start.syntax import Eq, Var

VAR_POOL = ["x", "y", "z", "u", "v"]


# --- models ---------------------------------------------------------------


@dataclass
class Model:
    name: str
    carrier: object  # a Hypothesis strategy sampling carrier elements
    interp: dict  # function symbol name -> python callable


def _compose(g, f):
    # transformations of {0,1} as tuples (h(0), h(1)); (g o f)(x) = g(f(x))
    return (g[f[0]], g[f[1]])


STRINGS = Model(
    "strings(++,'')",
    st.text(alphabet="ab", max_size=4),
    {"e": lambda: "", "*": lambda a, b: a + b},
)
NAT_PLUS = Model("(N,+,0)", st.integers(0, 12), {"e": lambda: 0, "*": lambda a, b: a + b})
NAT_TIMES = Model("(N,*,1)", st.integers(0, 12), {"e": lambda: 1, "*": lambda a, b: a * b})
TRANSF = Model(
    "T_2(compose,id)",
    st.sampled_from([(0, 0), (0, 1), (1, 0), (1, 1)]),
    {"e": lambda: (0, 1), "*": _compose},
)

MONOID_MODELS = [STRINGS, NAT_PLUS, NAT_TIMES, TRANSF]
COMM_MODELS = [NAT_PLUS, NAT_TIMES]
NONCOMMUTATIVE = [STRINGS, TRANSF]


def env_of(model: Model, data) -> dict:
    return {n: data.draw(model.carrier) for n in VAR_POOL}


# --- the models really are models -----------------------------------------


@given(st.data())
@settings(max_examples=300)
def test_models_satisfy_their_theories(data):
    for theory, models in ((MONOID, MONOID_MODELS), (COMM_MONOID, COMM_MODELS)):
        for model in models:
            env = env_of(model, data)
            for ax in theory.axioms:
                assert evaluate(ax, model, env), f"{model.name} fails {ax!r}"


# --- a worked abstract proof checks ---------------------------------------


def left_id_twice() -> Pf:
    """|- e*(e*x) = x, from the left-identity axiom alone (inst + inst + trans)."""
    x = Var("x")
    step1 = P.Inst(P.Axiom(LEFT_ID), "x", mul(E, x))  # e*(e*x) = e*x
    step2 = P.Axiom(LEFT_ID)  # e*x = x
    return P.Trans(step1, step2)


def test_left_id_twice_checks():
    seq = check(left_id_twice(), MONOID)
    x = Var("x")
    assert seq.concl == Eq(mul(E, mul(E, x)), x)
    assert seq.hyps == frozenset()


# --- the honesty net: monoid proofs are sound in ALL monoid models --------


def monoid_terms():
    return st.recursive(
        st.one_of(st.builds(Var, st.sampled_from(VAR_POOL)), st.just(E)),
        lambda kids: st.builds(mul, kids, kids),
        max_leaves=5,
    )


@st.composite
def monoid_proofs(draw):
    facts: list[tuple] = []

    def add(pf) -> None:
        try:
            seq = check(pf, MONOID)
        except (TypeError, ValueError):
            return
        facts.append((pf, seq))

    add(P.Axiom(ASSOC))
    add(P.Axiom(LEFT_ID))
    add(P.Axiom(RIGHT_ID))
    for _ in range(2):
        add(P.Refl(draw(monoid_terms())))

    for _ in range(draw(st.integers(2, 9))):
        rule = draw(st.sampled_from(["sym", "trans", "cong", "inst"]))
        if rule == "sym":
            add(P.Sym(draw(st.sampled_from(facts))[0]))
        elif rule == "trans":
            add(P.Trans(draw(st.sampled_from(facts))[0], draw(st.sampled_from(facts))[0]))
        elif rule == "cong":
            add(P.Cong("*", (draw(st.sampled_from(facts))[0], draw(st.sampled_from(facts))[0])))
        elif rule == "inst":
            target = draw(st.sampled_from(facts))[0]
            add(P.Inst(target, draw(st.sampled_from(VAR_POOL)), draw(monoid_terms())))

    return draw(st.sampled_from([pf for pf, _ in facts]))


@given(monoid_proofs(), st.data())
@settings(deadline=None, max_examples=400)
def test_monoid_proofs_sound_in_all_models(pf, data):
    seq = check(pf, MONOID)
    assume(not seq.hyps)
    for model in MONOID_MODELS:
        env = env_of(model, data)
        assert evaluate(seq.concl, model, env), f"UNSOUND in {model.name}: {seq!r}"


# --- commutativity is independent of the monoid axioms --------------------


@given(st.data())
def test_commutativity_is_not_a_monoid_theorem(data):
    """Each non-commutative model satisfies every monoid axiom, yet falsifies
    `x*y = y*x`. By soundness, commutativity therefore cannot be derived from
    the monoid axioms -- it is a genuine extra assumption (COMM_MONOID)."""
    comm = Eq(mul(Var("x"), Var("y")), mul(Var("y"), Var("x")))
    for model in NONCOMMUTATIVE:
        env = env_of(model, data)
        for ax in MONOID.axioms:
            assert evaluate(ax, model, env), f"{model.name} not a monoid"
    # explicit witness in strings: "a"++"b" != "b"++"a"
    assert not evaluate(comm, STRINGS, {"x": "a", "y": "b"})


def test_commutativity_requires_the_comm_axiom():
    """Commutativity is provable from COMM_MONOID (it's an axiom there) but the
    monoid theory does not even admit it as an axiom -- you cannot get it for
    free."""
    comm_proof = P.Axiom(COMM)
    seq = check(comm_proof, COMM_MONOID)
    assert seq.concl == Eq(mul(Var("x"), Var("y")), mul(Var("y"), Var("x")))
    try:
        check(comm_proof, MONOID)
    except ValueError:
        return
    raise AssertionError("MONOID accepted commutativity as an axiom")
