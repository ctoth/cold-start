"""Ring soundness across models, incl. a non-commutative one (Hypothesis).

A theorem proved from the ring axioms must hold in every ring -- and our models
include M_2(F_2), the 2x2 matrices over F_2, which is non-commutative. So any
accidental derivation of x*y = y*x from the ring axioms alone is caught, and we
confirm commutativity is a genuine extra assumption (COMM_RING).
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product

from hypothesis import assume, given, settings
from hypothesis import strategies as st
from semantics import evaluate

import cold_start.proof as P
from cold_start.algebra import (
    ADD_COMM,
    ADD_NEG,
    ADD_ZERO,
    COMM,
    COMM_RING,
    RING,
    RING_AXIOMS,
)
from cold_start.checker import check
from cold_start.syntax import Eq, Fun, Var
from cold_start.vocabulary import ZERO as R0
from cold_start.vocabulary import add, mul, neg

VAR_POOL = ["x", "y", "z", "u", "v"]


# --- models ---------------------------------------------------------------


@dataclass
class Model:
    name: str
    carrier: object  # Hypothesis strategy
    interp: dict


# Z and Z/6: commutative rings.
INTEGERS = Model(
    "Z",
    st.integers(-8, 8),
    {"+": lambda a, b: a + b, "*": lambda a, b: a * b,
     "0": lambda: 0, "1": lambda: 1, "neg": lambda a: -a},
)
Z6 = Model(
    "Z/6",
    st.integers(0, 5),
    {"+": lambda a, b: (a + b) % 6, "*": lambda a, b: (a * b) % 6,
     "0": lambda: 0, "1": lambda: 1, "neg": lambda a: (-a) % 6},
)


# M_2(F_2): a finite NON-commutative ring with unity. Matrices as (a,b,c,d).
def _madd(p, q):
    return tuple((i + j) % 2 for i, j in zip(p, q, strict=True))


def _mmul(p, q):
    a1, b1, c1, d1 = p
    a2, b2, c2, d2 = q
    return (
        (a1 * a2 + b1 * c2) % 2,
        (a1 * b2 + b1 * d2) % 2,
        (c1 * a2 + d1 * c2) % 2,
        (c1 * b2 + d1 * d2) % 2,
    )


MAT2 = Model(
    "M_2(F_2)",
    st.sampled_from([t for t in product((0, 1), repeat=4)]),
    {"+": _madd, "*": _mmul, "0": lambda: (0, 0, 0, 0), "1": lambda: (1, 0, 0, 1),
     "neg": lambda x: x},  # -e = e in characteristic 2
)

RING_MODELS = [INTEGERS, Z6, MAT2]
COMM_MODELS = [INTEGERS, Z6]


def env_of(model: Model, data) -> dict:
    return {n: data.draw(model.carrier) for n in VAR_POOL}


@given(st.data())
@settings(max_examples=300)
def test_models_satisfy_their_theories(data):
    for ax in RING_AXIOMS:
        for model in RING_MODELS:
            env = env_of(model, data)
            assert evaluate(ax, model, env), f"{model.name} fails {ax!r}"
    for model in COMM_MODELS:  # the commutative ones also satisfy COMM
        env = env_of(model, data)
        assert evaluate(COMM, model, env)


# --- worked ring theorems -------------------------------------------------


def _x():
    return Var("x")


def test_left_additive_inverse():
    # neg(x) + x = 0, from x + neg(x) = 0 and additive commutativity.
    comm = P.Inst(P.Axiom(ADD_COMM), "y", neg(_x()))  # x + neg(x) = neg(x) + x
    seq = check(P.Trans(P.Sym(comm), P.Axiom(ADD_NEG)), RING)
    assert seq.concl == Eq(add(neg(_x()), _x()), R0)
    assert seq.hyps == frozenset()


def test_left_additive_identity():
    # 0 + x = x, from x + 0 = x and additive commutativity.
    comm = P.Inst(P.Axiom(ADD_COMM), "y", R0)  # x + 0 = 0 + x
    seq = check(P.Trans(P.Sym(comm), P.Axiom(ADD_ZERO)), RING)
    assert seq.concl == Eq(add(R0, _x()), _x())
    assert seq.hyps == frozenset()


# --- the honesty net ------------------------------------------------------


def ring_terms():
    return st.recursive(
        st.one_of(
            st.builds(Var, st.sampled_from(VAR_POOL)),
            st.just(R0),
            st.just(Fun("1", ())),
        ),
        lambda kids: st.one_of(
            st.builds(add, kids, kids),
            st.builds(mul, kids, kids),
            st.builds(neg, kids),
        ),
        max_leaves=5,
    )


@st.composite
def ring_proofs(draw):
    facts: list[tuple] = []

    def add_fact(pf) -> None:
        try:
            seq = check(pf, RING)
        except (TypeError, ValueError):
            return
        facts.append((pf, seq))

    for ax in RING_AXIOMS:
        add_fact(P.Axiom(ax))
    add_fact(P.Refl(draw(ring_terms())))

    def pick():
        return draw(st.sampled_from(facts))[0]

    for _ in range(draw(st.integers(2, 9))):
        rule = draw(st.sampled_from(["sym", "trans", "cong+", "cong*", "congneg", "inst"]))
        if rule == "sym":
            add_fact(P.Sym(pick()))
        elif rule == "trans":
            add_fact(P.Trans(pick(), pick()))
        elif rule == "cong+":
            add_fact(P.Cong("+", (pick(), pick())))
        elif rule == "cong*":
            add_fact(P.Cong("*", (pick(), pick())))
        elif rule == "congneg":
            add_fact(P.Cong("neg", (pick(),)))
        elif rule == "inst":
            add_fact(P.Inst(pick(), draw(st.sampled_from(VAR_POOL)), draw(ring_terms())))

    return draw(st.sampled_from([pf for pf, _ in facts]))


@given(ring_proofs(), st.data())
@settings(deadline=None, max_examples=400)
def test_ring_proofs_sound_in_all_models(pf, data):
    seq = check(pf, RING)
    assume(not seq.hyps)
    for model in RING_MODELS:
        env = env_of(model, data)
        assert evaluate(seq.concl, model, env), f"UNSOUND in {model.name}: {seq!r}"


# --- multiplicative commutativity is independent of the ring axioms -------


@given(st.data())
def test_mul_commutativity_is_not_a_ring_theorem(data):
    """M_2(F_2) satisfies every ring axiom but falsifies x*y = y*x, so
    commutativity cannot be derived -- it is the extra axiom of COMM_RING."""
    comm = Eq(mul(Var("x"), Var("y")), mul(Var("y"), Var("x")))
    env = env_of(MAT2, data)
    for ax in RING_AXIOMS:
        assert evaluate(ax, MAT2, env), f"M_2(F_2) not a ring: {ax!r}"
    # explicit non-commuting witness: E12 * E21 != E21 * E12
    e12, e21 = (0, 1, 0, 0), (0, 0, 1, 0)
    assert not evaluate(comm, MAT2, {"x": e12, "y": e21})


def test_commutativity_requires_the_axiom():
    proof = P.Axiom(COMM)
    assert check(proof, COMM_RING).concl == Eq(mul(Var("x"), Var("y")), mul(Var("y"), Var("x")))
    try:
        check(proof, RING)
    except ValueError:
        return
    raise AssertionError("RING accepted commutativity as an axiom")
