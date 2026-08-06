"""Quantifier honesty net: evaluate ∀/∃ over a finite model and assert that
every sequent the checker accepts is valid there. Hand-picked tests cannot
catch an unsound capture or eigenvariable rule; a generator can.

Model: Z/3 as a commutative ring (carrier {0,1,2}). Finite, so ∀/∃ are decided
by enumeration.
"""

from __future__ import annotations

from dataclasses import dataclass

from hypothesis import given, settings
from hypothesis import strategies as st
from semantics import evaluate

import cold_start.proof as P
from cold_start.algebra import COMM_RING
from cold_start.checker import check
from cold_start.sequent import Sequent
from cold_start.syntax import (
    Eq,
    Var,
    exists,
    forall,
)
from cold_start.vocabulary import ONE as R1
from cold_start.vocabulary import ZERO as R0
from cold_start.vocabulary import add, mul, neg


@dataclass
class FiniteModel:
    name: str
    carrier: tuple  # explicit elements, so ∀/∃ can enumerate
    interp: dict


Z3 = FiniteModel(
    "Z/3",
    (0, 1, 2),
    {
        "+": lambda a, b: (a + b) % 3,
        "*": lambda a, b: (a * b) % 3,
        "neg": lambda a: (-a) % 3,
        "0": lambda: 0,
        "1": lambda: 1,
    },
)


def test_eval_quantifiers():
    # ∀x. x = x is true; ∀x. x = 0 is false in Z/3; ∃x. x = 1+1 is true.
    assert evaluate(forall("x", "", Eq(Var("x"), Var("x"))), Z3, {})
    assert not evaluate(forall("x", "", Eq(Var("x"), R0)), Z3, {})
    assert evaluate(exists("x", "", Eq(Var("x"), add(R1, R1))), Z3, {})


# --- the honesty net ------------------------------------------------------

VAR_POOL = ["x", "y", "z"]
ENV3 = st.fixed_dictionaries({n: st.sampled_from((0, 1, 2)) for n in VAR_POOL})


def ring_terms():
    return st.recursive(
        st.one_of(st.builds(Var, st.sampled_from(VAR_POOL)), st.just(R0), st.just(R1)),
        lambda kids: st.one_of(
            st.builds(add, kids, kids), st.builds(mul, kids, kids), st.builds(neg, kids)
        ),
        max_leaves=4,
    )


@st.composite
def ring_proofs(draw):
    """Forward proofs under COMM_RING, including ForallIntro/ForallElim and an
    Assume (so the eigenvariable condition is genuinely exercised: generalizing
    over a hypothesis-constrained variable must be refused, not produced)."""
    facts: list[tuple] = []

    def addf(pf) -> None:
        try:
            seq = check(pf, COMM_RING)
        except (TypeError, ValueError):
            return
        facts.append((pf, seq))

    for ax in COMM_RING.axioms:
        addf(P.Axiom(ax))
    addf(P.Refl(draw(ring_terms())))
    addf(P.Assume(Eq(draw(ring_terms()), draw(ring_terms()))))

    def pick():
        return draw(st.sampled_from(facts))[0]

    for _ in range(draw(st.integers(2, 9))):
        rule = draw(
            st.sampled_from(
                [
                    "sym", "trans", "cong+", "cong*", "congneg", "inst",
                    "fa_intro", "fa_elim", "ex_intro",
                ]
            )
        )
        if rule == "sym":
            addf(P.Sym(pick()))
        elif rule == "trans":
            addf(P.Trans(pick(), pick()))
        elif rule == "cong+":
            addf(P.Cong("+", (pick(), pick())))
        elif rule == "cong*":
            addf(P.Cong("*", (pick(), pick())))
        elif rule == "congneg":
            addf(P.Cong("neg", (pick(),)))
        elif rule == "inst":
            addf(P.Inst(pick(), draw(st.sampled_from(VAR_POOL)), draw(ring_terms())))
        elif rule == "fa_intro":
            addf(P.ForallIntro(draw(st.sampled_from(VAR_POOL)), "", pick()))
        elif rule == "fa_elim":
            addf(P.ForallElim(pick(), draw(ring_terms())))
        elif rule == "ex_intro":
            # vacuous existential over an unused name `q`: from `concl` introduce
            # `exists q. concl` (q does not occur in concl, so any witness works).
            f_pf, f_seq = draw(st.sampled_from(facts))
            addf(P.ExistsIntro(exists("q", "", f_seq.concl), R0, f_pf))

    return draw(st.sampled_from([pf for pf, _ in facts]))


@given(ring_proofs(), ENV3)
@settings(deadline=None, max_examples=400)
def test_quantifier_proofs_sound_in_Z3(pf, env):
    seq = check(pf, COMM_RING)
    # conditional validity: where every hypothesis holds, the conclusion must.
    if all(evaluate(h, Z3, env) for h in seq.hyps):
        assert evaluate(seq.concl, Z3, env), f"UNSOUND: {seq!r} at {env}"


def test_net_catches_a_false_universal():
    # The eigenvariable bug would yield {x=0} |- ∀x. x=0. Show the net's validity
    # check fires on it: at x=0 the hypothesis holds but ∀x.x=0 is false in Z/3.
    hyp = Eq(Var("x"), R0)
    bogus = Sequent(frozenset({hyp}), forall("x", "", Eq(Var("x"), R0)))
    env = {"x": 0, "y": 0, "z": 0}
    assert evaluate(hyp, Z3, env)  # hypothesis holds
    assert not evaluate(bogus.concl, Z3, env)  # but the universal is false
