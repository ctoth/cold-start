"""Robinson's (S, ·) arithmetic experiment (Julia Robinson 1949).

Addition is first-order definable from multiplication and successor. Here we:
  1. verify the bridge `S(a·c)·S(b·c) = S((c·c)·S(a·b))` is exactly the graph of
     addition in the standard model -- addition recovered from `·` and `S`, no `+`;
  2. check the `(1, S, ·)` Peano axioms are true in N (their intended positive
     integers); and
  3. have the trusted `check()` re-derive a Robinson-axiom instance, so the
     eliminated-addition theory really runs through the proof checker.
"""

from __future__ import annotations

import pytest
from semantics import Model, evaluate

import cold_start.proof as P
from cold_start.checker import check
from cold_start.presburger import S, numeral
from cold_start.proofs import robinson_add_proof
from cold_start.robinson import (
    ADD_ONE,
    ONE,
    ROBINSON_AXIOMS,
    ROBINSON_PEANO,
    bridge,
)

# The standard model N over (0, S, ·). Addition is NOT supplied -- the whole point
# is that the bridge recovers it from multiplication and successor alone.
N = Model("N", interp={"0": lambda: 0, "S": lambda x: x + 1, "*": lambda a, b: a * b})


@pytest.mark.parametrize("c", [1, 2, 3, 4, 5, 6])
@pytest.mark.parametrize("b", [0, 1, 2, 3, 4])
@pytest.mark.parametrize("a", [0, 1, 2, 3, 4])
def test_bridge_is_the_graph_of_addition(a, b, c):
    # Robinson's theorem, verified in N: the bridge holds exactly when a + b = c
    # (for c > 0). Addition read off of multiplication and successor.
    holds = evaluate(bridge(numeral(a), numeral(b), numeral(c)), N, {})
    assert holds is (a + b == c)


def test_bridge_concrete_witnesses():
    # The poster cases: 2 + 3 = 5 satisfies the bridge; 2 + 3 = 4 does not.
    assert evaluate(bridge(numeral(2), numeral(3), numeral(5)), N, {})
    assert not evaluate(bridge(numeral(2), numeral(3), numeral(4)), N, {})


@pytest.mark.parametrize("a", [1, 2, 3])
@pytest.mark.parametrize("b", [1, 2, 3])
@pytest.mark.parametrize("c", [1, 2, 3])
def test_robinson_peano_axioms_true_in_N(a, b, c):
    # Every (1, S, ·) Peano axiom holds in N over the positive integers (Robinson's
    # domain). This validates the eliminated-addition axiomatization is sound.
    env = {"a": a, "b": b, "c": c}
    for axiom in ROBINSON_AXIOMS:
        assert evaluate(axiom, N, env), f"axiom false in N at {env}: {axiom!r}"


def test_checker_derives_a_robinson_axiom_instance():
    # The trusted checker runs the (1, S, ·) theory: instantiate A4' (a + 1 = S a)
    # at a := 2, deriving the bridge for 2 + 1 = 3 -- a closed theorem containing no
    # `+` symbol at all, only S and ·.
    seq = check(P.Inst(P.Axiom(ADD_ONE), "a", numeral(2)), ROBINSON_PEANO)
    assert seq.concl == bridge(numeral(2), ONE, S(numeral(2)))
    assert seq.concl == bridge(numeral(2), numeral(1), numeral(3))
    assert seq.hyps == frozenset()


def test_robinson_add_proof_derives_two_plus_three():
    # The payoff: 2 + 3 = 5 as a DERIVED theorem of the (1, S, ·) theory. The
    # sequent has no hypotheses and its conclusion contains no `+` symbol at
    # all -- addition is the bridge, chained out of A4' and A5' by modus ponens.
    seq = check(robinson_add_proof(2, 3), ROBINSON_PEANO)
    assert seq.hyps == frozenset()
    assert seq.concl == bridge(numeral(2), numeral(3), numeral(5))


@pytest.mark.parametrize("b", [1, 2, 3, 4, 5])
@pytest.mark.parametrize("a", [1, 2, 3, 4, 5])
def test_robinson_add_proof_computes(a, b):
    # Robinson's recursion laws compute addition for every positive a, b, and
    # the trusted checker re-derives each one.
    seq = check(robinson_add_proof(a, b), ROBINSON_PEANO)
    assert seq.hyps == frozenset()
    assert seq.concl == bridge(numeral(a), numeral(b), numeral(a + b))


@pytest.mark.parametrize("a,b", [(0, 1), (1, 0), (0, 0), (-1, 2)])
def test_robinson_add_proof_rejects_non_positive(a, b):
    # Robinson's §2 domain is the POSITIVE integers -- there is no 0, and the
    # bridge is only the graph of addition for c > 0.
    with pytest.raises(ValueError):
        robinson_add_proof(a, b)
