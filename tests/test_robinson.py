"""Robinson's (S, ·) arithmetic experiment (Julia Robinson 1949).

Addition is first-order definable from multiplication and successor. Here we:
  1. verify the bridge `S(a·c)·S(b·c) = S((c·c)·S(a·b))` is exactly the graph of
     addition in the standard model -- addition recovered from `·` and `S`, no `+`;
  2. check the `(1, S, ·)` Peano axioms are true in N (their intended positive
     integers); and
  3. have the trusted `check()` re-derive a Robinson-axiom instance, so the
     eliminated-addition theory really runs through the proof checker; and
  4. prove the bridge itself IN PEANO -- Robinson's definition of addition is
     correct as a theorem, not as a table of checked cases -- and with it two of
     her three §2 axioms. The third, A5', is refuted instead: it needs the
     positivity that PEANO does not have.
"""

from __future__ import annotations

import pytest
from semantics import Model, evaluate

import cold_start.proof as P
from cold_start.checker import check
from cold_start.peano import PEANO
from cold_start.presburger import S, add, numeral
from cold_start.proofs import robinson_add_proof
from cold_start.robinson import (
    ADD_ONE,
    ADD_SUCC,
    MUL_SUCC,
    ONE,
    ROBINSON_AXIOMS,
    ROBINSON_PEANO,
    bridge,
)
from cold_start.robinson_proofs import (
    BRIDGE_CONVERSE_POS,
    BRIDGE_RESIDUAL,
    BRIDGE_SUM,
    bridge_converse_positive,
    bridge_residual,
    bridge_theorem,
    robinson_add_one,
    robinson_mul_succ,
)
from cold_start.syntax import Var

# The standard model N over (0, S, ·). Addition is NOT supplied -- the whole point
# is that the bridge recovers it from multiplication and successor alone.
N = Model("N", interp={"0": lambda: 0, "S": lambda x: x + 1, "*": lambda a, b: a * b})

# The same model with `+` interpreted as well, for the PEANO-side statements at
# the bottom: those are stated in PEANO's signature, where addition is primitive
# again and the bridge is a theorem ABOUT it rather than a stand-in FOR it.
N_PLUS = Model("N+", interp={**N.interp, "+": lambda a, b: a + b})


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


# ---------------------------------------------------------------------------
# The bridge as a PEANO theorem
# ---------------------------------------------------------------------------
# Everything above checks Robinson's definition against the standard model, one
# tuple of numerals at a time. Below it is PROVED: `check(_, PEANO)` re-derives
# the bridge at `c := a + b` for FREE a and b -- every pair of naturals at once,
# and no model in sight.


def test_the_bridge_at_c_is_a_plus_b_is_a_peano_theorem():
    # Robinson's definition of addition, correct as a theorem. Both sides
    # multiply out to `ab(a+b)^2 + (a+b)^2 + 1`; the tactics normalise them to
    # one canonical polynomial, and the checker re-derives the join.
    seq = check(bridge_theorem(), PEANO)
    assert seq.concl == BRIDGE_SUM
    assert seq.concl == bridge(Var("a"), Var("b"), add(Var("a"), Var("b")))
    assert seq.hyps == frozenset()


def test_the_bridge_hypothesis_reduces_to_its_cancellation_equation():
    seq = check(bridge_residual(), PEANO)

    assert seq.concl == BRIDGE_RESIDUAL
    assert seq.hyps == frozenset()


def test_the_positive_bridge_converse_is_a_peano_theorem():
    seq = check(bridge_converse_positive(), PEANO)

    assert seq.concl == BRIDGE_CONVERSE_POS
    assert seq.hyps == frozenset()


def test_the_bridge_theorem_covers_the_zeros_robinson_excluded():
    # The instance a sceptic reaches for: a = b = 0, which Robinson's positive
    # domain does not contain at all. The theorem has free variables, so it
    # already covers this -- here it is, spelled out in the model.
    assert evaluate(BRIDGE_SUM, N_PLUS, {"a": 0, "b": 0})
    assert evaluate(BRIDGE_SUM, N_PLUS, {"a": 4, "b": 0})


@pytest.mark.parametrize(
    "name,axiom,build",
    [("A4'", ADD_ONE, robinson_add_one), ("A7'", MUL_SUCC, robinson_mul_succ)],
)
def test_a_robinson_axiom_is_a_peano_theorem(name, axiom, build):
    # Interpretation soundness, mechanised: two of Robinson's §2 axioms come out
    # as PEANO theorems ON THE NOSE -- the derived sequent is the very formula
    # `cold_start.robinson` declares as an axiom, with no hypotheses.
    seq = check(build(), PEANO)
    assert seq.concl == axiom
    assert seq.hyps == frozenset()


def test_a5_is_false_in_the_standard_model_of_peano():
    """Why the third §2 axiom has no proof beside the other two. A5' says
    `bridge(a,b,c) -> bridge(a, S b, S c)`, and the bridge pins `a + b = c` down
    only where `c` can be cancelled. At c = 0 it cannot: the hypothesis holds
    vacuously and the conclusion is false. N is a model of PEANO, so by
    soundness A5' has no PEANO proof at all -- it wants Robinson's positive
    integers, and that is exactly the work her domain restriction does."""
    assert evaluate(bridge(numeral(1), numeral(1), numeral(0)), N, {})  # hypothesis
    assert not evaluate(bridge(numeral(1), numeral(2), numeral(1)), N, {})  # conclusion
    assert not evaluate(ADD_SUCC, N, {"a": 1, "b": 1, "c": 0})  # so A5' itself fails


@pytest.mark.parametrize("c", [1, 2, 3, 4])
@pytest.mark.parametrize("b", [1, 2, 3, 4])
@pytest.mark.parametrize("a", [1, 2, 3, 4])
def test_a5_survives_everywhere_positive(a, b, c):
    # And only the zero breaks it: over Robinson's own domain A5' is fine, which
    # is what makes the failure above a statement about positivity rather than
    # about the bridge.
    assert evaluate(ADD_SUCC, N, {"a": a, "b": b, "c": c})
