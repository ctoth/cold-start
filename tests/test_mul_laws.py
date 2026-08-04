"""The multiplication ladder in PEANO, built by the untrusted tactics.

Every lemma here is *stated* in `cold_start.proofs` and searched for by the
rewriting engine; `check(_, PEANO)` is what decides whether the resulting term
is a proof. So each test is the same two assertions -- the checker re-derived
exactly the sequent we asked for, and it needed no hypotheses to do it.

The laws climb: the one-sided recursion laws first, then commutativity from
them, then distributivity, then associativity. Each rung is a rewrite rule for
the next, which is why the ladder has to be climbed in order.
"""

from __future__ import annotations

import pytest
from semantics import Model, evaluate

from cold_start.checker import check
from cold_start.peano import PEANO
from cold_start.proofs import (
    ADD_LEFT_COMM,
    DISTRIB_LEFT,
    DISTRIB_RIGHT,
    MUL_ASSOC,
    MUL_COMM,
    MUL_LEFT_COMM,
    MUL_SUCC_LEFT,
    MUL_ZERO_LEFT,
    add_left_comm,
    distrib_left,
    distrib_right,
    mul_assoc,
    mul_comm,
    mul_left_comm,
    mul_succ_left,
    mul_zero_left,
)

# PEANO's standard model, used only to double-check that the STATEMENTS say what
# their names claim. The proofs are checked by `check`; this is a guard against
# proving the wrong theorem correctly.
N = Model(
    "N",
    interp={
        "0": lambda: 0,
        "S": lambda x: x + 1,
        "+": lambda a, b: a + b,
        "*": lambda a, b: a * b,
    },
)

LADDER = [
    ("add-left-comm", ADD_LEFT_COMM, add_left_comm),
    ("mul-zero-left", MUL_ZERO_LEFT, mul_zero_left),
    ("mul-succ-left", MUL_SUCC_LEFT, mul_succ_left),
    ("mul-comm", MUL_COMM, mul_comm),
    ("distrib-left", DISTRIB_LEFT, distrib_left),
    ("distrib-right", DISTRIB_RIGHT, distrib_right),
    ("mul-assoc", MUL_ASSOC, mul_assoc),
    ("mul-left-comm", MUL_LEFT_COMM, mul_left_comm),
]


@pytest.mark.parametrize("name,claim,build", LADDER, ids=[r[0] for r in LADDER])
def test_the_law_is_a_peano_theorem(name, claim, build):
    seq = check(build(), PEANO)
    assert seq.concl == claim
    assert seq.hyps == frozenset()


@pytest.mark.parametrize("name,claim,build", LADDER, ids=[r[0] for r in LADDER])
@pytest.mark.parametrize(
    "env", [{"x": 0, "y": 0, "z": 0, "n": 0}, {"x": 3, "y": 5, "z": 2, "n": 7}]
)
def test_the_law_says_what_its_name_says(name, claim, build, env):
    assert evaluate(claim, N, env)
