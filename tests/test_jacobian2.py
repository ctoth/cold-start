"""The char-2 Jacobian payload: the jc counterexample map certified here.

Two independent guards, in the repo's honesty tradition:

- `check()` is the only authority that the collision *proofs* are proofs
  (empty hypotheses, exactly the stated conclusions, in DIFF_RING_2).
- An exact F_2[x,y,z] model (polynomials as frozensets of exponent triples,
  addition = symmetric difference — the same representation the jc finder
  uses) guards the *statements*: a transcription slip in the map builders
  would prove true theorems about the wrong map, which no checker catches.
"""

from __future__ import annotations

from cold_start.checker import check
from cold_start.diffring2 import (
    CHAR2,
    DIFF_RING_2,
    GEN_X,
    GEN_Y,
    GEN_Z,
    NONTRIVIAL,
    dx,
)
from cold_start.jacobian2_proofs import (
    COLLISION_POINTS,
    COLLISION_VALUE,
    collision_proofs,
    collision_statements,
    f1,
    f2,
    f3,
    mul_zero_rule,
    zero_add_rule,
    zero_mul_rule,
)
from cold_start.sequent import Sequent
from cold_start.syntax import Eq, Fun, Term, Var
from cold_start.vocabulary import ONE, ZERO, add, mul

# --- the exact F_2[x,y,z] model -------------------------------------------
# Terms evaluate to frozensets of exponent triples; + is symmetric
# difference, * is convolution. Same data the jc finder computes with.

X = frozenset({(1, 0, 0)})
Y = frozenset({(0, 1, 0)})
Z = frozenset({(0, 0, 1)})
P_ONE = frozenset({(0, 0, 0)})
P_ZERO: frozenset = frozenset()


def _pmul(a: frozenset, b: frozenset) -> frozenset:
    acc: set = set()
    for e1 in a:
        for e2 in b:
            m = (e1[0] + e2[0], e1[1] + e2[1], e1[2] + e2[2])
            acc.symmetric_difference_update({m})
    return frozenset(acc)


def evaluate(term: Term) -> frozenset:
    if type(term) is Fun:
        args = [evaluate(a) for a in term.args]
        match term.name:
            case "0":
                return P_ZERO
            case "1":
                return P_ONE
            case "X":
                return X
            case "Y":
                return Y
            case "Z":
                return Z
            case "+":
                return args[0] ^ args[1]
            case "*":
                return _pmul(args[0], args[1])
    raise AssertionError(f"model cannot evaluate {term!r}")


# The map, straight from jc's README (and its lean_export/JcChar2.lean):
#   F1 = z + xy + xy^2 + x^2y^2 + x^2yz + x^2y^2z + x^3y^2z
#   F2 = y + xy^2
#   F3 = x + y + xy^2 + x^2z
F1_MONOMIALS = frozenset(
    {(0, 0, 1), (1, 1, 0), (1, 2, 0), (2, 2, 0), (2, 1, 1), (2, 2, 1), (3, 2, 1)}
)
F2_MONOMIALS = frozenset({(0, 1, 0), (1, 2, 0)})
F3_MONOMIALS = frozenset({(1, 0, 0), (0, 1, 0), (1, 2, 0), (2, 0, 1)})


def test_builders_encode_the_jc_map() -> None:
    assert evaluate(f1(GEN_X, GEN_Y, GEN_Z)) == F1_MONOMIALS
    assert evaluate(f2(GEN_X, GEN_Y, GEN_Z)) == F2_MONOMIALS
    assert evaluate(f3(GEN_X, GEN_Y, GEN_Z)) == F3_MONOMIALS


# --- the theory -----------------------------------------------------------


def test_theory_validates_and_carries_the_axioms() -> None:
    assert CHAR2 in DIFF_RING_2.axioms
    assert NONTRIVIAL in DIFF_RING_2.axioms
    assert dx(GEN_X) == Fun("DX", (GEN_X,))
    DIFF_RING_2.validate()


# --- the ring lemmas the evaluation rule set is built from ----------------


def test_char2_ring_lemmas_check() -> None:
    a = Var("a")
    expected = {
        zero_mul_rule(): Eq(mul(ZERO, a), ZERO),
        mul_zero_rule(): Eq(mul(a, ZERO), ZERO),
        zero_add_rule(): Eq(add(ZERO, a), a),
    }
    for rule, concl in expected.items():
        assert check(rule.proof, DIFF_RING_2) == Sequent(frozenset(), concl)


# --- the collisions -------------------------------------------------------


def test_three_points_collide_at_one_zero_zero() -> None:
    assert COLLISION_POINTS == ((0, 0, 1), (1, 0, 1), (1, 1, 1))
    assert COLLISION_VALUE == (1, 0, 0)
    statements = collision_statements()
    proofs = collision_proofs()
    assert len(statements) == 9  # three components at three points
    for stmt, pf in zip(statements, proofs, strict=True):
        assert check(pf, DIFF_RING_2) == Sequent(frozenset(), stmt)


def test_collision_statements_say_what_the_readme_says() -> None:
    bit = {0: ZERO, 1: ONE}
    statements = collision_statements()
    i = 0
    for point in COLLISION_POINTS:
        args = tuple(bit[b] for b in point)
        for component, value in zip((f1, f2, f3), COLLISION_VALUE, strict=True):
            assert statements[i] == Eq(component(*args), bit[value])
            i += 1
