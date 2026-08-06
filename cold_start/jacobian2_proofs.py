"""The jc characteristic-2 Jacobian counterexample, entering the ledger.

The map (found by SAT search over monomial supports in the jc repository):

    F1 = Z + XY + XY^2 + X^2Y^2 + X^2YZ + X^2Y^2Z + X^3Y^2Z
    F2 = Y + XY^2
    F3 = X + Y + XY^2 + X^2Z

This module is the first, smallest slice of its certificate: the three
rational points (0,0,1), (1,0,1), (1,1,1) all evaluate to (1,0,0) — nine
closed equations in DIFF_RING_2, proved by `prove_eq` over a terminating
evaluation rule set. The components are *builders* (functions of three
terms), so the same definitions state evaluation theorems at constants and,
later, derivative and determinant theorems at the generators.

The rule set's non-axiom rules are proved here from the char-2 ring axioms:
`0*a = 0` needs no negation — expand 0 into 1+1 and let CHAR2 cancel, the
subtraction-free spelling of the classic argument.
"""

from __future__ import annotations

from functools import reduce

from .algebra import (
    ADD_COMM,
    ADD_ZERO,
    COMM,
    DIST_RIGHT,
    MUL_LEFT_ID,
    MUL_RIGHT_ID,
)
from .diffring2 import CHAR2
from .proof import Cong, Pf, Refl, Sym, Trans
from .syntax import Eq, Formula, Term, Var
from .tactics import Rule, axiom_rule, lemma_rule, prove_eq
from .vocabulary import ONE, ZERO, add, mul

# --- the map, as term builders --------------------------------------------


def _m(*factors: Term) -> Term:
    """A monomial: the product of `factors`, right-nested."""
    return reduce(lambda acc, f: mul(f, acc), reversed(factors[:-1]), factors[-1])


def _s(*terms: Term) -> Term:
    """A polynomial: the sum of `terms`, right-nested."""
    return reduce(lambda acc, t: add(t, acc), reversed(terms[:-1]), terms[-1])


def f1(x: Term, y: Term, z: Term) -> Term:
    return _s(
        z,
        _m(x, y),
        _m(x, y, y),
        _m(x, x, y, y),
        _m(x, x, y, z),
        _m(x, x, y, y, z),
        _m(x, x, x, y, y, z),
    )


def f2(x: Term, y: Term, z: Term) -> Term:
    return _s(y, _m(x, y, y))


def f3(x: Term, y: Term, z: Term) -> Term:
    return _s(x, y, _m(x, y, y), _m(x, x, z))


COMPONENTS = (f1, f2, f3)

# --- the ring lemmas behind the evaluation rules --------------------------

_a = Var("a")


def zero_mul_rule() -> Rule:
    """0*a = 0, subtraction-free:  0*a = (1+1)*a = 1*a + 1*a = a + a = 0."""
    char2_at_one = axiom_rule(CHAR2).instance({"x": ONE})
    mul_id_at_a = axiom_rule(MUL_LEFT_ID).instance({"x": _a})
    pf = Trans(
        Trans(
            Trans(
                Cong("*", (Sym(char2_at_one), Refl(_a))),
                axiom_rule(DIST_RIGHT).instance({"x": ONE, "y": ONE, "z": _a}),
            ),
            Cong("+", (mul_id_at_a, mul_id_at_a)),
        ),
        axiom_rule(CHAR2).instance({"x": _a}),
    )
    return lemma_rule(Eq(mul(ZERO, _a), ZERO), pf)


def mul_zero_rule() -> Rule:
    """a*0 = 0, by commutativity through `zero_mul_rule`."""
    pf = Trans(
        axiom_rule(COMM).instance({"x": _a, "y": ZERO}),
        zero_mul_rule().proof,
    )
    return lemma_rule(Eq(mul(_a, ZERO), ZERO), pf)


def zero_add_rule() -> Rule:
    """0 + a = a, by commutativity through the ADD_ZERO axiom."""
    pf = Trans(
        axiom_rule(ADD_COMM).instance({"x": ZERO, "y": _a}),
        axiom_rule(ADD_ZERO).instance({"x": _a}),
    )
    return lemma_rule(Eq(add(ZERO, _a), _a), pf)


def evaluation_rules() -> tuple[Rule, ...]:
    """A terminating rule set that decides closed 0/1 terms: every rule
    strictly shrinks its redex, and together they compute in F_2."""
    return (
        zero_mul_rule(),
        mul_zero_rule(),
        axiom_rule(MUL_LEFT_ID),
        axiom_rule(MUL_RIGHT_ID),
        zero_add_rule(),
        axiom_rule(ADD_ZERO),
        axiom_rule(CHAR2),
    )


# --- the collisions -------------------------------------------------------

COLLISION_POINTS = ((0, 0, 1), (1, 0, 1), (1, 1, 1))
COLLISION_VALUE = (1, 0, 0)

_BIT = {0: ZERO, 1: ONE}


def collision_statements() -> tuple[Formula, ...]:
    """Nine closed equations: each component of F at each collision point
    equals the corresponding coordinate of (1, 0, 0)."""
    return tuple(
        Eq(component(*(_BIT[b] for b in point)), _BIT[value])
        for point in COLLISION_POINTS
        for component, value in zip(COMPONENTS, COLLISION_VALUE, strict=True)
    )


def collision_proofs(budget: int = 500) -> tuple[Pf, ...]:
    rules = evaluation_rules()
    return tuple(prove_eq(stmt, rules, budget) for stmt in collision_statements())


__all__ = [
    "COLLISION_POINTS",
    "COLLISION_VALUE",
    "COMPONENTS",
    "collision_proofs",
    "collision_statements",
    "evaluation_rules",
    "f1",
    "f2",
    "f3",
    "mul_zero_rule",
    "zero_add_rule",
    "zero_mul_rule",
]
