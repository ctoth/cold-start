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

from collections.abc import Callable
from functools import reduce

from .algebra import (
    ADD_ASSOC,
    ADD_COMM,
    ADD_ZERO,
    COMM,
    DIST_LEFT,
    DIST_RIGHT,
    MUL_ASSOC,
    MUL_LEFT_ID,
    MUL_RIGHT_ID,
)
from .diffring2 import CHAR2, D_AXIOMS, GEN_X, GEN_Y, GEN_Z, dx, dy, dz
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


# --- AC normalization and char-2 cancellation -----------------------------
# Sums and products are canonicalized by ordered permutative rules (comm and
# a rotation through right-nesting), so equal monomials become syntactically
# identical and adjacent -- where CHAR2 and the pair-cancellation lemma
# annihilate them. This is exactly ANF normalization, spelled as rewriting.

_x, _y = Var("x"), Var("y")
_z = Var("z")


def _rotate_rule(
    assoc: Formula, comm: Formula, name: str, op: Callable[[Term, Term], Term]
) -> Rule:
    """x . (y . z) = y . (x . z), the ordered rotation completing AC.

    Proved by reassociating left, commuting the front pair, reassociating
    right; `ordered=True` fires it only downhill, which sorts arguments."""
    assoc_rule = axiom_rule(assoc)
    pf = Trans(
        Trans(
            Sym(assoc_rule.instance({"x": _x, "y": _y, "z": _z})),
            Cong(name, (axiom_rule(comm).instance({"x": _x, "y": _y}), Refl(_z))),
        ),
        assoc_rule.instance({"x": _y, "y": _x, "z": _z}),
    )
    eq = Eq(op(_x, op(_y, _z)), op(_y, op(_x, _z)))
    return Rule(eq, pf, frozenset({"x", "y", "z"}), ordered=True)


def add_rotate_rule() -> Rule:
    return _rotate_rule(ADD_ASSOC, ADD_COMM, "+", add)


def mul_rotate_rule() -> Rule:
    return _rotate_rule(MUL_ASSOC, COMM, "*", mul)


def cancel_pair_rule() -> Rule:
    """x + (x + y) = y: reassociate, collapse the pair by CHAR2, drop the 0."""
    pf = Trans(
        Trans(
            Sym(axiom_rule(ADD_ASSOC).instance({"x": _x, "y": _x, "z": _y})),
            Cong("+", (axiom_rule(CHAR2).instance({"x": _x}), Refl(_y))),
        ),
        Trans(
            axiom_rule(ADD_COMM).instance({"x": ZERO, "y": _y}),
            axiom_rule(ADD_ZERO).instance({"x": _y}),
        ),
    )
    return lemma_rule(Eq(add(_x, add(_x, _y)), _y), pf)


def normal_form_rules() -> tuple[Rule, ...]:
    """Ring normalization for char 2: expand products over sums, associate
    right, sort by the ordered rules, cancel duplicate summands."""
    return (
        axiom_rule(DIST_LEFT),
        axiom_rule(DIST_RIGHT),
        axiom_rule(ADD_ASSOC),
        axiom_rule(MUL_ASSOC),
        axiom_rule(ADD_COMM, ordered=True),
        axiom_rule(COMM, ordered=True),
        add_rotate_rule(),
        mul_rotate_rule(),
        axiom_rule(CHAR2),
        cancel_pair_rule(),
    )


# --- the derivative lemmas ------------------------------------------------


def derivative_rules() -> tuple[Rule, ...]:
    """Push D symbols to the generators, substitute their values, evaluate."""
    return (
        *(axiom_rule(ax) for ax in D_AXIOMS),
        *evaluation_rules(),
        *normal_form_rules(),
    )


def derivative_statements() -> tuple[Formula, ...]:
    """The Jacobian matrix, row by row: D(component) = explicit polynomial,
    the data the jc finder computes with `pderiv` (char-2: even powers die)."""
    x, y, z = GEN_X, GEN_Y, GEN_Z
    rows = (
        (
            _s(y, _m(y, y), _m(x, x, y, y, z)),  # dF1/dx
            _s(x, _m(x, x, z)),  # dF1/dy
            _s(ONE, _m(x, x, y), _m(x, x, y, y), _m(x, x, x, y, y)),  # dF1/dz
        ),
        (_m(y, y), ONE, ZERO),  # dF2/dx, dF2/dy, dF2/dz
        (_s(ONE, _m(y, y)), ONE, _m(x, x)),  # dF3/dx, dF3/dy, dF3/dz
    )
    return tuple(
        Eq(d(component(x, y, z)), rhs)
        for component, row in zip(COMPONENTS, rows, strict=True)
        for d, rhs in zip((dx, dy, dz), row, strict=True)
    )


def derivative_proofs(budget: int = 20_000) -> tuple[Pf, ...]:
    rules = derivative_rules()
    return tuple(prove_eq(stmt, rules, budget) for stmt in derivative_statements())


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
    "add_rotate_rule",
    "cancel_pair_rule",
    "collision_proofs",
    "collision_statements",
    "derivative_proofs",
    "derivative_rules",
    "derivative_statements",
    "evaluation_rules",
    "f1",
    "f2",
    "f3",
    "mul_rotate_rule",
    "mul_zero_rule",
    "normal_form_rules",
    "zero_add_rule",
    "zero_mul_rule",
]
