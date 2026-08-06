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
from typing import cast

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
from .diffring2 import CHAR2, D_AXIOMS, GEN_X, GEN_Y, GEN_Z, NONTRIVIAL, dx, dy, dz
from .proof import Axiom, Cong, ExistsIntro, Pf, Refl, Sym, Trans
from .prop import And, and_intro
from .syntax import Eq, Formula, Not, Term, Var, exists
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


# --- the derivations kill both constants ----------------------------------


def derivation_zero_proofs() -> tuple[Pf, ...]:
    """D(0) = 0 for DX, DY, DZ:  D(0) = D(0+0) = D(0)+D(0) = 0 by CHAR2."""
    out: list[Pf] = []
    for i, d in enumerate((dx, dy, dz)):
        name = ("DX", "DY", "DZ")[i]
        additivity = D_AXIOMS[5 * i]
        out.append(
            Trans(
                Trans(
                    Cong(name, (Sym(axiom_rule(ADD_ZERO).instance({"x": ZERO})),)),
                    axiom_rule(additivity).instance({"x": ZERO, "y": ZERO}),
                ),
                axiom_rule(CHAR2).instance({"x": d(ZERO)}),
            )
        )
    return tuple(out)


def derivation_one_proofs() -> tuple[Pf, ...]:
    """D(1) = 0:  D(1) = D(1*1) = D(1)*1 + 1*D(1) = D(1)+D(1) = 0."""
    out: list[Pf] = []
    for i, d in enumerate((dx, dy, dz)):
        name = ("DX", "DY", "DZ")[i]
        leibniz = D_AXIOMS[5 * i + 1]
        d1 = d(ONE)
        out.append(
            Trans(
                Trans(
                    Trans(
                        Cong(name, (Sym(axiom_rule(MUL_LEFT_ID).instance({"x": ONE})),)),
                        axiom_rule(leibniz).instance({"x": ONE, "y": ONE}),
                    ),
                    Cong(
                        "+",
                        (
                            axiom_rule(MUL_RIGHT_ID).instance({"x": d1}),
                            axiom_rule(MUL_LEFT_ID).instance({"x": d1}),
                        ),
                    ),
                ),
                axiom_rule(CHAR2).instance({"x": d1}),
            )
        )
    return tuple(out)


# --- non-injectivity, as one closed sentence ------------------------------

_POINT_NAMES = ("x1", "y1", "z1", "x2", "y2", "z2")
_WITNESSES = (ZERO, ZERO, ONE, ONE, ZERO, ONE)  # (0,0,1) and (1,0,1)


def _noninjectivity_body(args: tuple[Term, ...]) -> Formula:
    p, q = args[:3], args[3:]
    return And(
        Eq(f1(*p), f1(*q)),
        Eq(f2(*p), f2(*q)),
        Eq(f3(*p), f3(*q)),
        Not(Eq(args[0], args[3])),
    )


def noninjectivity_statement() -> Formula:
    """There are two points, first coordinates distinct, with equal images
    under every component of F -- the Jacobian conjecture's conclusion,
    negated, with no free variables and no metatheory."""
    args: tuple[Term, ...] = tuple(Var(n) for n in _POINT_NAMES)
    stmt = _noninjectivity_body(args)
    for name in reversed(_POINT_NAMES):
        stmt = exists(name, "", stmt)
    return stmt


def noninjectivity_proof() -> Pf:
    """ExistsIntro six times over the witnesses; the ground body is the
    collision proofs Trans-joined pairwise, and NONTRIVIAL tells 0 from 1.

    Untrusted like every tactic, but self-diagnosing: the conjunction it
    builds must equal the statement's body at the witnesses, or we raise
    here instead of handing `check` a mystery."""
    proofs = collision_proofs()
    statements = collision_statements()
    # collision index: point * 3 + component; points 0 = (0,0,1), 1 = (1,0,1)
    eq_stmts: list[Formula] = []
    eq_pfs: list[Pf] = []
    for component in range(3):
        ls, rs = statements[component], statements[3 + component]
        if type(ls) is not Eq or type(rs) is not Eq:
            raise TypeError("collision statements must be equations")
        eq_stmts.append(Eq(ls.lhs, rs.lhs))
        eq_pfs.append(Trans(proofs[component], Sym(proofs[3 + component])))

    pf: Pf = Axiom(NONTRIVIAL)
    formula: Formula = NONTRIVIAL
    for stmt, eq_pf in zip(reversed(eq_stmts), reversed(eq_pfs), strict=True):
        pf = and_intro(stmt, formula, eq_pf, pf)
        formula = And(stmt, formula)
    if formula != _noninjectivity_body(_WITNESSES):
        raise AssertionError("conjunction shape drifted from the statement body")

    for j in reversed(range(6)):
        args = (*_WITNESSES[:j], *(Var(n) for n in _POINT_NAMES[j:]))
        opened = _noninjectivity_body(args)
        for name in reversed(_POINT_NAMES[j + 1 :]):
            opened = exists(name, "", opened)
        pf = ExistsIntro(exists(_POINT_NAMES[j], "", opened), _WITNESSES[j], pf)
    return pf


# --- the determinant ------------------------------------------------------


def det_term() -> Term:
    """det of the Jacobian matrix of F, with the derivatives in the term:
    the 3x3 cofactor expansion, all signs + because the characteristic is 2."""
    a, b, c, d, e, f, g, h, i = (
        derivation(component(GEN_X, GEN_Y, GEN_Z))
        for component in COMPONENTS
        for derivation in (dx, dy, dz)
    )
    return add(
        mul(a, add(mul(e, i), mul(f, h))),
        add(
            mul(b, add(mul(d, i), mul(f, g))),
            mul(c, add(mul(d, h), mul(e, g))),
        ),
    )


def det_proof(budget: int = 200_000) -> Pf:
    """det J(F) = 1: rewrite each matrix entry by its derivative lemma, then
    it is a polynomial identity the normal-form rules decide."""
    entry_rules = tuple(
        lemma_rule(stmt, pf)
        for stmt, pf in zip(derivative_statements(), derivative_proofs(), strict=True)
    )
    rules = (*entry_rules, *evaluation_rules(), *normal_form_rules())
    return prove_eq(Eq(det_term(), ONE), rules, budget)


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


# --- the answer surface ---------------------------------------------------


def _toll(pf: Pf) -> int:
    """Proof nodes in `pf` -- the certificate's cost, counted like the
    bridge ledger's toll column."""
    from dataclasses import fields as dc_fields
    from dataclasses import is_dataclass

    count = 0
    stack: list[object] = [pf]
    while stack:
        node = stack.pop()
        if isinstance(node, Pf) and is_dataclass(node):
            count += 1
            for f in dc_fields(node):
                value: object = getattr(node, f.name)
                if type(value) is tuple:
                    stack.extend(cast("tuple[object, ...]", value))
                else:
                    stack.append(value)
    return count


def main() -> None:
    """Re-check every theorem of the certificate and print its toll.
    Like the ledger: numbers re-derived by the trusted checker on every
    run, never quoted from documentation."""
    from .checker import check
    from .diffring2 import DIFF_RING_2

    groups: tuple[tuple[str, tuple[Pf, ...]], ...] = (
        ("collisions (9)", collision_proofs()),
        ("derivative lemmas (9)", derivative_proofs()),
        ("det J = 1", (det_proof(),)),
        ("D(0) = 0 (3)", derivation_zero_proofs()),
        ("D(1) = 0 (3)", derivation_one_proofs()),
        ("non-injectivity (closed)", (noninjectivity_proof(),)),
    )
    total = 0
    for label, proofs in groups:
        toll = 0
        for pf in proofs:
            check(pf, DIFF_RING_2)
            toll += _toll(pf)
        total += toll
        print(f"{label:<28} toll {toll:>9,}")
    print(f"{'TOTAL':<28} toll {total:>9,}")


if __name__ == "__main__":
    main()


__all__ = [
    "COLLISION_POINTS",
    "COLLISION_VALUE",
    "COMPONENTS",
    "add_rotate_rule",
    "cancel_pair_rule",
    "collision_proofs",
    "collision_statements",
    "derivation_one_proofs",
    "derivation_zero_proofs",
    "derivative_proofs",
    "derivative_rules",
    "derivative_statements",
    "det_proof",
    "det_term",
    "noninjectivity_proof",
    "noninjectivity_statement",
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
