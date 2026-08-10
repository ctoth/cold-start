"""The jc characteristic-2 Jacobian counterexample, entering the ledger.

The map (found by SAT search over monomial supports in the jc repository):

    F1 = Z + XY + XY^2 + X^2Y^2 + X^2YZ + X^2Y^2Z + X^3Y^2Z
    F2 = Y + XY^2
    F3 = X + Y + XY^2 + X^2Z

This module is the first, smallest slice of its certificate: the three
rational points (0,0,1), (1,0,1), (1,1,1) all evaluate to (1,0,0) — nine
closed equations in DIFF_RING_2, proved by the sparse characteristic-2
normalizer. The components are *builders* (functions of three
terms), so the same definitions state evaluation theorems at constants and,
later, derivative and determinant theorems at the generators.

Generic characteristic-2 algebra proofs and normalization context live in
`diffring2_proofs`; this module owns only the map, derivative statements,
determinant, collisions, and their use of the generic certified algebra.
"""

from __future__ import annotations

from time import perf_counter

from .diffring2 import D_AXIOMS, GEN_X, GEN_Y, GEN_Z, NONTRIVIAL, dx, dy, dz
from .diffring2_proofs import (
    DIFF_RING_2_CONTEXT,
    evaluation_rules,
)
from .diffring2_proofs import (
    derivation_one_proofs as _derivation_one_proofs,
)
from .diffring2_proofs import (
    derivation_zero_proofs as _derivation_zero_proofs,
)
from .groebner2 import CertifiedMembership, prove_ideal_membership
from .proof import Assume, Axiom, ExistsIntro, Pf, Sym, Trans, proof_size
from .prop import And, and_intro
from .ring_nf import ring_eq
from .syntax import Eq, Formula, Not, Term, Var, exists
from .tactics import Rule, axiom_rule, lemma_rule, normalize
from .vocabulary import ONE, ZERO, add, mul, product, summation

# --- the map, as term builders --------------------------------------------


def f1(x: Term, y: Term, z: Term) -> Term:
    return summation(
        z,
        product(x, y),
        product(x, y, y),
        product(x, x, y, y),
        product(x, x, y, z),
        product(x, x, y, y, z),
        product(x, x, x, y, y, z),
    )


def f2(x: Term, y: Term, z: Term) -> Term:
    return summation(y, product(x, y, y))


def f3(x: Term, y: Term, z: Term) -> Term:
    return summation(x, y, product(x, y, y), product(x, x, z))


COMPONENTS = (f1, f2, f3)

# --- the derivative lemmas ------------------------------------------------


def derivative_rules() -> tuple[Rule, ...]:
    """Push D symbols to generators and simplify zero/one before ring_nf."""
    return (
        *(axiom_rule(ax) for ax in D_AXIOMS),
        *evaluation_rules(),
    )


def derivative_statements() -> tuple[Formula, ...]:
    """The Jacobian matrix, row by row: D(component) = explicit polynomial,
    the data the jc finder computes with `pderiv` (char-2: even powers die)."""
    x, y, z = GEN_X, GEN_Y, GEN_Z
    rows = (
        (
            summation(y, product(y, y), product(x, x, y, y, z)),  # dF1/dx
            summation(x, product(x, x, z)),  # dF1/dy
            summation(ONE, product(x, x, y), product(x, x, y, y), product(x, x, x, y, y)),  # dF1/dz
        ),
        (product(y, y), ONE, ZERO),  # dF2/dx, dF2/dy, dF2/dz
        (summation(ONE, product(y, y)), ONE, product(x, x)),  # dF3/dx, dF3/dy, dF3/dz
    )
    return tuple(
        Eq(d(component(x, y, z)), rhs)
        for component, row in zip(COMPONENTS, rows, strict=True)
        for d, rhs in zip((dx, dy, dz), row, strict=True)
    )


def derivative_proofs(budget: int = 20_000) -> tuple[Pf, ...]:
    rules = derivative_rules()
    out: list[Pf] = []
    for statement in derivative_statements():
        if type(statement) is not Eq:
            raise TypeError("derivative statement must be an equality")
        eliminated, elimination = normalize(statement.lhs, rules, budget)
        out.append(
            Trans(
                elimination,
                ring_eq(Eq(eliminated, statement.rhs), DIFF_RING_2_CONTEXT),
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
    rewritten, rewrite_proof = normalize(det_term(), entry_rules, budget)
    return Trans(
        rewrite_proof,
        ring_eq(Eq(rewritten, ONE), DIFF_RING_2_CONTEXT),
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


def collision_proofs() -> tuple[Pf, ...]:
    return tuple(ring_eq(stmt, DIFF_RING_2_CONTEXT) for stmt in collision_statements())


# --- an ideal consequence of the Jacobian map ----------------------------


def jacobian_ideal_consequence_sources() -> tuple[Eq, ...]:
    """Two conditional equations about the map at its generic point."""
    x, y, z = GEN_X, GEN_Y, GEN_Z
    return (
        Eq(f1(x, y, z), ONE),
        Eq(f2(x, y, z), ZERO),
    )


def jacobian_ideal_consequence_statement() -> Eq:
    """The sum of the first two components is one on that conditional fiber."""
    x, y, z = GEN_X, GEN_Y, GEN_Z
    return Eq(add(f1(x, y, z), f2(x, y, z)), ONE)


def jacobian_ideal_consequence() -> CertifiedMembership:
    """Search for cofactors, then elaborate them into an ordinary proof."""
    sources = jacobian_ideal_consequence_sources()
    result = prove_ideal_membership(
        jacobian_ideal_consequence_statement(),
        tuple((source, Assume(source)) for source in sources),
        DIFF_RING_2_CONTEXT,
    )
    if not isinstance(result, CertifiedMembership):
        raise AssertionError(f"Jacobian ideal consequence was not certified: {result!r}")
    return result


# --- the answer surface ---------------------------------------------------


def main() -> None:
    """Re-check every theorem of the certificate and print its toll.
    Like the ledger: numbers re-derived by the trusted checker on every
    run, never quoted from documentation."""
    from .checker import check
    from .diffring2 import DIFF_RING_2

    ideal_started = perf_counter()
    ideal = jacobian_ideal_consequence()
    ideal_seconds = perf_counter() - ideal_started
    groups: tuple[tuple[str, tuple[Pf, ...]], ...] = (
        ("collisions (9)", collision_proofs()),
        ("derivative lemmas (9)", derivative_proofs()),
        ("det J = 1", (det_proof(),)),
        ("D(0) = 0 (3)", _derivation_zero_proofs()),
        ("D(1) = 0 (3)", _derivation_one_proofs()),
        ("non-injectivity (closed)", (noninjectivity_proof(),)),
        ("ideal consequence", (ideal.proof,)),
    )
    total = 0
    for label, proofs in groups:
        toll = 0
        for pf in proofs:
            check(pf, DIFF_RING_2)
            toll += proof_size(pf)
        total += toll
        print(f"{label:<28} toll {toll:>9,}")
    print(f"{'TOTAL':<28} toll {total:>9,}")
    stats = ideal.witness.stats
    print(
        "ideal search                 "
        f"steps {stats.steps:,}, degree {stats.max_degree}, "
        f"basis {stats.basis_size}, cofactors {stats.max_cofactor_monomials}, "
        f"construction {ideal_seconds:.6f}s"
    )


if __name__ == "__main__":
    main()


__all__ = [
    "COLLISION_POINTS",
    "COLLISION_VALUE",
    "collision_proofs",
    "collision_statements",
    "derivative_proofs",
    "derivative_statements",
    "det_proof",
    "det_term",
    "jacobian_ideal_consequence",
    "jacobian_ideal_consequence_sources",
    "jacobian_ideal_consequence_statement",
    "noninjectivity_proof",
    "noninjectivity_statement",
    "f1",
    "f2",
    "f3",
]
