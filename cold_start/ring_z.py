"""The full ring of integers, interpreted into Peano arithmetic.

The Grothendieck bridge (`cold_start.integers`) carried ℤ's abelian group
into Presburger on pairs of naturals, `(a, b)` meaning `a - b`. This module
carries the whole COMMUTATIVE RING across, into PEANO, on the same pairs and
the same defined equivalence -- the two new symbols are

    1        becomes  one above the diagonal   c.1 = S(c.2)
    x * y    becomes  the difference product   (x1*y1 + x2*y2, x1*y2 + x2*y1)

-- the second being exactly how (a-b)(c-d) expands when subtraction is not
allowed to appear. All 23 obligations are paid: three equivalence laws,
totality and respect for the five symbols, and the ten translated ring
axioms, multiplicative associativity, commutativity, units, and both
distributive laws among them.

Two facts do the work. The PEANO semiring context gives the shared sparse
normalizer proved polynomial merge recipes, deciding every commutative-semiring
identity the shuffles below reduce to. The combination elaborator admits term
coefficients: equal differences stay equal
under `*` only after each hypothesis is multiplied through by factors of the
other -- e.g. respect for `*` scales `a ~ a'` by `b1` and `b2`, and `b ~ b'`
by `a'1` and `a'2`, before one cancellation lands the goal. The plain
cancellation of the group bridge cannot say that; this is the move that
makes multiplication cross.

Untrusted, like every prover module: `check` remains the only judge.
"""

from __future__ import annotations

from .algebra import (
    ADD_ASSOC,
    ADD_COMM,
    ADD_NEG,
    ADD_ZERO,
    COMM,
    COMM_RING,
    DIST_LEFT,
    DIST_RIGHT,
    MUL_ASSOC,
    MUL_LEFT_ID,
    MUL_RIGHT_ID,
)
from .integer_pairs import (
    ADD_COMPONENTWISE,
    NEG_AS_SWAP,
    ZERO_AS_DIAGONAL,
    add_graph,
    assume,
    cancel,
    flip,
    guarded_axiom_payment,
    int_eq,
    orient_add,
    orient_neg,
    orient_zero,
    pay_add_assoc,
    pay_add_comm,
    pay_add_neg,
    pay_add_zero,
    pay_equivalence_refl,
    pay_equivalence_sym,
    pay_equivalence_trans,
    pay_respect,
    pay_totality,
)
from .interp import ObligationKey
from .peano import PEANO
from .proof import Assume, Pf, Sym
from .quotient import QuotientInterpretation, Vec, VecSymbol, vec
from .ring_nf import CombinationSource
from .syntax import Eq, Term
from .vocabulary import ZERO, S, add, mul

# ---------------------------------------------------------------------------
# The two new symbols
# ---------------------------------------------------------------------------


def _g_one(args: tuple[Vec, ...], res: Vec) -> Eq:
    return Eq(res[0], S(res[1]))


def _g_mul(args: tuple[Vec, ...], res: Vec) -> Eq:
    a, b = args
    return int_eq(
        (
            add(mul(a[0], b[0]), mul(a[1], b[1])),
            add(mul(a[0], b[1]), mul(a[1], b[0])),
        ),
        res,
    )


ONE_ABOVE_DIAGONAL = VecSymbol("1", 0, _g_one)
MUL_DIFFERENCE_PRODUCT = VecSymbol("*", 2, _g_mul)


# ---------------------------------------------------------------------------
# The proof engine: linear combinations under the semiring kit
# ---------------------------------------------------------------------------


def _scale(eq: Eq, coeff: Term) -> CombinationSource:
    return eq, Assume(eq), coeff


def _scale_flip(eq: Eq, coeff: Term) -> CombinationSource:
    return Eq(eq.rhs, eq.lhs), Sym(Assume(eq)), coeff


def _orient_one(
    eps_hyps: tuple[Eq, ...],
    g_c: Eq,
    g_d: Eq,
) -> tuple[CombinationSource, ...]:
    return (assume(g_c), flip(g_d))


def _orient_mul(
    eps_hyps: tuple[Eq, ...],
    g_c: Eq,
    g_d: Eq,
) -> tuple[CombinationSource, ...]:
    """a ~ a' scaled by b's components, b ~ b' scaled by a''s components:
    exactly the cross-multiplication that makes equal differences multiply."""
    b, a_prime = vec("x!1", 2), vec("y!0", 2)
    return (
        _scale(eps_hyps[0], b[0]),
        _scale_flip(eps_hyps[0], b[1]),
        _scale(eps_hyps[1], a_prime[0]),
        _scale_flip(eps_hyps[1], a_prime[1]),
        flip(g_c),
        assume(g_d),
    )


# ---------------------------------------------------------------------------
# Payments: the translated axioms
# ---------------------------------------------------------------------------
# Each translated axiom is a block of hoist guards around one equivalence
# atom; the payment mirrors the translator's wrapping exactly (hoists on the
# right-hand side first, innermost first) and pays the core by one linear
# combination. Bound markers are alpha-invisible, so the local u!-names need
# only bind in the translator's order, not spell its exact fresh names.

_x, _y, _z = vec("x", 2), vec("y", 2), vec("z", 2)
_u, _u0, _u1 = vec("u!", 2), vec("u!0", 2), vec("u!1", 2)
_u2, _u3 = vec("u!2", 2), vec("u!3", 2)


def _pay_mul_assoc() -> Pf:
    """(x*y)*z = x*(y*z): the degree-3 heart of the bridge. Re-associating a
    difference product means moving z's components across x ~-classes, so g3
    is scaled by z's components and g1 by x's."""
    g1 = _g_mul((_y, _z), _u)
    g2 = _g_mul((_x, _u), _u0)
    g3 = _g_mul((_x, _y), _u1)
    g4 = _g_mul((_u1, _z), _u2)
    core = cancel(
        int_eq(_u2, _u0),
        (
            flip(g4),
            assume(g2),
            _scale_flip(g3, _z[0]),
            _scale(g3, _z[1]),
            _scale(g1, _x[0]),
            _scale_flip(g1, _x[1]),
        ),
    )
    return guarded_axiom_payment((("u!", g1), ("u!0", g2), ("u!1", g3), ("u!2", g4)), core)


def _pay_mul_left_id() -> Pf:
    g1 = _g_one((), _u)
    g2 = _g_mul((_u, _x), _u0)
    core = cancel(
        int_eq(_u0, _x),
        (flip(g2), _scale(g1, _x[0]), _scale_flip(g1, _x[1])),
    )
    return guarded_axiom_payment((("u!", g1), ("u!0", g2)), core)


def _pay_mul_right_id() -> Pf:
    g1 = _g_one((), _u)
    g2 = _g_mul((_x, _u), _u0)
    core = cancel(
        int_eq(_u0, _x),
        (flip(g2), _scale(g1, _x[0]), _scale_flip(g1, _x[1])),
    )
    return guarded_axiom_payment((("u!", g1), ("u!0", g2)), core)


def _pay_mul_comm() -> Pf:
    """x*y = y*x: the difference product is literally symmetric, so this is
    the ADD_COMM shape with the semiring kit sorting the monomials."""
    g_r = _g_mul((_y, _x), _u)
    g_l = _g_mul((_x, _y), _u0)
    core = cancel(int_eq(_u0, _u), (flip(g_l), assume(g_r)))
    return guarded_axiom_payment((("u!", g_r), ("u!0", g_l)), core)


def _pay_dist_left() -> Pf:
    g1 = _g_mul((_x, _y), _u)
    g2 = _g_mul((_x, _z), _u0)
    g3 = add_graph((_u, _u0), _u1)
    g4 = add_graph((_y, _z), _u2)
    g5 = _g_mul((_x, _u2), _u3)
    core = cancel(
        int_eq(_u3, _u1),
        (
            flip(g5),
            _scale_flip(g4, _x[0]),
            _scale(g4, _x[1]),
            assume(g3),
            assume(g1),
            assume(g2),
        ),
    )
    return guarded_axiom_payment(
        (("u!", g1), ("u!0", g2), ("u!1", g3), ("u!2", g4), ("u!3", g5)),
        core,
    )


def _pay_dist_right() -> Pf:
    g1 = _g_mul((_x, _z), _u)
    g2 = _g_mul((_y, _z), _u0)
    g3 = add_graph((_u, _u0), _u1)
    g4 = add_graph((_x, _y), _u2)
    g5 = _g_mul((_u2, _z), _u3)
    core = cancel(
        int_eq(_u3, _u1),
        (
            flip(g5),
            _scale_flip(g4, _z[0]),
            _scale(g4, _z[1]),
            assume(g3),
            assume(g1),
            assume(g2),
        ),
    )
    return guarded_axiom_payment(
        (("u!", g1), ("u!0", g2), ("u!1", g3), ("u!2", g4), ("u!3", g5)),
        core,
    )


# ---------------------------------------------------------------------------
# The artifact
# ---------------------------------------------------------------------------


def ring_z_interpretation() -> QuotientInterpretation:
    """The commutative ring of integers -> PEANO, dimension 2, all paid."""
    x0, x1 = vec("x!0", 2), vec("x!1", 2)
    product_image = (
        add(mul(x0[0], x1[0]), mul(x0[1], x1[1])),
        add(mul(x0[0], x1[1]), mul(x0[1], x1[0])),
    )
    return QuotientInterpretation(
        name="ring-of-integers-into-peano",
        source=COMM_RING,
        target=PEANO,
        dim=2,
        equiv=int_eq,
        symbols=(
            ZERO_AS_DIAGONAL,
            ONE_ABOVE_DIAGONAL,
            ADD_COMPONENTWISE,
            NEG_AS_SWAP,
            MUL_DIFFERENCE_PRODUCT,
        ),
        payments=(
            (ObligationKey.equivalence("refl"), pay_equivalence_refl()),
            (ObligationKey.equivalence("sym"), pay_equivalence_sym()),
            (ObligationKey.equivalence("trans"), pay_equivalence_trans()),
            (ObligationKey.totality("0"), pay_totality(ZERO_AS_DIAGONAL, (ZERO, ZERO))),
            (ObligationKey.respect("0"), pay_respect(ZERO_AS_DIAGONAL, orient_zero)),
            (ObligationKey.totality("1"), pay_totality(ONE_ABOVE_DIAGONAL, (S(ZERO), ZERO))),
            (ObligationKey.respect("1"), pay_respect(ONE_ABOVE_DIAGONAL, _orient_one)),
            (
                ObligationKey.totality("+"),
                pay_totality(ADD_COMPONENTWISE, (add(x0[0], x1[0]), add(x0[1], x1[1]))),
            ),
            (ObligationKey.respect("+"), pay_respect(ADD_COMPONENTWISE, orient_add)),
            (ObligationKey.totality("neg"), pay_totality(NEG_AS_SWAP, (x0[1], x0[0]))),
            (ObligationKey.respect("neg"), pay_respect(NEG_AS_SWAP, orient_neg)),
            (ObligationKey.totality("*"), pay_totality(MUL_DIFFERENCE_PRODUCT, product_image)),
            (ObligationKey.respect("*"), pay_respect(MUL_DIFFERENCE_PRODUCT, _orient_mul)),
            (ObligationKey.axiom(ADD_ZERO), pay_add_zero()),
            (ObligationKey.axiom(ADD_COMM), pay_add_comm()),
            (ObligationKey.axiom(ADD_ASSOC), pay_add_assoc()),
            (ObligationKey.axiom(ADD_NEG), pay_add_neg()),
            (ObligationKey.axiom(MUL_ASSOC), _pay_mul_assoc()),
            (ObligationKey.axiom(MUL_LEFT_ID), _pay_mul_left_id()),
            (ObligationKey.axiom(MUL_RIGHT_ID), _pay_mul_right_id()),
            (ObligationKey.axiom(COMM), _pay_mul_comm()),
            (ObligationKey.axiom(DIST_LEFT), _pay_dist_left()),
            (ObligationKey.axiom(DIST_RIGHT), _pay_dist_right()),
        ),
    )


__all__ = [
    "MUL_DIFFERENCE_PRODUCT",
    "ONE_ABOVE_DIAGONAL",
    "ring_z_interpretation",
]
