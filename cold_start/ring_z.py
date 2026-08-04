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

Two facts do the work. `ring_kit` gives `prove_eq` a polynomial normal form,
deciding every commutative-semiring identity the shuffles below reduce to.
And `by_combination` admits TERM COEFFICIENTS: equal differences stay equal
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
from .combination import Hypothesis, by_combination
from .integers import ADD_COMPONENTWISE, NEG_AS_SWAP, ZERO_AS_DIAGONAL, int_eq
from .peano import PEANO, mul
from .peano_proofs import ring_kit
from .presburger import ZERO, S, add
from .proof import Assume, ExistsIntro, ForallIntro, ImpIntro, Pf, Refl, Sym
from .quotient import QuotientInterpretation, Vec, VecSymbol, vec
from .syntax import Eq, Formula, Term, exists

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

_KIT = ring_kit()
_BUDGET = 5000  # degree-3 shuffles (mul assoc, distribution) outgrow the default


def _cancel(goal: Eq, hyps: tuple[Hypothesis, ...]) -> Pf:
    return by_combination(goal, hyps, _KIT, _BUDGET)


def _assume(eq: Eq) -> Hypothesis:
    return eq, Assume(eq), None


def _flip(eq: Eq) -> Hypothesis:
    return Eq(eq.rhs, eq.lhs), Sym(Assume(eq)), None


def _scale(eq: Eq, coeff: Term) -> Hypothesis:
    return eq, Assume(eq), coeff


def _scale_flip(eq: Eq, coeff: Term) -> Hypothesis:
    return Eq(eq.rhs, eq.lhs), Sym(Assume(eq)), coeff


# ---------------------------------------------------------------------------
# Payments: the equivalence laws
# ---------------------------------------------------------------------------

_a, _b, _c = vec("x!", 2), vec("y!", 2), vec("z!", 2)


def _pay_refl() -> Pf:
    return Refl(add(_a[0], _a[1]))


def _pay_sym() -> Pf:
    hyp = int_eq(_a, _b)
    return ImpIntro(hyp, Sym(Assume(hyp)))


def _pay_trans() -> Pf:
    h1, h2 = int_eq(_a, _b), int_eq(_b, _c)
    core = _cancel(int_eq(_a, _c), (_assume(h1), _assume(h2)))
    return ImpIntro(h1, ImpIntro(h2, core))


# ---------------------------------------------------------------------------
# Payments: totality and respect
# ---------------------------------------------------------------------------


def _pay_totality(symbol: VecSymbol, image: tuple[Term, Term]) -> Pf:
    """Every totality witness is the image tuple itself, where the graph
    collapses to a reflexive equation -- for `*`, the difference product's
    own components."""
    args = symbol._args(2)
    claim = symbol.graph(args, vec("c!", 2))
    outer: Formula = exists("c!.1", "", exists("c!.2", "", claim))
    inner = exists("c!.2", "", symbol.graph(args, (image[0], vec("c!", 2)[1])))
    ground = symbol.graph(args, image)
    assert type(ground) is Eq and ground.lhs == ground.rhs
    return ExistsIntro(outer, image[0], ExistsIntro(inner, image[1], Refl(ground.lhs)))


def _pay_respect(symbol: VecSymbol, orient) -> Pf:
    """The respect chain, discharged in obligation order: one ~ per argument
    slot, then the two graph hypotheses, one combination at the core."""
    args, primed = symbol._args(2), symbol._primed(2)
    c, d = vec("c!", 2), vec("d!", 2)
    eps_hyps = tuple(int_eq(old, new) for old, new in zip(args, primed, strict=True))
    g_c = symbol.graph(args, c)
    g_d = symbol.graph(primed, d)
    assert type(g_c) is Eq and type(g_d) is Eq
    core = _cancel(int_eq(c, d), orient(eps_hyps, g_c, g_d))
    out = ImpIntro(g_c, ImpIntro(g_d, core))
    for hyp in reversed(eps_hyps):
        out = ImpIntro(hyp, out)
    return out


def _orient_zero(eps_hyps, g_c: Eq, g_d: Eq):
    return (_assume(g_c), _flip(g_d))


def _orient_one(eps_hyps, g_c: Eq, g_d: Eq):
    return (_assume(g_c), _flip(g_d))


def _orient_add(eps_hyps, g_c: Eq, g_d: Eq):
    return (_flip(g_c), _assume(g_d), _assume(eps_hyps[0]), _assume(eps_hyps[1]))


def _orient_neg(eps_hyps, g_c: Eq, g_d: Eq):
    return (_flip(eps_hyps[0]), _flip(g_c), _assume(g_d))


def _orient_mul(eps_hyps, g_c: Eq, g_d: Eq):
    """a ~ a' scaled by b's components, b ~ b' scaled by a''s components:
    exactly the cross-multiplication that makes equal differences multiply."""
    b, a_prime = vec("x!1", 2), vec("y!0", 2)
    return (
        _scale(eps_hyps[0], b[0]),
        _scale_flip(eps_hyps[0], b[1]),
        _scale(eps_hyps[1], a_prime[0]),
        _scale_flip(eps_hyps[1], a_prime[1]),
        _flip(g_c),
        _assume(g_d),
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


def _g_add(args: tuple[Vec, ...], res: Vec) -> Eq:
    g = ADD_COMPONENTWISE.graph(args, res)
    assert type(g) is Eq
    return g


def _g_neg(args: tuple[Vec, ...], res: Vec) -> Eq:
    g = NEG_AS_SWAP.graph(args, res)
    assert type(g) is Eq
    return g


def _g_zero(args: tuple[Vec, ...], res: Vec) -> Eq:
    g = ZERO_AS_DIAGONAL.graph(args, res)
    assert type(g) is Eq
    return g


def _pay_axiom(guards: tuple[tuple[str, Formula], ...], core: Pf) -> Pf:
    out = core
    for marker, guard in reversed(guards):
        out = ImpIntro(guard, out)
        for i in reversed(range(2)):
            out = ForallIntro(f"{marker}.{i + 1}", "", out)
    return out


def _pay_add_zero() -> Pf:
    g0 = _g_zero((), _u)
    ga = _g_add((_x, _u), _u0)
    core = _cancel(int_eq(_u0, _x), (_flip(ga), _assume(g0)))
    return _pay_axiom((("u!", g0), ("u!0", ga)), core)


def _pay_add_comm() -> Pf:
    g_r = _g_add((_y, _x), _u)
    g_l = _g_add((_x, _y), _u0)
    core = _cancel(int_eq(_u0, _u), (_flip(g_l), _assume(g_r)))
    return _pay_axiom((("u!", g_r), ("u!0", g_l)), core)


def _pay_add_assoc() -> Pf:
    g1 = _g_add((_y, _z), _u)
    g2 = _g_add((_x, _u), _u0)
    g3 = _g_add((_x, _y), _u1)
    g4 = _g_add((_u1, _z), _u2)
    core = _cancel(
        int_eq(_u2, _u0),
        (_assume(g1), _assume(g2), _flip(g3), _flip(g4)),
    )
    return _pay_axiom((("u!", g1), ("u!0", g2), ("u!1", g3), ("u!2", g4)), core)


def _pay_add_neg() -> Pf:
    g0 = _g_zero((), _u)
    gn = _g_neg((_x,), _u0)
    ga = _g_add((_x, _u0), _u1)
    core = _cancel(int_eq(_u1, _u), (_flip(ga), _flip(gn), _flip(g0)))
    return _pay_axiom((("u!", g0), ("u!0", gn), ("u!1", ga)), core)


def _pay_mul_assoc() -> Pf:
    """(x*y)*z = x*(y*z): the degree-3 heart of the bridge. Re-associating a
    difference product means moving z's components across x ~-classes, so g3
    is scaled by z's components and g1 by x's."""
    g1 = _g_mul((_y, _z), _u)
    g2 = _g_mul((_x, _u), _u0)
    g3 = _g_mul((_x, _y), _u1)
    g4 = _g_mul((_u1, _z), _u2)
    core = _cancel(
        int_eq(_u2, _u0),
        (
            _flip(g4),
            _assume(g2),
            _scale_flip(g3, _z[0]),
            _scale(g3, _z[1]),
            _scale(g1, _x[0]),
            _scale_flip(g1, _x[1]),
        ),
    )
    return _pay_axiom((("u!", g1), ("u!0", g2), ("u!1", g3), ("u!2", g4)), core)


def _pay_mul_left_id() -> Pf:
    g1 = _g_one((), _u)
    g2 = _g_mul((_u, _x), _u0)
    core = _cancel(
        int_eq(_u0, _x),
        (_flip(g2), _scale(g1, _x[0]), _scale_flip(g1, _x[1])),
    )
    return _pay_axiom((("u!", g1), ("u!0", g2)), core)


def _pay_mul_right_id() -> Pf:
    g1 = _g_one((), _u)
    g2 = _g_mul((_x, _u), _u0)
    core = _cancel(
        int_eq(_u0, _x),
        (_flip(g2), _scale(g1, _x[0]), _scale_flip(g1, _x[1])),
    )
    return _pay_axiom((("u!", g1), ("u!0", g2)), core)


def _pay_mul_comm() -> Pf:
    """x*y = y*x: the difference product is literally symmetric, so this is
    the ADD_COMM shape with the semiring kit sorting the monomials."""
    g_r = _g_mul((_y, _x), _u)
    g_l = _g_mul((_x, _y), _u0)
    core = _cancel(int_eq(_u0, _u), (_flip(g_l), _assume(g_r)))
    return _pay_axiom((("u!", g_r), ("u!0", g_l)), core)


def _pay_dist_left() -> Pf:
    g1 = _g_mul((_x, _y), _u)
    g2 = _g_mul((_x, _z), _u0)
    g3 = _g_add((_u, _u0), _u1)
    g4 = _g_add((_y, _z), _u2)
    g5 = _g_mul((_x, _u2), _u3)
    core = _cancel(
        int_eq(_u3, _u1),
        (
            _flip(g5),
            _scale_flip(g4, _x[0]),
            _scale(g4, _x[1]),
            _assume(g3),
            _assume(g1),
            _assume(g2),
        ),
    )
    return _pay_axiom(
        (("u!", g1), ("u!0", g2), ("u!1", g3), ("u!2", g4), ("u!3", g5)),
        core,
    )


def _pay_dist_right() -> Pf:
    g1 = _g_mul((_x, _z), _u)
    g2 = _g_mul((_y, _z), _u0)
    g3 = _g_add((_u, _u0), _u1)
    g4 = _g_add((_x, _y), _u2)
    g5 = _g_mul((_u2, _z), _u3)
    core = _cancel(
        int_eq(_u3, _u1),
        (
            _flip(g5),
            _scale_flip(g4, _z[0]),
            _scale(g4, _z[1]),
            _assume(g3),
            _assume(g1),
            _assume(g2),
        ),
    )
    return _pay_axiom(
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
            ("equivalence:refl", _pay_refl()),
            ("equivalence:sym", _pay_sym()),
            ("equivalence:trans", _pay_trans()),
            ("totality:0", _pay_totality(ZERO_AS_DIAGONAL, (ZERO, ZERO))),
            ("respect:0", _pay_respect(ZERO_AS_DIAGONAL, _orient_zero)),
            ("totality:1", _pay_totality(ONE_ABOVE_DIAGONAL, (S(ZERO), ZERO))),
            ("respect:1", _pay_respect(ONE_ABOVE_DIAGONAL, _orient_one)),
            (
                "totality:+",
                _pay_totality(ADD_COMPONENTWISE, (add(x0[0], x1[0]), add(x0[1], x1[1]))),
            ),
            ("respect:+", _pay_respect(ADD_COMPONENTWISE, _orient_add)),
            ("totality:neg", _pay_totality(NEG_AS_SWAP, (x0[1], x0[0]))),
            ("respect:neg", _pay_respect(NEG_AS_SWAP, _orient_neg)),
            ("totality:*", _pay_totality(MUL_DIFFERENCE_PRODUCT, product_image)),
            ("respect:*", _pay_respect(MUL_DIFFERENCE_PRODUCT, _orient_mul)),
            (f"axiom:{ADD_ZERO!r}", _pay_add_zero()),
            (f"axiom:{ADD_COMM!r}", _pay_add_comm()),
            (f"axiom:{ADD_ASSOC!r}", _pay_add_assoc()),
            (f"axiom:{ADD_NEG!r}", _pay_add_neg()),
            (f"axiom:{MUL_ASSOC!r}", _pay_mul_assoc()),
            (f"axiom:{MUL_LEFT_ID!r}", _pay_mul_left_id()),
            (f"axiom:{MUL_RIGHT_ID!r}", _pay_mul_right_id()),
            (f"axiom:{COMM!r}", _pay_mul_comm()),
            (f"axiom:{DIST_LEFT!r}", _pay_dist_left()),
            (f"axiom:{DIST_RIGHT!r}", _pay_dist_right()),
        ),
    )


if __name__ == "__main__":
    from .quotient import verify

    report = verify(ring_z_interpretation())
    print(
        f"{report.name}: bridge {report.bridge_size} nodes; "
        f"toll {report.total_toll}; open {report.open_labels()}"
    )


__all__ = [
    "MUL_DIFFERENCE_PRODUCT",
    "ONE_ABOVE_DIAGONAL",
    "ring_z_interpretation",
]
