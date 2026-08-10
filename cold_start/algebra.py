"""Abstract equational theories, as plain `Theory` objects.

The checker's term language is already abstract (`Fun(name, args)`), and a
`Theory` is just a set of axiom formulas with implicitly-universal free
variables. So an algebraic structure needs no kernel changes -- only its
axioms. These are the first rung toward non-commutative algebra (the road to
Clifford): structures where commutativity is an *extra* assumption, never a
theorem.

The monoid and ring theories are closed single-sorted signatures.
MONOID_ACTION is many-sorted (sorts `M` and `X`, via `ACTION_SIG`) -- the first
place sorts earn their keep, on the way to modules and Clifford.
"""

from __future__ import annotations

from . import vocabulary as _v
from .syntax import Eq, Formula, Fun, Not, Term, Var
from .theory import Signature, Theory

# --- signature ------------------------------------------------------------

E = Fun("e", ())  # the unit element


_x, _y, _z = Var("x"), Var("y"), Var("z")

# --- axioms (free vars implicitly universally quantified) -----------------

ASSOC = Eq(_v.mul(_v.mul(_x, _y), _z), _v.mul(_x, _v.mul(_y, _z)))
LEFT_ID = Eq(_v.mul(E, _x), _x)
RIGHT_ID = Eq(_v.mul(_x, E), _x)
COMM = Eq(_v.mul(_x, _y), _v.mul(_y, _x))

# --- theories -------------------------------------------------------------

SEMIGROUP_SIG = Signature(
    sorts=frozenset({""}),
    ranks=(("*", ("", ""), ""),),
)
MONOID_SIG = Signature(
    sorts=frozenset({""}),
    ranks=(("e", (), ""), ("*", ("", ""), "")),
)

SEMIGROUP = Theory(axioms=frozenset({ASSOC}), signature=SEMIGROUP_SIG)
MONOID = Theory(axioms=frozenset({ASSOC, LEFT_ID, RIGHT_ID}), signature=MONOID_SIG)
COMM_MONOID = Theory(
    axioms=frozenset({ASSOC, LEFT_ID, RIGHT_ID, COMM}),
    signature=MONOID_SIG,
)


# --- a many-sorted theory: a monoid M acting on a set X -------------------
# The first place sorts earn their keep: `act` takes an M and an X and returns
# an X, so `act(x, m)` is ill-sorted and the checker rejects it. This is the
# shape (scalars acting on vectors) that generalizes to modules and Clifford.


def act(m: Term, x: Term) -> Term:
    return Fun("act", (m, x))


_m, _n, _p = Var("m", "M"), Var("n", "M"), Var("p", "M")
_xX = Var("x", "X")

ACTION_SIG = Signature(
    sorts=frozenset({"M", "X"}),
    ranks=(
        ("e", (), "M"),
        ("*", ("M", "M"), "M"),
        ("act", ("M", "X"), "X"),
    ),
)

M_ASSOC = Eq(_v.mul(_v.mul(_m, _n), _p), _v.mul(_m, _v.mul(_n, _p)))
M_LEFT_ID = Eq(_v.mul(E, _m), _m)
M_RIGHT_ID = Eq(_v.mul(_m, E), _m)
ACT_ID = Eq(act(E, _xX), _xX)  # act(e, x) = x
ACT_COMP = Eq(act(_m, act(_n, _xX)), act(_v.mul(_m, _n), _xX))

MONOID_ACTION = Theory(
    axioms=frozenset({M_ASSOC, M_LEFT_ID, M_RIGHT_ID, ACT_ID, ACT_COMP}),
    signature=ACTION_SIG,
)


# --- rings ----------------------------------------------------------------
# A ring with unity (not assumed commutative): an abelian group under +, a
# monoid under *, tied by distributivity. `*` reuses `mul`; commutativity of `*`
# is an EXTRA axiom (COMM), never a theorem -- the non-commutative matrix model
# in the tests is the witness.

ADD_ASSOC = Eq(_v.add(_v.add(_x, _y), _z), _v.add(_x, _v.add(_y, _z)))
ADD_COMM = Eq(_v.add(_x, _y), _v.add(_y, _x))
ADD_ZERO = Eq(_v.add(_x, _v.ZERO), _x)
ADD_NEG = Eq(_v.add(_x, _v.neg(_x)), _v.ZERO)
MUL_ASSOC = Eq(_v.mul(_v.mul(_x, _y), _z), _v.mul(_x, _v.mul(_y, _z)))
MUL_LEFT_ID = Eq(_v.mul(_v.ONE, _x), _x)
MUL_RIGHT_ID = Eq(_v.mul(_x, _v.ONE), _x)
DIST_LEFT = Eq(
    _v.mul(_x, _v.add(_y, _z)),
    _v.add(_v.mul(_x, _y), _v.mul(_x, _z)),
)
DIST_RIGHT = Eq(
    _v.mul(_v.add(_x, _y), _z),
    _v.add(_v.mul(_x, _z), _v.mul(_y, _z)),
)

RING_AXIOMS = frozenset(
    {
        ADD_ASSOC,
        ADD_COMM,
        ADD_ZERO,
        ADD_NEG,
        MUL_ASSOC,
        MUL_LEFT_ID,
        MUL_RIGHT_ID,
        DIST_LEFT,
        DIST_RIGHT,
    }
)

RING_SIG = Signature(
    sorts=frozenset({""}),
    ranks=(
        ("0", (), ""),
        ("1", (), ""),
        ("+", ("", ""), ""),
        ("neg", ("",), ""),
        ("*", ("", ""), ""),
    ),
)
AB_GROUP_SIG = Signature(
    sorts=frozenset({""}),
    ranks=(("0", (), ""), ("+", ("", ""), ""), ("neg", ("",), "")),
)

RING = Theory(axioms=RING_AXIOMS, signature=RING_SIG)
COMM_RING = Theory(
    axioms=RING_AXIOMS | {COMM},
    signature=RING_SIG,
)  # COMM is x*y = y*x (reused)

AB_GROUP = Theory(
    axioms=frozenset({ADD_ASSOC, ADD_COMM, ADD_ZERO, ADD_NEG}),
    signature=AB_GROUP_SIG,
)
"""The additive fragment of RING on its own: an abelian group (0, +, neg).
The source theory of the Grothendieck bridge in `cold_start.integers`."""


# --- characteristic two ----------------------------------------------------
# `x + x = 0` replaces ADD_NEG: every element is its own additive inverse, so
# `neg` is not in the signature at all and the rewriting kits derive their
# cancellation from CHAR2 instead. NONTRIVIAL is what keeps the one-element
# ring out -- without it `0 = 1` is consistent and every separation collapses.
# Shared, as mathematical content must be, by `groupring2` and `diffring2`.

CHAR2: Formula = Eq(_v.add(_x, _x), _v.ZERO)
NONTRIVIAL: Formula = Not(Eq(_v.ZERO, _v.ONE))
