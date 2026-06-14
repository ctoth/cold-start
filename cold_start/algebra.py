"""Abstract equational theories, as plain `Theory` objects.

The checker's term language is already abstract (`Fun(name, args)`), and a
`Theory` is just a set of axiom formulas with implicitly-universal free
variables. So an algebraic structure needs no kernel changes -- only its
axioms. These are the first rung toward non-commutative algebra (the road to
Clifford): structures where commutativity is an *extra* assumption, never a
theorem.

Signature here is single-sorted: a binary product `*` and a unit `e`. (Sorts --
scalars vs vectors -- come later, when we need them for modules and forms.)
"""

from __future__ import annotations

from .checker import Signature, Theory
from .syntax import Eq, Fun, Term, Var

# --- signature ------------------------------------------------------------

E = Fun("e", ())  # the unit element


def mul(a: Term, b: Term) -> Term:
    return Fun("*", (a, b))


_x, _y, _z = Var("x"), Var("y"), Var("z")

# --- axioms (free vars implicitly universally quantified) -----------------

ASSOC = Eq(mul(mul(_x, _y), _z), mul(_x, mul(_y, _z)))  # (x*y)*z = x*(y*z)
LEFT_ID = Eq(mul(E, _x), _x)  # e*x = x
RIGHT_ID = Eq(mul(_x, E), _x)  # x*e = x
COMM = Eq(mul(_x, _y), mul(_y, _x))  # x*y = y*x   -- an EXTRA assumption

# --- theories -------------------------------------------------------------

SEMIGROUP = Theory(axioms=frozenset({ASSOC}))
MONOID = Theory(axioms=frozenset({ASSOC, LEFT_ID, RIGHT_ID}))
COMM_MONOID = Theory(axioms=frozenset({ASSOC, LEFT_ID, RIGHT_ID, COMM}))


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

M_ASSOC = Eq(mul(mul(_m, _n), _p), mul(_m, mul(_n, _p)))
M_LEFT_ID = Eq(mul(E, _m), _m)
M_RIGHT_ID = Eq(mul(_m, E), _m)
ACT_ID = Eq(act(E, _xX), _xX)  # act(e, x) = x
ACT_COMP = Eq(act(_m, act(_n, _xX)), act(mul(_m, _n), _xX))  # m·(n·x) = (m*n)·x

MONOID_ACTION = Theory(
    axioms=frozenset({M_ASSOC, M_LEFT_ID, M_RIGHT_ID, ACT_ID, ACT_COMP}),
    signature=ACTION_SIG,
)
