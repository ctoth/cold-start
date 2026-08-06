"""The differential commutative ring of characteristic 2 on generators X, Y, Z.

The theory the jc characteristic-2 Jacobian certificate lives in. Two design
decisions carry it:

- **Characteristic 2 replaces negation.** `x + x = 0` makes every element its
  own additive inverse, so the signature drops `neg` entirely and the additive
  axioms are a commutative monoid plus CHAR2 — leaner terms for the rewriting
  tactics downstream.
- **The derivative is a function symbol, not trusted code.** `DX`, `DY`, `DZ`
  are unary symbols whose meaning is exhausted by the differential-ring
  axioms: additivity, the Leibniz rule, and their values on the generators
  (`DX(X) = 1`, `DX(Y) = 0`, ...). "dF1/dx = <explicit polynomial>" is then a
  *checked rewriting theorem*, where the Lean-side certificate had to trust
  its own `pderivX` definition. `D(0) = 0` and `D(1) = 0` are deliberately
  NOT axioms — both are theorems (D(0) = D(0+0) = D0 + D0 = 0 by CHAR2, and
  D(1) = D(1*1) = D1 + D1 likewise), which is exactly the kind of debt this
  repo prefers proved over assumed.

The generators are CONSTANTS (`Fun`, not `Var`): an axiom's free variables
are implicitly universal, and `DX(a) = 0` for all `a` is false. Nontriviality
(`0 ≠ 1`) is the one non-equational axiom; the existential non-injectivity
theorem needs it to tell the collision's preimages apart.
"""

from __future__ import annotations

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
from .syntax import Eq, Formula, Fun, Not, Term, Var
from .theory import Signature, Theory
from .vocabulary import ONE, ZERO, add, mul

# --- generators and derivations -------------------------------------------

GEN_X: Term = Fun("X", ())
GEN_Y: Term = Fun("Y", ())
GEN_Z: Term = Fun("Z", ())
GENERATORS: tuple[Term, ...] = (GEN_X, GEN_Y, GEN_Z)


def dx(term: Term) -> Term:
    return Fun("DX", (term,))


def dy(term: Term) -> Term:
    return Fun("DY", (term,))


def dz(term: Term) -> Term:
    return Fun("DZ", (term,))


DERIVATIONS = (dx, dy, dz)

# --- axioms ---------------------------------------------------------------

_x, _y = Var("x"), Var("y")

CHAR2: Formula = Eq(add(_x, _x), ZERO)
NONTRIVIAL: Formula = Not(Eq(ZERO, ONE))

_D_AXIOMS: list[Formula] = []
for _d, _values in zip(
    DERIVATIONS,
    ((ONE, ZERO, ZERO), (ZERO, ONE, ZERO), (ZERO, ZERO, ONE)),
    strict=True,
):
    _D_AXIOMS.append(Eq(_d(add(_x, _y)), add(_d(_x), _d(_y))))
    _D_AXIOMS.append(Eq(_d(mul(_x, _y)), add(mul(_d(_x), _y), mul(_x, _d(_y)))))
    for _g, _v in zip(GENERATORS, _values, strict=True):
        _D_AXIOMS.append(Eq(_d(_g), _v))

D_ADDITIVITY, D_LEIBNIZ = _D_AXIOMS[0], _D_AXIOMS[1]  # the DX pair, for callers

# --- the theory -----------------------------------------------------------

DIFF_RING_2_SIG = Signature(
    sorts=frozenset({""}),
    ranks=(
        ("0", (), ""),
        ("1", (), ""),
        ("+", ("", ""), ""),
        ("*", ("", ""), ""),
        ("X", (), ""),
        ("Y", (), ""),
        ("Z", (), ""),
        ("DX", ("",), ""),
        ("DY", ("",), ""),
        ("DZ", ("",), ""),
    ),
)

DIFF_RING_2 = Theory(
    axioms=frozenset(
        {
            ADD_ASSOC,
            ADD_COMM,
            ADD_ZERO,
            MUL_ASSOC,
            MUL_LEFT_ID,
            MUL_RIGHT_ID,
            COMM,
            DIST_LEFT,
            DIST_RIGHT,
            CHAR2,
            NONTRIVIAL,
            *_D_AXIOMS,
        }
    ),
    signature=DIFF_RING_2_SIG,
)

__all__ = [
    "CHAR2",
    "D_ADDITIVITY",
    "D_LEIBNIZ",
    "DERIVATIONS",
    "DIFF_RING_2",
    "DIFF_RING_2_SIG",
    "GENERATORS",
    "GEN_X",
    "GEN_Y",
    "GEN_Z",
    "NONTRIVIAL",
    "dx",
    "dy",
    "dz",
]
