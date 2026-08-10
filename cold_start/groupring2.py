"""The characteristic-two group ring of the Promislow group.

This is an equational presentation, not an executable group model.  The
trusted checker sees only a noncommutative unital char-2 ring together with
four named group elements, inverse equations, and the two presentation
relations.  Coordinate arithmetic belongs to the independent statement guard
in ``tests/test_groupring2.py``.

The group relations are oriented from positive generator words toward words
containing the named inverses.  This direction exposes the collection moves
used by the untrusted certificate prover while adding no multiplicative
commutativity axiom.
"""

from __future__ import annotations

from .algebra import (
    ADD_ASSOC,
    ADD_COMM,
    ADD_ZERO,
    CHAR2,
    DIST_LEFT,
    DIST_RIGHT,
    MUL_ASSOC,
    MUL_LEFT_ID,
    MUL_RIGHT_ID,
    NONTRIVIAL,
)
from .syntax import Eq, Formula, Fun, Term, Var
from .theory import Signature, Theory
from .vocabulary import ONE, mul

A: Term = Fun("A", ())
B: Term = Fun("B", ())
A_INV: Term = Fun("A'", ())
B_INV: Term = Fun("B'", ())

_x = Var("x")

A_RIGHT_INV: Formula = Eq(mul(A, A_INV), ONE)
A_LEFT_INV: Formula = Eq(mul(A_INV, A), ONE)
B_RIGHT_INV: Formula = Eq(mul(B, B_INV), ONE)
B_LEFT_INV: Formula = Eq(mul(B_INV, B), ONE)

# a^2 b = b a^-2 and b^2 a = a b^-2, right-nested throughout.
GROUP_REL_A: Formula = Eq(mul(A, mul(A, B)), mul(B, mul(A_INV, A_INV)))
GROUP_REL_B: Formula = Eq(mul(B, mul(B, A)), mul(A, mul(B_INV, B_INV)))

GROUP_RING_P2_SIG = Signature(
    sorts=frozenset({""}),
    ranks=(
        ("0", (), ""),
        ("1", (), ""),
        ("+", ("", ""), ""),
        ("*", ("", ""), ""),
        ("A", (), ""),
        ("B", (), ""),
        ("A'", (), ""),
        ("B'", (), ""),
    ),
)

GROUP_RING_P2 = Theory(
    axioms=frozenset(
        {
            ADD_ASSOC,
            ADD_COMM,
            ADD_ZERO,
            CHAR2,
            NONTRIVIAL,
            MUL_ASSOC,
            MUL_LEFT_ID,
            MUL_RIGHT_ID,
            DIST_LEFT,
            DIST_RIGHT,
            A_RIGHT_INV,
            A_LEFT_INV,
            B_RIGHT_INV,
            B_LEFT_INV,
            GROUP_REL_A,
            GROUP_REL_B,
        }
    ),
    signature=GROUP_RING_P2_SIG,
)

__all__ = [
    "A",
    "A_INV",
    "A_LEFT_INV",
    "A_RIGHT_INV",
    "B",
    "B_INV",
    "B_LEFT_INV",
    "B_RIGHT_INV",
    "CHAR2",
    "GROUP_REL_A",
    "GROUP_REL_B",
    "GROUP_RING_P2",
    "GROUP_RING_P2_SIG",
    "NONTRIVIAL",
]
