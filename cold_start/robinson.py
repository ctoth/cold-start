"""Robinson's (S, ·) arithmetic: Peano with addition ELIMINATED.

Julia Robinson (1949, "Definability and decision problems in arithmetic") showed
that addition is first-order definable from multiplication and successor:

    a + b = c   iff   S(a·c) · S(b·c) = S((c·c) · S(a·b))        (positive integers)

So Peano arithmetic can be axiomatized over the signature `(1, S, ·)` ALONE, with
`+` a *defined* relation -- the `bridge` below. This module exhibits that basis: the
`+`/`×` entanglement that makes arithmetic undecidable is here on display as one
identity, rather than buried inside the usual recursive axiom `x·S(y) = x·y + x`.
(Undecidability enters exactly when `S` is added to `·`: multiplication alone is
decidable -- its prime-permuting automorphisms hide addition -- and successor
rigidifies the integers, kills those automorphisms, and lets `+` be defined.)

We keep `cold_start.peano` (with `+` primitive and `×` recursive) as the practical
trusted base; Robinson herself (§2) called the eliminated-`+` axioms "complicated
and artificial". This is the thematic experiment, not the working theory.
Source, read in full: papers/Robinson_1949_DefinabilityArithmetic/.
"""

from __future__ import annotations

from .checker import Theory
from .peano import mul
from .presburger import ZERO, S
from .syntax import Eq, Formula, Implies, Not, Term, Var

ONE: Term = S(ZERO)  # the multiplicative identity, 1 = S(0)


def bridge(a: Term, b: Term, c: Term) -> Eq:
    """Robinson's identity defining `a + b = c` using only `S` and `·`:

        S(a·c) · S(b·c) = S((c·c) · S(a·b)).

    Multiplying out gives `(a+b)·c = c²`, true (for c > 0) iff `a + b = c`. There is
    no `+` symbol anywhere in it -- addition is read off of multiplication and
    successor."""
    return Eq(
        mul(S(mul(a, c)), S(mul(b, c))),
        S(mul(mul(c, c), S(mul(a, b)))),
    )


_a, _b, _c = Var("a"), Var("b"), Var("c")

# Peano's axioms with `+` eliminated -- the signature is (1, S, ·) only. A4'/A5'/A7'
# are exactly Robinson's §2 axioms, written through `bridge` so the structure shows:
# A5'/A7' are the recursion laws for `+` and `·` with their `+`s replaced by bridges.
SUCC_NEQ_ONE: Formula = Not(Eq(S(_a), ONE))  # A1:  S a ≠ 1
SUCC_INJ: Formula = Implies(Eq(S(_a), S(_b)), Eq(_a, _b))  # A2:  S a = S b → a = b
ADD_ONE: Formula = bridge(_a, ONE, S(_a))  # A4':  a + 1 = S a
ADD_SUCC: Formula = Implies(bridge(_a, _b, _c), bridge(_a, S(_b), S(_c)))  # A5': a+b=c → a+Sb=Sc
MUL_ONE: Formula = Eq(mul(_a, ONE), _a)  # A6:  a · 1 = a
MUL_SUCC: Formula = bridge(mul(_a, _b), _a, mul(_a, S(_b)))  # A7':  a·b + a = a·S b

ROBINSON_AXIOMS = frozenset({SUCC_NEQ_ONE, SUCC_INJ, ADD_ONE, ADD_SUCC, MUL_ONE, MUL_SUCC})

# Peano over (1, S, ·): the induction base is 1 (Robinson's positive integers), and
# the only function symbols are S and ·. `+` is not a primitive -- it is `bridge`.
ROBINSON_PEANO = Theory(axioms=ROBINSON_AXIOMS, zero=ONE, succ="S")
