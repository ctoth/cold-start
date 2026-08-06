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
See tests/test_padoa.py for that automorphism, executably: a prime-swapping σ that
preserves `·`, breaks `+` and `S`, and leaves the bridge's `·`-only subterms fixed.

We keep `cold_start.peano` (with `+` primitive and `×` recursive) as the practical
trusted base; Robinson herself (§2) called the eliminated-`+` axioms "complicated
and artificial". This is the thematic experiment, not the working theory.
Source, read in full: papers/Robinson_1949_DefinabilityArithmetic/.
"""

from __future__ import annotations

from . import vocabulary as _v
from .syntax import Eq, Formula, Implies, Not, Term, Var
from .theory import Signature, Theory

ONE: Term = _v.ONE


def positive_numeral(value: int) -> Term:
    """The positive numeral vocabulary generated from primitive ``1`` and ``S``."""
    if type(value) is not int or value < 1:
        raise ValueError("Robinson numerals require a positive genuine int")
    term = ONE
    for _ in range(value - 1):
        term = _v.S(term)
    return term


def bridge(a: Term, b: Term, c: Term) -> Eq:
    """Robinson's identity defining `a + b = c` using only `S` and `·`:

        S(a·c) · S(b·c) = S((c·c) · S(a·b)).

    Multiplying out gives `(a+b)·c = c²`, true (for c > 0) iff `a + b = c`. There is
    no `+` symbol anywhere in it -- addition is read off of multiplication and
    successor."""
    return Eq(
        _v.mul(_v.S(_v.mul(a, c)), _v.S(_v.mul(b, c))),
        _v.S(_v.mul(_v.mul(c, c), _v.S(_v.mul(a, b)))),
    )


_a, _b, _c = Var("a"), Var("b"), Var("c")

# Peano's axioms with `+` eliminated -- the signature is (1, S, ·) only. A4'/A5'/A7'
# are exactly Robinson's §2 axioms, written through `bridge` so the structure shows:
# A5'/A7' are the recursion laws for `+` and `·` with their `+`s replaced by bridges.
SUCC_NEQ_ONE: Formula = Not(Eq(_v.S(_a), ONE))
SUCC_INJ: Formula = Implies(Eq(_v.S(_a), _v.S(_b)), Eq(_a, _b))
ADD_ONE: Formula = bridge(_a, ONE, _v.S(_a))
ADD_SUCC: Formula = Implies(bridge(_a, _b, _c), bridge(_a, _v.S(_b), _v.S(_c)))
MUL_ONE: Formula = Eq(_v.mul(_a, ONE), _a)
MUL_SUCC: Formula = bridge(_v.mul(_a, _b), _a, _v.mul(_a, _v.S(_b)))

ROBINSON_AXIOMS = frozenset({SUCC_NEQ_ONE, SUCC_INJ, ADD_ONE, ADD_SUCC, MUL_ONE, MUL_SUCC})

# Peano over (1, S, ·): the induction base is 1 (Robinson's positive integers), and
# the only function symbols are S and ·. `+` is not a primitive -- it is `bridge`.
ROBINSON_SIG = Signature(
    sorts=frozenset({""}),
    ranks=(("1", (), ""), ("S", ("",), ""), ("*", ("", ""), "")),
)
ROBINSON_PEANO = Theory(
    axioms=ROBINSON_AXIOMS,
    zero=ONE,
    succ="S",
    signature=ROBINSON_SIG,
)
