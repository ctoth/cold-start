"""Robinson's bridge, proved -- not model-checked -- in PEANO.

`cold_start.robinson` exhibits the (1, S, ·) axiomatisation and `tests/` checks
it against the standard model. That leaves the interesting half unsaid: is
Robinson's definition of addition *correct*? Here it is, as a theorem.

    PEANO |- S(a·(a+b)) · S(b·(a+b)) = S(((a+b)·(a+b)) · S(a·b))

Read with `+` back in, that is `(1 + ac)(1 + bc) = 1 + c²(1 + ab)` at `c := a+b`,
and at that instance it is a pure semiring identity -- both sides multiply out to
`ab(a+b)² + (a+b)² + 1`. So it needs no positivity and no case split: it is true
of every natural number, 0 included. (Positivity is what the CONVERSE needs --
that the bridge holding forces `a + b = c` -- and that is not proved here.)

The proof is the identity's own reason: `poly_kit()` normalises both sides to
one canonical polynomial. Distributivity expands the products, the recursion
laws float every successor to the outside, and the AC rules sort the sum of
monomials; then `prove_eq` joins the two sides at the shared normal form. Both
sides of the theorem above land on

    S(a·a + (a·b + (a·b + (b·b + (a·(a·(a·b)) + ...)))))

which is `1 + (a+b)² + ab(a+b)²` written in the canonical arrangement.

Robinson's §2 axioms A4' and A7' then come out as instances, with one rewrite
each to put the sum back in the shape the axiom is stated in. A5' does NOT come
out, and cannot -- see `A5_IS_NOT_A_PEANO_THEOREM` at the bottom.
"""

from __future__ import annotations

from .peano import MUL_SUCC_F, MUL_ZERO_F, mul
from .presburger import add
from .proof import Pf, Sym, Trans
from .proofs import (
    DISTRIB_LEFT,
    DISTRIB_RIGHT,
    MUL_ASSOC,
    MUL_COMM,
    MUL_LEFT_COMM,
    MUL_SUCC_LEFT,
    MUL_ZERO_LEFT,
    add_kit,
    distrib_left,
    distrib_right,
    mul_assoc,
    mul_comm,
    mul_left_comm,
    mul_succ_left,
    mul_zero_left,
)
from .robinson import ONE, bridge
from .syntax import Formula, Var
from .tactics import axiom_rule, lemma_rule, normalize, prove_eq

_a, _b = Var("a"), Var("b")

BRIDGE_SUM: Formula = bridge(_a, _b, add(_a, _b))
"""Robinson's bridge at `c := a + b` -- the claim that his definition of
addition is correct, stated in PEANO's own signature."""

POLY_BUDGET = 400
"""Rewrite steps the bridge needs; the identity is degree four in two
variables, so its normal form is eight monomials wide."""


def poly_kit() -> tuple:
    """Every law of `+` and `·` proved in `cold_start.proofs`, as one rewrite
    kit that normalises a term to a canonical polynomial.

    Three groups do three jobs. The recursion laws (both axioms and both of
    their mirror images) float every successor out to the front, so a term
    becomes `S^k` of a successor-free body. Distributivity, both ways, expands
    every product over a sum, so that body becomes a sum of monomials. The AC
    rules for `+` and for `·` -- associativity directed, commutativity and
    left-commutativity ordered -- right-nest and sort both the sum and each
    monomial. What is left is unique, so `prove_eq` over this kit decides any
    identity of the commutative semiring."""
    return (
        *add_kit(),
        axiom_rule(MUL_ZERO_F),
        axiom_rule(MUL_SUCC_F),
        lemma_rule(MUL_ZERO_LEFT, mul_zero_left()),
        lemma_rule(MUL_SUCC_LEFT, mul_succ_left()),
        lemma_rule(DISTRIB_LEFT, distrib_left()),
        lemma_rule(DISTRIB_RIGHT, distrib_right()),
        lemma_rule(MUL_ASSOC, mul_assoc()),
        lemma_rule(MUL_COMM, mul_comm(), ordered=True),
        lemma_rule(MUL_LEFT_COMM, mul_left_comm(), ordered=True),
    )


def bridge_theorem() -> Pf:
    """PEANO |- bridge(a, b, a + b): Robinson's definition of addition is
    correct. Both sides normalise to the same polynomial; nothing is assumed
    about `a` and `b`, so this is the theorem for every pair of naturals."""
    return prove_eq(BRIDGE_SUM, poly_kit(), POLY_BUDGET)


def _instance_at(sigma: dict, rewrite: tuple) -> Pf:
    """The bridge theorem at `sigma`, with `rewrite` applied to the sum that
    `c := a + b` leaves behind.

    Robinson states A4' and A7' with the sum already evaluated -- `a + 1` as
    `S(a)`, `a·b + a` as `a·S(b)` -- so an instance of the theorem is one
    congruence rewrite away from the axiom. `normalize` proves that rewrite on
    each side separately (`src = tgt`), and the two are pasted around the
    instance: from `L_src = R_src` and `L_src = L_tgt`, `R_src = R_tgt`, we get
    `L_tgt = R_tgt`, which is the axiom on the nose."""
    instance = lemma_rule(BRIDGE_SUM, bridge_theorem()).instance(sigma)
    source = bridge(sigma["a"], sigma["b"], add(sigma["a"], sigma["b"]))
    _, left = normalize(source.lhs, rewrite)
    _, right = normalize(source.rhs, rewrite)
    return Trans(Sym(left), Trans(instance, right))


def robinson_add_one() -> Pf:
    """A4' as a Peano theorem: PEANO |- bridge(a, 1, S(a)).

    The bridge theorem at `b := 1`, whose `a + 1` the two addition axioms turn
    into `S(a)` -- one unfold and one zero law, inside every position where the
    sum occurs."""
    return _instance_at({"a": _a, "b": ONE}, add_kit())


def robinson_mul_succ() -> Pf:
    """A7' as a Peano theorem: PEANO |- bridge(a·b, a, a·S(b)).

    The bridge theorem at `a := a·b, b := a` -- a SIMULTANEOUS substitution, so
    it goes through `Rule.instance` rather than a chain of `Inst`, which would
    substitute the second into what the first introduced. The sum it leaves,
    `a·b + a`, is folded back up by the multiplication axiom read right to
    left: exactly the step Robinson's A7' states."""
    return _instance_at({"a": mul(_a, _b), "b": _a}, (axiom_rule(MUL_SUCC_F).flipped,))


# --- why A5' is missing ----------------------------------------------------
# Robinson's A5' -- `bridge(a,b,c) -> bridge(a, S b, S c)`, the recursion law for
# addition -- has no proof here, and can have none. It is not that the tactics
# are too weak: the implication is FALSE in the standard model of PEANO, which by
# soundness settles it.
#
# The bridge says `(a + b)·c = c·c`, which pins `a + b = c` down only when `c` can
# be cancelled -- and 0 cannot. At `a = b = 1, c = 0` the hypothesis holds
# vacuously (`(1 + 0)·(1 + 0) = 1 = 1 + 0·(1 + 1)`) while the conclusion
# `bridge(1, 2, 1)` demands `2·3 = 1 + 1·3`, i.e. `6 = 4`. Robinson's §2 domain is
# the POSITIVE integers, where `c > 0` makes the cancellation available; PEANO's
# is the naturals, where it does not. That is precisely the work positivity does
# in her definition -- A4' and A7' transfer to PEANO without it, A5' does not --
# and `tests/test_robinson.py` pins the counterexample.
