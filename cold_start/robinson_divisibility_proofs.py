"""PEANO proofs of formula (2)'s components -- the paid leaves of the debts.

The Robinson product bridge (cold_start.divisibility_bridges) owes totality and
uniqueness. As ledgered, its target theory is empty, so those obligations are
not payable at all (a two-element model with total divisibility refutes
uniqueness); the payable shore is the composed one, where the divisibility atom
is read in PEANO as ``a|b := exists k, a*k=b`` and -- because uniqueness is
false at zero even there -- the domain is relativized to the positive numbers.
This module proves, through the trusted checker, the leaves of that composed
obligation that the current machinery can reach:

* coprimality of 1 with everything (both orders);
* the lcm graph at the unit and on the diagonal;
* the unit disjunct at (1,1,1), and what it forces of its arguments;
* both factors of a product divide whatever the product divides;
* the Chinese-remainder congruence identity behind Robinson's general disjunct:
  from ``mk = S(ax)`` and ``ml = S(by)``, ``abxy + (mk + ml) = S(mk*ml)`` --
  i.e. ``abxy = 1 (mod m)``, spelled without subtraction;
* one checked point of the totality graph: ``exists c, formula2(1, 1, c)``.

Nothing here discharges the two ledgered obligations; the report keeps them
open. These are foundations, each a genuine node of the obligation's proof DAG.
"""

from __future__ import annotations

from .divisibility import (
    ONE,
    divides_factor,
    divides_one,
    divides_product_right,
    divides_trans,
    one_divides,
    peano_divides,
)
from .divisibility_bridges import positive_peano
from .proof import (
    MP,
    Assume,
    Cong,
    ExistsIntro,
    ForallElim,
    ForallIntro,
    ImpIntro,
    Inst,
    Pf,
    Refl,
    Sym,
    Trans,
)
from .prop import And, and_intro, and_left, and_right, or_left
from .robinson_divisibility import coprime, lcm, robinson_product, unit_case
from .robinson_proofs import POLY_BUDGET, poly_kit
from .syntax import Eq, Formula, Implies, Var, exists
from .tactics import prove_eq
from .vocabulary import ZERO, S, add, mul

_a, _b, _c, _d, _x, _y = Var("a"), Var("b"), Var("c"), Var("d"), Var("x"), Var("y")
_m, _k, _l = Var("m"), Var("k"), Var("l")

COPRIME_ONE_LEFT: Formula = coprime(ONE, _a, via=peano_divides)
COPRIME_ONE_RIGHT: Formula = coprime(_a, ONE, via=peano_divides)
LCM_ONE_LEFT: Formula = lcm(ONE, _a, _a, via=peano_divides)
LCM_ONE_RIGHT: Formula = lcm(_a, ONE, _a, via=peano_divides)
LCM_SELF: Formula = lcm(_a, _a, _a, via=peano_divides)
UNIT_CASE_UNIT: Formula = unit_case(ONE, ONE, ONE, via=peano_divides)
UNIT_CASE_FORCES_UNIT_DIVISORS: Formula = Implies(
    unit_case(_a, _b, _c, via=peano_divides),
    And(
        peano_divides(_a, ONE),
        peano_divides(_b, ONE),
        peano_divides(_c, ONE),
    ),
)
UNIT_CASE_FORCES_UNITS: Formula = Implies(
    unit_case(_a, _b, _c, via=peano_divides),
    And(Eq(_a, ONE), Eq(_b, ONE), Eq(_c, ONE)),
)
POSITIVE_UNIT_CASE_UNIT: Formula = unit_case(
    ONE,
    ONE,
    ONE,
    via=peano_divides,
    domain=positive_peano,
)
POSITIVE_UNIT_CASE_FORCES_UNITS: Formula = Implies(
    unit_case(_a, _b, _c, via=peano_divides, domain=positive_peano),
    And(Eq(_a, ONE), Eq(_b, ONE), Eq(_c, ONE)),
)
POSITIVE_TOTALITY_AT_UNIT: Formula = exists(
    "c",
    "",
    And(
        positive_peano(_c),
        robinson_product(
            ONE,
            ONE,
            _c,
            via=peano_divides,
            domain=positive_peano,
        ),
    ),
)
PRODUCT_DIVIDES_BOTH: Formula = Implies(
    peano_divides(mul(_a, _b), _c),
    And(peano_divides(_a, _c), peano_divides(_b, _c)),
)
CRT_KEY_IDENTITY: Formula = Implies(
    Eq(mul(_m, _k), S(mul(_a, _x))),
    Implies(
        Eq(mul(_m, _l), S(mul(_b, _y))),
        Eq(
            add(mul(mul(_a, _b), mul(_x, _y)), add(mul(_m, _k), mul(_m, _l))),
            S(mul(mul(_m, _k), mul(_m, _l))),
        ),
    ),
)


def _coprime_one(unit_first: bool) -> Pf:
    """Shared spine of both unit-coprimality proofs.

    Given a common divisor ``d`` of 1 and ``a`` (in either order), ``d | 1``
    and ``1 | y`` chain through transitivity to ``d | y`` for arbitrary ``y``.
    """
    d_one, d_a = peano_divides(_d, ONE), peano_divides(_d, _a)
    if unit_first:
        packed = And(d_one, d_a)
        d_divides_one = and_left(d_one, d_a, Assume(packed))
    else:
        packed = And(d_a, d_one)
        d_divides_one = and_right(d_a, d_one, Assume(packed))
    through_one = Inst(Inst(Inst(divides_trans(), "a", _d), "b", ONE), "c", _y)
    d_divides_y = MP(MP(through_one, d_divides_one), Inst(one_divides(), "a", _y))
    body = ImpIntro(packed, ForallIntro("y", "", d_divides_y))
    return ForallIntro("d", "", body)


def coprime_one_left() -> Pf:
    """PEANO proves 1 is coprime to every ``a`` (unit on the left)."""
    return _coprime_one(unit_first=True)


def coprime_one_right() -> Pf:
    """PEANO proves every ``a`` is coprime to 1 (unit on the right)."""
    return _coprime_one(unit_first=False)


def _iff(left: Formula, right: Formula, forward: Pf, backward: Pf) -> Pf:
    """Pack the two implication proofs into the biconditional's conjunction."""
    return and_intro(
        Implies(left, right),
        Implies(right, left),
        ImpIntro(left, forward),
        ImpIntro(right, backward),
    )


def lcm_one_right() -> Pf:
    """PEANO proves the lcm graph at ``lcm(a, 1) = a``.

    A common multiple of ``a`` and 1 is just a multiple of ``a``: forward drops
    the trivial conjunct, backward restores it from ``1 | x``.
    """
    a_x, one_x = peano_divides(_a, _x), peano_divides(ONE, _x)
    both = And(a_x, one_x)
    forward = and_left(a_x, one_x, Assume(both))
    backward = and_intro(a_x, one_x, Assume(a_x), Inst(one_divides(), "a", _x))
    return ForallIntro("x", "", _iff(both, a_x, forward, backward))


def lcm_one_left() -> Pf:
    """PEANO proves the lcm graph at ``lcm(1, a) = a`` -- the mirror image."""
    a_x, one_x = peano_divides(_a, _x), peano_divides(ONE, _x)
    both = And(one_x, a_x)
    forward = and_right(one_x, a_x, Assume(both))
    backward = and_intro(one_x, a_x, Inst(one_divides(), "a", _x), Assume(a_x))
    return ForallIntro("x", "", _iff(both, a_x, forward, backward))


def lcm_self() -> Pf:
    """PEANO proves the lcm graph on the diagonal, ``lcm(a, a) = a``."""
    a_x = peano_divides(_a, _x)
    both = And(a_x, a_x)
    forward = and_left(a_x, a_x, Assume(both))
    backward = and_intro(a_x, a_x, Assume(a_x), Assume(a_x))
    return ForallIntro("x", "", _iff(both, a_x, forward, backward))


def unit_case_unit() -> Pf:
    """PEANO proves formula (2)'s unit disjunct at ``a = b = c = 1``."""
    one_x = peano_divides(ONE, _x)
    everywhere = Inst(one_divides(), "a", _x)
    packed = and_intro(
        one_x,
        And(one_x, one_x),
        everywhere,
        and_intro(one_x, one_x, everywhere, everywhere),
    )
    return ForallIntro("x", "", packed)


def unit_case_forces_unit_divisors() -> Pf:
    """PEANO proves the unit disjunct pins its arguments as divisors of 1.

    The disjunct says ``a``, ``b``, ``c`` divide everything; instantiating its
    universal at 1 is the whole proof. (Concluding ``a = b = c = 1`` from this
    still needs ``a | 1 -> a = 1``, an open leaf.)
    """
    hyp = unit_case(_a, _b, _c, via=peano_divides)
    return ImpIntro(hyp, ForallElim(Assume(hyp), ONE))


def _units_from_divisors(divisors: Pf) -> Pf:
    a_one_divisor = peano_divides(_a, ONE)
    b_one_divisor = peano_divides(_b, ONE)
    c_one_divisor = peano_divides(_c, ONE)
    tail = And(b_one_divisor, c_one_divisor)
    a_divides_one = and_left(a_one_divisor, tail, divisors)
    remaining = and_right(a_one_divisor, tail, divisors)
    b_divides_one = and_left(b_one_divisor, c_one_divisor, remaining)
    c_divides_one = and_right(b_one_divisor, c_one_divisor, remaining)

    a_is_one = MP(Inst(divides_one(), "a", _a), a_divides_one)
    b_is_one = MP(Inst(divides_one(), "a", _b), b_divides_one)
    c_is_one = MP(Inst(divides_one(), "a", _c), c_divides_one)
    return and_intro(
        Eq(_a, ONE),
        And(Eq(_b, ONE), Eq(_c, ONE)),
        a_is_one,
        and_intro(Eq(_b, ONE), Eq(_c, ONE), b_is_one, c_is_one),
    )


def unit_case_forces_units() -> Pf:
    """The first disjunct is possible only at ``a=b=c=1`` in PEANO."""
    hyp = unit_case(_a, _b, _c, via=peano_divides)
    divisors = MP(unit_case_forces_unit_divisors(), Assume(hyp))
    return ImpIntro(hyp, _units_from_divisors(divisors))


def _one_positive() -> Pf:
    return ExistsIntro(positive_peano(ONE), ZERO, Refl(ONE))


def positive_unit_case_unit() -> Pf:
    """The positive-relativized unit disjunct holds at ``(1,1,1)``."""
    one_x = peano_divides(ONE, _x)
    everywhere = Inst(one_divides(), "a", _x)
    packed = and_intro(
        one_x,
        And(one_x, one_x),
        everywhere,
        and_intro(one_x, one_x, everywhere, everywhere),
    )
    return ForallIntro("x", "", ImpIntro(positive_peano(_x), packed))


def positive_unit_case_forces_units() -> Pf:
    """The positive-relativized first disjunct also forces all values to 1."""
    hyp = unit_case(_a, _b, _c, via=peano_divides, domain=positive_peano)
    guarded_divisors = ForallElim(Assume(hyp), ONE)
    divisors = MP(guarded_divisors, _one_positive())
    return ImpIntro(hyp, _units_from_divisors(divisors))


def product_divides_both() -> Pf:
    """PEANO proves ``a*b | c`` passes to both factors: ``a | c`` and ``b | c``.

    Each factor divides the product (the factor laws), and transitivity carries
    it on to ``c``. This is the easy half of the coprime-lcm-product law that
    totality's hard leaf needs; the converse direction is Euclid-grade.
    """
    hyp = peano_divides(mul(_a, _b), _c)
    staged = Inst(Inst(Inst(divides_trans(), "a", Var("t!")), "b", mul(_a, _b)), "t!", _a)
    left = MP(MP(staged, divides_factor()), Assume(hyp))
    staged_right = Inst(
        Inst(Inst(divides_trans(), "a", Var("t!")), "b", mul(_a, _b)),
        "t!",
        _b,
    )
    right = MP(MP(staged_right, divides_product_right()), Assume(hyp))
    packed = and_intro(peano_divides(_a, _c), peano_divides(_b, _c), left, right)
    return ImpIntro(hyp, packed)


def crt_key_identity() -> Pf:
    """PEANO proves Robinson's congruence step, subtraction-free.

    From ``mk = S(ax)`` and ``ml = S(by)`` -- i.e. ``ax = -1`` and ``by = -1``
    modulo ``m`` -- her argument needs ``abxy = 1 (mod m)``. Over N that is the
    displayed identity ``abxy + (mk + ml) = S(mk * ml)``: substitute both
    hypotheses by congruence and the rest is the semiring identity
    ``abxy + (S(ax) + S(by)) = S(S(ax) * S(by))``, decided by the polynomial
    kit. What remains open toward totality is only the extraction of the
    quotient: ``m*p + q + 1 = m*q' + 1 -> m | q``-style reasoning.
    """
    h1 = Eq(mul(_m, _k), S(mul(_a, _x)))
    h2 = Eq(mul(_m, _l), S(mul(_b, _y)))
    abxy = mul(mul(_a, _b), mul(_x, _y))
    sax, sby = S(mul(_a, _x)), S(mul(_b, _y))

    pure = prove_eq(
        Eq(add(abxy, add(sax, sby)), S(mul(sax, sby))),
        poly_kit(),
        POLY_BUDGET,
    )
    fold_lhs = Cong("+", (Refl(abxy), Cong("+", (Assume(h1), Assume(h2)))))
    fold_rhs = Cong("S", (Cong("*", (Assume(h1), Assume(h2))),))
    chained = Trans(fold_lhs, Trans(pure, Sym(fold_rhs)))
    return ImpIntro(h1, ImpIntro(h2, chained))


def totality_witness_at_unit() -> Pf:
    """PEANO checks one point of the totality graph: ``exists c, (2)(1,1,c)``.

    The witness is 1 through the unit disjunct. A point, not the debt: the open
    totality obligation quantifies over all positive ``a`` and ``b``.
    """
    phi = robinson_product(ONE, ONE, ONE, via=peano_divides)
    assert type(phi) is Implies  # Or(unit, general) in the classical encoding
    packed = or_left(UNIT_CASE_UNIT, phi.con, unit_case_unit())
    claim = exists("c", "", robinson_product(ONE, ONE, _c, via=peano_divides))
    return ExistsIntro(claim, ONE, packed)


def positive_totality_witness_at_unit() -> Pf:
    """The positive composed graph contains the checked point ``1*1=1``."""
    phi = robinson_product(
        ONE,
        ONE,
        ONE,
        via=peano_divides,
        domain=positive_peano,
    )
    assert type(phi) is Implies
    graph = or_left(POSITIVE_UNIT_CASE_UNIT, phi.con, positive_unit_case_unit())
    packed = and_intro(positive_peano(ONE), phi, _one_positive(), graph)
    return ExistsIntro(POSITIVE_TOTALITY_AT_UNIT, ONE, packed)


__all__ = [
    "COPRIME_ONE_LEFT",
    "COPRIME_ONE_RIGHT",
    "CRT_KEY_IDENTITY",
    "LCM_ONE_LEFT",
    "LCM_ONE_RIGHT",
    "LCM_SELF",
    "PRODUCT_DIVIDES_BOTH",
    "POSITIVE_TOTALITY_AT_UNIT",
    "POSITIVE_UNIT_CASE_FORCES_UNITS",
    "POSITIVE_UNIT_CASE_UNIT",
    "UNIT_CASE_FORCES_UNIT_DIVISORS",
    "UNIT_CASE_FORCES_UNITS",
    "UNIT_CASE_UNIT",
    "coprime_one_left",
    "coprime_one_right",
    "crt_key_identity",
    "lcm_one_left",
    "lcm_one_right",
    "lcm_self",
    "product_divides_both",
    "positive_totality_witness_at_unit",
    "positive_unit_case_forces_units",
    "positive_unit_case_unit",
    "totality_witness_at_unit",
    "unit_case_forces_unit_divisors",
    "unit_case_forces_units",
    "unit_case_unit",
]
