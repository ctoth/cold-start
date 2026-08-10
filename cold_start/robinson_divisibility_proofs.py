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
* order/divisibility antisymmetry and functionality of the positive lcm graph;
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
    divides_refl,
    divides_trans,
    one_divides,
    peano_divides,
)
from .order import le, le_antisym
from .peano import MUL_SUCC_F, MUL_ZERO_F, positive_peano
from .presburger import ADD_SUCC_F, SUCC_NEQ_ZERO
from .presburger_proofs import add_comm, zero_or_succ
from .proof import (
    MP,
    Assume,
    Axiom,
    Cong,
    ExFalso,
    ExistsElim,
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
from .prop import And, and_intro, and_left, and_right, or_elim, or_left
from .robinson_divisibility import coprime, lcm, robinson_product, unit_case
from .robinson_proofs import POLY_BUDGET, poly_kit
from .syntax import Eq, Formula, Implies, Var, exists, instantiate
from .tactics import prove_eq, simultaneous_inst
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
PRODUCT_POSITIVE: Formula = Implies(
    positive_peano(_a),
    Implies(positive_peano(_b), positive_peano(mul(_a, _b))),
)
DIVIDES_LE_POSITIVE: Formula = Implies(
    positive_peano(_b),
    Implies(peano_divides(_a, _b), le(_a, _b)),
)
DIVIDES_ANTISYM_POSITIVE: Formula = Implies(
    positive_peano(_a),
    Implies(
        positive_peano(_b),
        Implies(
            peano_divides(_a, _b),
            Implies(peano_divides(_b, _a), Eq(_a, _b)),
        ),
    ),
)
LCM_UNIQUE_POSITIVE: Formula = Implies(
    positive_peano(_c),
    Implies(
        positive_peano(_d),
        Implies(
            lcm(_a, _b, _c, via=peano_divides, domain=positive_peano),
            Implies(
                lcm(_a, _b, _d, via=peano_divides, domain=positive_peano),
                Eq(_c, _d),
            ),
        ),
    ),
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
    universal at 1 is the whole proof. ``unit_case_forces_units`` then applies
    the checked ``a | 1 -> a = 1`` theorem to all three conjuncts.
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
    staged = simultaneous_inst(divides_trans(), {"a": _a, "b": mul(_a, _b)})
    left = MP(MP(staged, divides_factor()), Assume(hyp))
    staged_right = simultaneous_inst(divides_trans(), {"a": _b, "b": mul(_a, _b)})
    right = MP(MP(staged_right, divides_product_right()), Assume(hyp))
    packed = and_intro(peano_divides(_a, _c), peano_divides(_b, _c), left, right)
    return ImpIntro(hyp, packed)


def product_positive() -> Pf:
    """The ordinary product of two positive PEANO naturals is positive."""
    pos_a, pos_b = positive_peano(_a), positive_peano(_b)
    j, k = Var("j!"), Var("k!")
    a_succ, b_succ = instantiate(pos_a, j), instantiate(pos_b, k)

    expose_b = Cong("*", (Refl(_a), Assume(b_succ)))
    unfold = Inst(Inst(Axiom(MUL_SUCC_F), "x", _a), "y", k)
    expose_a = Cong("+", (Refl(mul(_a, k)), Assume(a_succ)))
    push = Inst(Inst(Axiom(ADD_SUCC_F), "x", mul(_a, k)), "y", j)
    product_is_succ = Trans(expose_b, Trans(unfold, Trans(expose_a, push)))
    packed = ExistsIntro(
        positive_peano(mul(_a, _b)),
        add(mul(_a, k), j),
        product_is_succ,
    )
    use_b = ExistsElim("k!", Assume(pos_b), packed)
    use_a = ExistsElim("j!", Assume(pos_a), use_b)
    return ImpIntro(pos_a, ImpIntro(pos_b, use_a))


def divides_le_positive() -> Pf:
    """A divisor of a positive natural is no larger than it."""
    pos = positive_peano(_b)
    dvd = peano_divides(_a, _b)
    goal = le(_a, _b)
    n, k, j = Var("n!"), Var("k!"), Var("j!")
    pos_n = instantiate(pos, n)
    dvd_k = instantiate(dvd, k)

    k_zero = Eq(k, ZERO)
    to_zero = Cong("*", (Refl(_a), Assume(k_zero)))
    times_zero = Inst(Axiom(MUL_ZERO_F), "x", _a)
    b_zero = Trans(Sym(Assume(dvd_k)), Trans(to_zero, times_zero))
    succ_zero = Trans(Sym(Assume(pos_n)), b_zero)
    contradiction = MP(Inst(Axiom(SUCC_NEQ_ZERO), "x", n), succ_zero)
    zero_arm = ImpIntro(k_zero, ExFalso(contradiction, goal))

    k_succ = Eq(k, S(j))
    to_succ = Cong("*", (Refl(_a), Assume(k_succ)))
    unfold = Inst(Inst(Axiom(MUL_SUCC_F), "x", _a), "y", j)
    commute = Inst(Inst(add_comm(), "x", mul(_a, j)), "y", _a)
    witnessed = Trans(
        Sym(commute),
        Trans(Sym(unfold), Trans(Sym(to_succ), Assume(dvd_k))),
    )
    packed = ExistsIntro(goal, mul(_a, j), witnessed)
    k_is_succ = exists("j", "", Eq(k, S(Var("j"))))
    succ_arm = ImpIntro(k_is_succ, ExistsElim("j!", Assume(k_is_succ), packed))

    split = Inst(zero_or_succ(), "n", k)
    cases = or_elim(k_zero, k_is_succ, goal, split, zero_arm, succ_arm)
    use_k = ExistsElim("k!", Assume(dvd), cases)
    use_n = ExistsElim("n!", Assume(pos), use_k)
    return ImpIntro(pos, ImpIntro(dvd, use_n))


def divides_antisym_positive() -> Pf:
    """Positive naturals that divide each other are equal."""
    pos_a, pos_b = positive_peano(_a), positive_peano(_b)
    a_b, b_a = peano_divides(_a, _b), peano_divides(_b, _a)
    ab_le = MP(MP(divides_le_positive(), Assume(pos_b)), Assume(a_b))
    ba_le = MP(
        MP(simultaneous_inst(divides_le_positive(), {"a": _b, "b": _a}), Assume(pos_a)),
        Assume(b_a),
    )
    antisym = simultaneous_inst(le_antisym(), {"a": _a, "b": _b})
    equal = MP(MP(antisym, ab_le), ba_le)
    return ImpIntro(pos_a, ImpIntro(pos_b, ImpIntro(a_b, ImpIntro(b_a, equal))))


def lcm_unique_positive() -> Pf:
    """The positive-relativized divisibility lcm graph is functional."""
    pos_c, pos_d = positive_peano(_c), positive_peano(_d)
    lc = lcm(_a, _b, _c, via=peano_divides, domain=positive_peano)
    ld = lcm(_a, _b, _d, via=peano_divides, domain=positive_peano)

    both_d = And(peano_divides(_a, _d), peano_divides(_b, _d))
    c_d, d_d = peano_divides(_c, _d), peano_divides(_d, _d)
    lc_at_d = MP(ForallElim(Assume(lc), _d), Assume(pos_d))
    ld_at_d = MP(ForallElim(Assume(ld), _d), Assume(pos_d))
    lc_forward = and_left(Implies(both_d, c_d), Implies(c_d, both_d), lc_at_d)
    ld_backward = and_right(Implies(both_d, d_d), Implies(d_d, both_d), ld_at_d)
    common_d = MP(ld_backward, Inst(divides_refl(), "a", _d))
    c_divides_d = MP(lc_forward, common_d)

    both_c = And(peano_divides(_a, _c), peano_divides(_b, _c))
    d_c, c_c = peano_divides(_d, _c), peano_divides(_c, _c)
    ld_at_c = MP(ForallElim(Assume(ld), _c), Assume(pos_c))
    lc_at_c = MP(ForallElim(Assume(lc), _c), Assume(pos_c))
    ld_forward = and_left(Implies(both_c, d_c), Implies(d_c, both_c), ld_at_c)
    lc_backward = and_right(Implies(both_c, c_c), Implies(c_c, both_c), lc_at_c)
    common_c = MP(lc_backward, Inst(divides_refl(), "a", _c))
    d_divides_c = MP(ld_forward, common_c)

    antisym = simultaneous_inst(divides_antisym_positive(), {"a": _c, "b": _d})
    equal = MP(
        MP(MP(MP(antisym, Assume(pos_c)), Assume(pos_d)), c_divides_d),
        d_divides_c,
    )
    return ImpIntro(pos_c, ImpIntro(pos_d, ImpIntro(lc, ImpIntro(ld, equal))))


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
    "DIVIDES_ANTISYM_POSITIVE",
    "DIVIDES_LE_POSITIVE",
    "LCM_ONE_LEFT",
    "LCM_ONE_RIGHT",
    "LCM_SELF",
    "LCM_UNIQUE_POSITIVE",
    "PRODUCT_DIVIDES_BOTH",
    "PRODUCT_POSITIVE",
    "POSITIVE_TOTALITY_AT_UNIT",
    "POSITIVE_UNIT_CASE_FORCES_UNITS",
    "POSITIVE_UNIT_CASE_UNIT",
    "UNIT_CASE_FORCES_UNIT_DIVISORS",
    "UNIT_CASE_FORCES_UNITS",
    "UNIT_CASE_UNIT",
    "coprime_one_left",
    "coprime_one_right",
    "crt_key_identity",
    "divides_antisym_positive",
    "divides_le_positive",
    "lcm_one_left",
    "lcm_one_right",
    "lcm_self",
    "lcm_unique_positive",
    "product_divides_both",
    "product_positive",
    "positive_totality_witness_at_unit",
    "positive_unit_case_forces_units",
    "positive_unit_case_unit",
    "totality_witness_at_unit",
    "unit_case_forces_unit_divisors",
    "unit_case_forces_units",
    "unit_case_unit",
]
