"""PEANO-checked leaves of Robinson's formula (2) definedness debts.

Each theorem here is a component of the totality/uniqueness obligations of the
331-node multiplication graph, taken on the PEANO shore (| read as the
existential graph). They are leaves, not the debts themselves: the report in
reports/formula2-bridge-debts.md places each one in the decomposition.
"""

from __future__ import annotations

from cold_start.checker import check
from cold_start.divisibility import ONE, peano_divides
from cold_start.peano import PEANO
from cold_start.prop import And, Or
from cold_start.robinson_divisibility import lcm, robinson_product, unit_case
from cold_start.robinson_divisibility_proofs import (
    COPRIME_ONE_LEFT,
    COPRIME_ONE_RIGHT,
    CRT_KEY_IDENTITY,
    LCM_ONE_LEFT,
    LCM_ONE_RIGHT,
    LCM_SELF,
    PRODUCT_DIVIDES_BOTH,
    UNIT_CASE_FORCES_UNIT_DIVISORS,
    UNIT_CASE_UNIT,
    coprime_one_left,
    coprime_one_right,
    crt_key_identity,
    lcm_one_left,
    lcm_one_right,
    lcm_self,
    product_divides_both,
    totality_witness_at_unit,
    unit_case_forces_unit_divisors,
    unit_case_unit,
)
from cold_start.syntax import Eq, Implies, Var, exists
from cold_start.vocabulary import S, add, mul

_a, _b, _c = Var("a"), Var("b"), Var("c")


def _checked(build, claim):
    seq = check(build(), PEANO)
    assert seq.hyps == frozenset()
    assert seq.concl == claim
    return seq


def test_one_is_coprime_to_everything_on_both_sides():
    _checked(coprime_one_left, COPRIME_ONE_LEFT)
    _checked(coprime_one_right, COPRIME_ONE_RIGHT)


def test_lcm_graph_holds_at_the_unit_and_on_the_diagonal():
    _checked(lcm_one_left, LCM_ONE_LEFT)
    _checked(lcm_one_right, LCM_ONE_RIGHT)
    _checked(lcm_self, LCM_SELF)
    assert LCM_ONE_RIGHT == lcm(_a, ONE, _a, via=peano_divides)
    assert LCM_ONE_LEFT == lcm(ONE, _a, _a, via=peano_divides)
    assert LCM_SELF == lcm(_a, _a, _a, via=peano_divides)


def test_the_unit_disjunct_holds_at_one_and_forces_unit_divisors():
    _checked(unit_case_unit, UNIT_CASE_UNIT)
    _checked(unit_case_forces_unit_divisors, UNIT_CASE_FORCES_UNIT_DIVISORS)
    assert UNIT_CASE_UNIT == unit_case(ONE, ONE, ONE, via=peano_divides)
    assert UNIT_CASE_FORCES_UNIT_DIVISORS == Implies(
        unit_case(_a, _b, _c, via=peano_divides),
        And(
            peano_divides(_a, ONE),
            peano_divides(_b, ONE),
            peano_divides(_c, ONE),
        ),
    )


def test_a_product_divisor_yields_both_factor_divisors():
    _checked(product_divides_both, PRODUCT_DIVIDES_BOTH)
    assert PRODUCT_DIVIDES_BOTH == Implies(
        peano_divides(mul(_a, _b), _c),
        And(peano_divides(_a, _c), peano_divides(_b, _c)),
    )


def test_the_chinese_remainder_congruence_identity_is_a_peano_theorem():
    m, k, ell, x, y = Var("m"), Var("k"), Var("l"), Var("x"), Var("y")
    _checked(crt_key_identity, CRT_KEY_IDENTITY)
    assert CRT_KEY_IDENTITY == Implies(
        Eq(mul(m, k), S(mul(_a, x))),
        Implies(
            Eq(mul(m, ell), S(mul(_b, y))),
            Eq(
                add(mul(mul(_a, _b), mul(x, y)), add(mul(m, k), mul(m, ell))),
                S(mul(mul(m, k), mul(m, ell))),
            ),
        ),
    )


def test_the_totality_graph_has_a_checked_point_at_one_times_one():
    seq = check(totality_witness_at_unit(), PEANO)
    phi_c = robinson_product(ONE, ONE, Var("c"), via=peano_divides)

    assert seq.hyps == frozenset()
    assert seq.concl == exists("c", "", phi_c)
    # the witnessed disjunct really is formula (2)'s Or shape
    phi_one = robinson_product(ONE, ONE, ONE, via=peano_divides)
    assert type(phi_one) is Implies
    assert phi_one == Or(UNIT_CASE_UNIT, phi_one.con)
