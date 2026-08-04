"""Parity in PEANO: the 2-adic case split and Euclid's lemma at the prime 2.

Everything here is untrusted recipe-building; ``checker.check`` remains the
only judge. The four theorems are the smallest complete kit for reasoning
about doubling without subtraction or order:

    PARITY        every n is m*2 or S(m*2)
    EVEN_NE_ODD   a*2 = S(b*2) is absurd
    CANCEL_TWO    a*2 = b*2 -> a = b
    EUCLID_TWO    2 does not divide d -> d | x*2 -> d | x

``EUCLID_TWO`` is Euclid's lemma at 2 -- the first rung of the H1 debt in
``reports/formula2-bridge-debts.md``, and the whole toll of the Skolem bridge
(``cold_start.skolem``): closure of the powers of two under doubling is
exactly this lemma. Doubling is spelled ``t*2`` throughout (recursion on the
right argument is what the multiplication axioms unfold), and oddness is the
negative ``Not(2 | d)`` rather than a witness form: the parity split turns it
into ``d = S(j*2)`` where needed.
"""

from __future__ import annotations

from .divisibility import peano_divides
from .peano import MUL_SUCC_F, mul
from .peano_proofs import (
    DISTRIB_RIGHT,
    MUL_ASSOC,
    MUL_COMM,
    MUL_RULES,
    distrib_right,
    mul_assoc,
    mul_cancel_right_succ,
    mul_comm,
)
from .presburger import (
    ADD_SUCC_F,
    SUCC_INJ,
    SUCC_NEQ_ZERO,
    ZERO,
    S,
    add,
    induction,
)
from .presburger_proofs import (
    ADD_RULES,
    LEFT_IDENTITY,
    SUCC_ADD,
    left_identity,
    succ_add,
    zero_or_succ,
)
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
from .prop import Or, or_elim, or_left, or_right
from .syntax import Bottom, Eq, Formula, Implies, Not, Var, exists, forall
from .tactics import lemma_rule, normalize_equality, prove_eq

ONE = S(ZERO)
TWO = S(ONE)

_a, _b, _d, _n, _x = Var("a"), Var("b"), Var("d"), Var("n"), Var("x")


def double(t):
    """``t*2`` -- the canonical doubling, recursing where the axioms unfold."""
    return mul(t, TWO)


def _rules() -> tuple:
    """The rewrite kit that evaluates doublings: ``t*2`` normalizes to
    ``t + t`` (through ``t*1 + t`` and the left identity), and a successor
    escapes a sum's first argument through ``succ_add``."""
    return (
        *ADD_RULES,
        *MUL_RULES,
        lemma_rule(LEFT_IDENTITY, left_identity()),
        lemma_rule(SUCC_ADD, succ_add()),
    )


# ---------------------------------------------------------------------------
# The case split: every number is even or odd
# ---------------------------------------------------------------------------

PARITY: Formula = Or(
    exists("m", "", Eq(_n, double(Var("m")))),
    exists("m", "", Eq(_n, S(double(Var("m"))))),
)


def parity() -> Pf:
    """PEANO proves ``n = m*2 or n = S(m*2)`` -- induction on ``n``.

    The zero is even with half 0; a successor flips the disjunct, and the
    odd-to-even flip carries the half up by one (``S(S(m*2)) = S(m)*2``)."""
    even = exists("m", "", Eq(_n, double(Var("m"))))
    odd = exists("m", "", Eq(_n, S(double(Var("m")))))
    even_succ = exists("m", "", Eq(S(_n), double(Var("m"))))
    odd_succ = exists("m", "", Eq(S(_n), S(double(Var("m")))))
    goal_succ = Or(even_succ, odd_succ)

    even_zero = exists("m", "", Eq(ZERO, double(Var("m"))))
    odd_zero = exists("m", "", Eq(ZERO, S(double(Var("m")))))
    zero_even = ExistsIntro(even_zero, ZERO, prove_eq(Eq(ZERO, double(ZERO)), _rules()))
    base = or_left(even_zero, odd_zero, zero_even)

    m = Var("m!")
    # n even: S(n) is odd with the same half.
    n_even = Eq(_n, double(m))
    lift_odd = ExistsIntro(odd_succ, m, Cong("S", (Assume(n_even),)))
    even_arm = ImpIntro(
        even,
        ExistsElim("m!", Assume(even), or_right(even_succ, odd_succ, lift_odd)),
    )
    # n odd: S(n) is even with the half raised by one.
    n_odd = Eq(_n, S(double(m)))
    flip = prove_eq(Eq(S(S(double(m))), double(S(m))), _rules())
    lift_even = ExistsIntro(even_succ, S(m), Trans(Cong("S", (Assume(n_odd),)), flip))
    odd_arm = ImpIntro(
        odd,
        ExistsElim("m!", Assume(odd), or_left(even_succ, odd_succ, lift_even)),
    )

    step = ImpIntro(PARITY, or_elim(even, odd, goal_succ, Assume(PARITY), even_arm, odd_arm))
    return induction("n", PARITY, base, step)


# ---------------------------------------------------------------------------
# Separation: an even number is never an odd one
# ---------------------------------------------------------------------------

EVEN_NE_ODD: Formula = Not(Eq(double(_a), S(double(_b))))


def _all_a_even_ne_odd(b) -> Formula:
    """``forall a, not(a*2 = S(b*2))`` -- the induction predicate on ``b``."""
    a = Var("a")
    return forall("a", "", Not(Eq(double(a), S(double(b)))))


def _even_ne_odd_case_zero(hyp: Formula, offender) -> Pf:
    """From ``a = 0`` and ``hyp : a*2 = S(offender)``, absurdity: the left side
    collapses to zero, which is no successor."""
    a_zero = Eq(_a, ZERO)
    to_zero = Cong("*", (Assume(a_zero), Refl(TWO)))  # a*2 = 0*2
    succ_is_zero = Trans(
        Sym(Assume(hyp)),  # S(offender) = a*2
        Trans(to_zero, prove_eq(Eq(double(ZERO), ZERO), _rules())),
    )
    boom = MP(Inst(Axiom(SUCC_NEQ_ZERO), "x", offender), succ_is_zero)
    return ImpIntro(a_zero, ExFalso(boom, Bottom()))


def even_ne_odd() -> Pf:
    """PEANO proves ``not (a*2 = S(b*2))``: even never equals odd.

    Induction on ``b`` with the ``forall a`` predicate. At each rung, split
    ``a``: zero makes the even side zero against a successor, and ``a = S(m)``
    normalizes both doublings to sums, where two injectivity steps descend to
    the same equation one ``b`` lower -- the induction hypothesis's territory."""
    pred = _all_a_even_ne_odd(_b)

    def _step_down(hyp: Formula, rhs_head, use_smaller) -> Pf:
        """Common successor case: from ``a = S(m!)`` and ``hyp``, normalize,
        peel successors, and hand ``m! + m! = rhs`` to `use_smaller`."""
        m = Var("m!")
        a_succ = Eq(_a, S(m))
        to_succ = Cong("*", (Assume(a_succ), Refl(TWO)))  # a*2 = S(m!)*2
        shifted = Trans(Sym(to_succ), Assume(hyp))  # S(m!)*2 = S(rhs_head)
        normal = normalize_equality(Eq(double(S(m)), S(rhs_head)), shifted, _rules())
        ex_succ = exists("m", "", Eq(_a, S(Var("m"))))
        return ImpIntro(ex_succ, ExistsElim("m!", Assume(ex_succ), use_smaller(m, normal)))

    # base: forall a, not(a*2 = S(0*2)) -- descend to S(m!+m!) = S(0), whose
    # peeled form is a successor equal to zero.
    base_hyp = Eq(double(_a), S(double(ZERO)))

    def base_smaller(m, normal: Pf) -> Pf:
        # normal : S(S(m!+m!)) = S(0*2-normal-form) = S(0)
        peeled = MP(Inst(Inst(Axiom(SUCC_INJ), "x", S(add(m, m))), "y", ZERO), normal)
        boom = MP(Inst(Axiom(SUCC_NEQ_ZERO), "x", add(m, m)), peeled)
        return ExFalso(boom, Bottom())

    base_cases = or_elim(
        Eq(_a, ZERO),
        exists("m", "", Eq(_a, S(Var("m")))),
        Bottom(),
        Inst(zero_or_succ(), "n", _a),
        _even_ne_odd_case_zero(base_hyp, double(ZERO)),
        _step_down(base_hyp, double(ZERO), base_smaller),
    )
    base = ForallIntro("a", "", ImpIntro(base_hyp, base_cases))

    # step: assume forall a at b; conclude it at S(b).
    step_hyp = Eq(double(_a), S(double(S(_b))))

    def step_smaller(m, normal: Pf) -> Pf:
        # normal : S(S(m!+m!)) = S(S(S(b+b))) -- peel twice, then rebuild the
        # doubling shapes and refute via the induction hypothesis at m!.
        first = MP(
            Inst(Inst(Axiom(SUCC_INJ), "x", S(add(m, m))), "y", S(S(add(_b, _b)))),
            normal,
        )
        second = MP(
            Inst(Inst(Axiom(SUCC_INJ), "x", add(m, m)), "y", S(add(_b, _b))),
            first,
        )  # m! + m! = S(b + b)
        as_doubles = Trans(
            prove_eq(Eq(double(m), add(m, m)), _rules()),
            Trans(second, Sym(prove_eq(Eq(S(double(_b)), S(add(_b, _b))), _rules()))),
        )  # m!*2 = S(b*2)
        smaller = ForallElim(Assume(pred), m)  # not(m!*2 = S(b*2))
        return ExFalso(MP(smaller, as_doubles), Bottom())

    step_cases = or_elim(
        Eq(_a, ZERO),
        exists("m", "", Eq(_a, S(Var("m")))),
        Bottom(),
        Inst(zero_or_succ(), "n", _a),
        _even_ne_odd_case_zero(step_hyp, double(S(_b))),
        _step_down(step_hyp, double(S(_b)), step_smaller),
    )
    step = ImpIntro(pred, ForallIntro("a", "", ImpIntro(step_hyp, step_cases)))

    return ForallElim(induction("b", pred, base, step), _a)


# ---------------------------------------------------------------------------
# Cancellation and Euclid's lemma at 2
# ---------------------------------------------------------------------------

CANCEL_TWO: Formula = Implies(Eq(double(_a), double(_b)), Eq(_a, _b))


def cancel_two() -> Pf:
    """``a*2 = b*2 -> a = b``: positive cancellation at the multiplier 2."""
    specialized = Inst(mul_cancel_right_succ(), "z", ONE)
    return Inst(Inst(specialized, "x", _a), "y", _b)


EUCLID_TWO: Formula = Implies(
    Not(peano_divides(TWO, _d)),
    Implies(peano_divides(_d, double(_x)), peano_divides(_d, _x)),
)


def euclid_two() -> Pf:
    """Euclid's lemma at 2: an odd ``d`` dividing ``x*2`` divides ``x``.

    From the witness ``d*k = x*2``, split ``k`` by parity. An even ``k = m*2``
    re-associates to ``(d*m)*2 = x*2`` and cancels the 2, leaving the witness
    ``m``. An odd ``k`` forces a parity split on ``d`` itself: an even ``d``
    contradicts oddness outright, and an odd ``d`` makes ``d*k`` odd -- an odd
    number equal to the even ``x*2``, which `even_ne_odd` refutes. No order,
    no subtraction, no Bezout: parity alone carries the prime 2."""
    odd_d = Not(peano_divides(TWO, _d))
    dvd = peano_divides(_d, double(_x))
    goal = peano_divides(_d, _x)
    k, m, j = Var("k!"), Var("m!"), Var("j!")
    witness = Eq(mul(_d, k), double(_x))  # d*k! = x*2

    assoc = lemma_rule(MUL_ASSOC, mul_assoc())
    comm = lemma_rule(MUL_COMM, mul_comm())

    # k! even: (d*m!)*2 = d*(m!*2) = d*k! = x*2; cancel the common 2.
    k_even = Eq(k, double(m))
    doubled = Trans(
        assoc.instance({"x": _d, "y": m, "z": TWO}),  # (d*m!)*2 = d*(m!*2)
        Trans(Cong("*", (Refl(_d), Sym(Assume(k_even)))), Assume(witness)),
    )  # (d*m!)*2 = x*2
    halve = Inst(Inst(Inst(mul_cancel_right_succ(), "z", ONE), "x", mul(_d, m)), "y", _x)
    even_packed = ExistsIntro(goal, m, MP(halve, doubled))
    ex_k_even = exists("m", "", Eq(k, double(Var("m"))))
    k_even_arm = ImpIntro(ex_k_even, ExistsElim("m!", Assume(ex_k_even), even_packed))

    # k! odd: split d by parity.
    k_odd = Eq(k, S(double(m)))

    #   d even: d = j!*2 makes 2 a divisor of d, against oddness.
    d_even = Eq(_d, double(j))
    two_divides = ExistsIntro(
        peano_divides(TWO, _d),
        j,
        Trans(comm.instance({"x": TWO, "y": j}), Sym(Assume(d_even))),  # 2*j! = d
    )
    ex_d_even = exists("m", "", Eq(_d, double(Var("m"))))
    # d's parity eliminates through the eigenvariable j!: the enclosing k!-odd
    # case still holds its own hypothesis mentioning m!.
    d_even_arm = ImpIntro(
        ex_d_even,
        ExistsElim("j!", Assume(ex_d_even), ExFalso(MP(Assume(odd_d), two_divides), goal)),
    )

    #   d odd: d*k! = d*(m!*2) + d = (d*m!)*2 + S(j!*2) = S((d*m! + j!)*2),
    #   so x*2 = S((d*m! + j!)*2) -- even equals odd, absurd.
    d_odd = Eq(_d, S(double(j)))
    unfold = Trans(
        Cong("*", (Refl(_d), Assume(k_odd))),  # d*k! = d*S(m!*2)
        Inst(Inst(Axiom(MUL_SUCC_F), "x", _d), "y", double(m)),  # = d*(m!*2) + d
    )
    regroup = Cong(
        "+",
        (Sym(assoc.instance({"x": _d, "y": m, "z": TWO})), Assume(d_odd)),
    )  # d*(m!*2) + d = (d*m!)*2 + S(j!*2)
    push = Inst(Inst(Axiom(ADD_SUCC_F), "x", double(mul(_d, m))), "y", double(j))
    gather = Cong(
        "S",
        (
            Sym(
                lemma_rule(DISTRIB_RIGHT, distrib_right()).instance(
                    {"x": mul(_d, m), "y": j, "z": TWO}
                )
            ),
        ),
    )  # S((d*m!)*2 + j!*2) = S((d*m! + j!)*2)
    odd_total = Trans(unfold, Trans(regroup, Trans(push, gather)))
    even_is_odd = Trans(Sym(Assume(witness)), odd_total)  # x*2 = S((d*m!+j!)*2)
    refute = Inst(Inst(even_ne_odd(), "b", add(mul(_d, m), j)), "a", _x)
    ex_d_odd = exists("m", "", Eq(_d, S(double(Var("m")))))
    d_odd_arm = ImpIntro(
        ex_d_odd,
        ExistsElim("j!", Assume(ex_d_odd), ExFalso(MP(refute, even_is_odd), goal)),
    )

    d_cases = or_elim(
        ex_d_even,
        ex_d_odd,
        goal,
        Inst(parity(), "n", _d),
        d_even_arm,
        d_odd_arm,
    )
    ex_k_odd = exists("m", "", Eq(k, S(double(Var("m")))))
    k_odd_arm = ImpIntro(ex_k_odd, ExistsElim("m!", Assume(ex_k_odd), d_cases))

    k_cases = or_elim(
        ex_k_even,
        ex_k_odd,
        goal,
        Inst(parity(), "n", k),
        k_even_arm,
        k_odd_arm,
    )
    used = ExistsElim("k!", Assume(dvd), k_cases)
    return ImpIntro(odd_d, ImpIntro(dvd, used))


__all__ = [
    "CANCEL_TWO",
    "EUCLID_TWO",
    "EVEN_NE_ODD",
    "PARITY",
    "TWO",
    "cancel_two",
    "double",
    "euclid_two",
    "even_ne_odd",
    "parity",
]
