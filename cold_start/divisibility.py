"""Divisibility foundations proved in PEANO.

The atomic ``|`` relation is the vocabulary of Robinson's Theorem 1.2.  Here we
give its ordinary multiplication interpretation, ``a | b := exists k, a*k=b``,
and derive the first reusable laws as proof terms.  This module is untrusted:
the returned recipes become theorems only when ``checker.check`` accepts them in
PEANO.
"""

from __future__ import annotations

from .peano import MUL_SUCC_F, MUL_ZERO_F
from .peano_proofs import (
    DISTRIB_LEFT,
    MUL_ASSOC,
    MUL_COMM,
    MUL_RULES,
    MUL_ZERO_LEFT,
    distrib_left,
    mul_assoc,
    mul_comm,
    mul_zero_left,
)
from .presburger import ADD_SUCC_F, ADD_ZERO_F, SUCC_INJ, SUCC_NEQ_ZERO, induction
from .presburger_proofs import (
    ADD_ASSOC,
    ADD_RULES,
    LEFT_IDENTITY,
    add_assoc,
    add_cancel_right,
    add_eq_zero,
    left_identity,
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
    ImpIntro,
    Inst,
    Pf,
    Refl,
    Sym,
    Trans,
)
from .prop import and_left, and_right, or_elim
from .syntax import Eq, Formula, Implies, Term, Var, exists, instantiate
from .tactics import fresh_name, lemma_rule, prove_eq
from .vocabulary import ZERO, S, add, mul

ONE = S(ZERO)


def peano_divides(a: Term, b: Term) -> Formula:
    """``a | b`` interpreted in PEANO as ``exists k, a*k=b``."""
    witness_name = fresh_name("k", a, b)
    witness = Var(witness_name)
    return exists(witness_name, "", Eq(mul(a, witness), b))


_a, _b, _c = Var("a"), Var("b"), Var("c")

DIVIDES_REFL: Formula = peano_divides(_a, _a)
DIVIDES_FACTOR: Formula = peano_divides(_a, mul(_a, _b))
DIVIDES_PRODUCT_RIGHT: Formula = peano_divides(_b, mul(_a, _b))
DIVIDES_ZERO: Formula = peano_divides(_a, ZERO)
ONE_DIVIDES: Formula = peano_divides(ONE, _a)
DIVIDES_TRANS: Formula = Implies(
    peano_divides(_a, _b),
    Implies(peano_divides(_b, _c), peano_divides(_a, _c)),
)
DIVIDES_PRODUCT: Formula = Implies(
    peano_divides(_a, _b),
    peano_divides(_a, mul(_b, _c)),
)
DIVIDES_ADD: Formula = Implies(
    peano_divides(_a, _b),
    Implies(peano_divides(_a, _c), peano_divides(_a, add(_b, _c))),
)
DIVIDES_MUL_LEFT: Formula = Implies(
    peano_divides(_a, _b),
    peano_divides(mul(_c, _a), mul(_c, _b)),
)
_k = Var("k")
DIVIDES_STEP: Formula = Implies(
    Eq(mul(_a, _k), add(_b, _a)),
    peano_divides(_a, _b),
)
DIVIDES_ADD_CANCEL: Formula = Implies(
    peano_divides(_a, add(_b, mul(_a, _c))),
    peano_divides(_a, _b),
)
DIVIDES_ONE: Formula = Implies(peano_divides(_a, ONE), Eq(_a, ONE))


def _mul_one(term: Term) -> Pf:
    return prove_eq(
        Eq(mul(term, ONE), term),
        (*ADD_RULES, *MUL_RULES, lemma_rule(LEFT_IDENTITY, left_identity())),
    )


def divides_refl() -> Pf:
    """PEANO proves ``a | a``; the witness is 1."""
    return ExistsIntro(DIVIDES_REFL, ONE, _mul_one(_a))


def divides_factor() -> Pf:
    """PEANO proves ``a | a*b``; the witness is ``b``."""
    return ExistsIntro(DIVIDES_FACTOR, _b, Refl(mul(_a, _b)))


def divides_product_right() -> Pf:
    """PEANO proves ``b | a*b`` by commuting the product; witness ``a``."""
    commute = lemma_rule(MUL_COMM, mul_comm()).instance({"x": _b, "y": _a})
    return ExistsIntro(DIVIDES_PRODUCT_RIGHT, _a, commute)


def divides_zero() -> Pf:
    """PEANO proves ``a | 0``; the witness is 0."""
    zero_product = prove_eq(Eq(mul(_a, ZERO), ZERO), MUL_RULES)
    return ExistsIntro(DIVIDES_ZERO, ZERO, zero_product)


def one_divides() -> Pf:
    """PEANO proves ``1 | a``; the witness is ``a``."""
    one_times_a = Trans(
        lemma_rule(MUL_COMM, mul_comm()).instance({"x": ONE, "y": _a}),
        _mul_one(_a),
    )
    return ExistsIntro(ONE_DIVIDES, _a, one_times_a)


def divides_trans() -> Pf:
    """PEANO proves transitivity of divisibility.

    From witnesses ``a*k=b`` and ``b*l=c``, associativity certifies
    ``a*(k*l)=(a*k)*l=b*l=c``; ``k*l`` is the composite witness.
    """
    ab, bc, ac = peano_divides(_a, _b), peano_divides(_b, _c), peano_divides(_a, _c)
    k, ell = Var("k!"), Var("l!")
    ab_instance = instantiate(ab, k)
    bc_instance = instantiate(bc, ell)

    assoc = lemma_rule(MUL_ASSOC, mul_assoc()).instance({"x": _a, "y": k, "z": ell})
    multiply_ab = Cong("*", (Assume(ab_instance), Refl(ell)))
    product_eq_c = Trans(Sym(assoc), Trans(multiply_ab, Assume(bc_instance)))
    packed = ExistsIntro(ac, mul(k, ell), product_eq_c)

    use_bc = ExistsElim("l!", Assume(bc), packed)
    use_ab = ExistsElim("k!", Assume(ab), use_bc)
    return ImpIntro(ab, ImpIntro(bc, use_ab))


def divides_product() -> Pf:
    """PEANO proves ``a|b -> a|b*c`` by transitivity through ``b|b*c``."""
    ab = peano_divides(_a, _b)
    transitive = Inst(
        Inst(Inst(divides_trans(), "a", _a), "b", _b),
        "c",
        mul(_b, _c),
    )
    # Substitute the original ``b`` first: replacing ``a`` by the term named
    # ``b`` and then substituting ``b`` would also rewrite that replacement.
    factor = Inst(Inst(divides_factor(), "b", _c), "a", _b)
    return ImpIntro(ab, MP(MP(transitive, Assume(ab)), factor))


def divides_add() -> Pf:
    """PEANO proves ``a|b -> a|c -> a|(b+c)``.

    From witnesses ``a*k=b`` and ``a*l=c``, distributivity certifies
    ``a*(k+l) = a*k + a*l = b + c``; ``k+l`` is the composite witness.
    """
    ab, ac = peano_divides(_a, _b), peano_divides(_a, _c)
    goal = peano_divides(_a, add(_b, _c))
    k, ell = Var("k!"), Var("l!")
    ab_instance = instantiate(ab, k)
    ac_instance = instantiate(ac, ell)

    distribute = lemma_rule(DISTRIB_LEFT, distrib_left()).instance({"x": _a, "y": k, "z": ell})
    sum_of_witnesses = Cong("+", (Assume(ab_instance), Assume(ac_instance)))
    product_eq_sum = Trans(distribute, sum_of_witnesses)
    packed = ExistsIntro(goal, add(k, ell), product_eq_sum)

    use_ac = ExistsElim("l!", Assume(ac), packed)
    use_ab = ExistsElim("k!", Assume(ab), use_ac)
    return ImpIntro(ab, ImpIntro(ac, use_ab))


def divides_mul_left() -> Pf:
    """PEANO proves ``a|b -> c*a|c*b``: a common left factor is harmless.

    From the witness ``a*k=b``, associativity certifies
    ``(c*a)*k = c*(a*k) = c*b``; the witness survives unchanged.
    """
    ab = peano_divides(_a, _b)
    goal = peano_divides(mul(_c, _a), mul(_c, _b))
    k = Var("k!")
    ab_instance = instantiate(ab, k)

    assoc = lemma_rule(MUL_ASSOC, mul_assoc()).instance({"x": _c, "y": _a, "z": k})
    scale = Cong("*", (Refl(_c), Assume(ab_instance)))
    packed = ExistsIntro(goal, k, Trans(assoc, scale))

    return ImpIntro(ab, ExistsElim("k!", Assume(ab), packed))


def divides_step() -> Pf:
    """PEANO proves ``a*k = b + a -> a | b``: peel one copy of the divisor.

    By cases on ``k``. At ``k = 0`` the hypothesis makes the sum zero, so
    ``a = b = 0`` and the witness is 0. At ``k = S(m)`` the recursion law
    exposes ``a*m + a = b + a``; additive cancellation leaves the witness
    ``m``. This is the subtraction step ``(b + a) - a`` spelled without
    subtraction, and the engine of ``divides_add_cancel`` below.
    """
    hyp = Eq(mul(_a, _k), add(_b, _a))
    goal = peano_divides(_a, _b)
    k_zero = Eq(_k, ZERO)
    ex_succ = exists("m", "", Eq(_k, S(Var("m"))))

    # k = 0: the sum collapses to zero, so both summands do.
    to_zero = Cong("*", (Refl(_a), Assume(k_zero)))  # a*k = a*0
    times_zero = Inst(Axiom(MUL_ZERO_F), "x", _a)  # a*0 = 0
    sum_is_zero = Sym(Trans(Trans(Sym(times_zero), Sym(to_zero)), Assume(hyp)))  # b + a = 0
    split = MP(Inst(Inst(add_eq_zero(), "x", _b), "y", _a), sum_is_zero)
    b_zero = and_left(Eq(_b, ZERO), Eq(_a, ZERO), split)
    zero_witness = Trans(times_zero, Sym(b_zero))  # a*0 = b
    zero_arm = ImpIntro(k_zero, ExistsIntro(goal, ZERO, zero_witness))

    # k = S(m!): unfold one recursion rung and cancel the common suffix.
    m = Var("m!")
    k_succ = Eq(_k, S(m))
    to_succ = Cong("*", (Refl(_a), Assume(k_succ)))  # a*k = a*S(m!)
    unfold = Inst(Inst(Axiom(MUL_SUCC_F), "x", _a), "y", m)  # a*S(m!) = a*m! + a
    shifted = Trans(Trans(Sym(unfold), Sym(to_succ)), Assume(hyp))  # a*m! + a = b + a
    cancel = Inst(Inst(Inst(add_cancel_right(), "z", _a), "x", mul(_a, m)), "y", _b)
    smaller_witness = MP(cancel, shifted)  # a*m! = b
    packed = ExistsIntro(goal, m, smaller_witness)
    succ_arm = ImpIntro(ex_succ, ExistsElim("m!", Assume(ex_succ), packed))

    cases = or_elim(k_zero, ex_succ, goal, Inst(zero_or_succ(), "n", _k), zero_arm, succ_arm)
    return ImpIntro(hyp, cases)


def divides_add_cancel() -> Pf:
    """PEANO proves ``a | b + a*c -> a | b``: subtract a multiple of ``a``.

    Induction on ``c``. The base simplifies ``b + a*0`` to ``b``; the step
    rearranges ``b + a*S(c)`` into ``(b + a*c) + a``, peels the trailing ``a``
    with ``divides_step``, and hands the rest to the induction hypothesis.
    Together with ``divides_add`` this makes divisibility a congruence for the
    additive structure -- the extraction step Robinson's Chinese-remainder
    argument needs after the ``crt_key_identity`` congruence.
    """
    pred = DIVIDES_ADD_CANCEL
    goal = peano_divides(_a, _b)
    k = Var("k!")

    base_hyp = peano_divides(_a, add(_b, mul(_a, ZERO)))
    base_instance = instantiate(base_hyp, k)
    simplify = prove_eq(Eq(add(_b, mul(_a, ZERO)), _b), (*ADD_RULES, *MUL_RULES))
    base_witness = Trans(Assume(base_instance), simplify)  # a*k! = b
    base_packed = ExistsIntro(goal, k, base_witness)
    base = ImpIntro(base_hyp, ExistsElim("k!", Assume(base_hyp), base_packed))

    step_hyp = peano_divides(_a, add(_b, mul(_a, S(_c))))
    step_instance = instantiate(step_hyp, k)
    rearrange = prove_eq(
        Eq(add(_b, mul(_a, S(_c))), add(add(_b, mul(_a, _c)), _a)),
        (*ADD_RULES, *MUL_RULES, lemma_rule(ADD_ASSOC, add_assoc())),
    )
    shifted = Trans(Assume(step_instance), rearrange)  # a*k! = (b + a*c) + a
    peel = Inst(Inst(divides_step(), "b", add(_b, mul(_a, _c))), "k", k)
    smaller = MP(peel, shifted)  # a | b + a*c
    from_ih = MP(Assume(pred), smaller)  # a | b
    step_body = ExistsElim("k!", Assume(step_hyp), from_ih)
    step = ImpIntro(pred, ImpIntro(step_hyp, step_body))

    return induction("c", pred, base, step)


def divides_one() -> Pf:
    """PEANO proves ``a | 1 -> a = 1``: units are trivial.

    From the witness ``a*k = 1``, case on ``k``: zero makes the product zero,
    never ``S(0)``. At ``k = S(j)``, case on ``a``: zero zeroes the product
    again; at ``a = S(m)`` the recursion laws expose ``S(a*j + m) = S(0)``,
    injectivity peels it, and a zero sum forces ``m = 0`` -- so ``a = S(0)``.
    The unit-divisor constraint of formula (2)'s first disjunct becomes
    ``a = b = c = 1`` through this lemma.
    """
    hyp = peano_divides(_a, ONE)
    goal = Eq(_a, ONE)
    k, j, m = Var("k!"), Var("j!"), Var("m!")
    witness = instantiate(hyp, k)  # a*k! = S(0)

    # k! = 0: the product is zero, contradicting S(0).
    k_zero = Eq(k, ZERO)
    to_zero = Cong("*", (Refl(_a), Assume(k_zero)))  # a*k! = a*0
    times_zero = Inst(Axiom(MUL_ZERO_F), "x", _a)  # a*0 = 0
    zero_is_one = Trans(Trans(Sym(times_zero), Sym(to_zero)), Assume(witness))  # 0 = S(0)
    k_zero_arm = ImpIntro(
        k_zero,
        ExFalso(MP(Inst(Axiom(SUCC_NEQ_ZERO), "x", ZERO), Sym(zero_is_one)), goal),
    )

    # k! = S(j!): one recursion rung leaves  a*j! + a = S(0).
    k_succ = Eq(k, S(j))
    to_succ = Cong("*", (Refl(_a), Assume(k_succ)))  # a*k! = a*S(j!)
    unfold = Inst(Inst(Axiom(MUL_SUCC_F), "x", _a), "y", j)  # a*S(j!) = a*j! + a
    sum_is_one = Trans(Sym(unfold), Trans(Sym(to_succ), Assume(witness)))  # a*j! + a = S(0)

    #   a = 0: the sum collapses to zero, contradicting S(0) again.
    a_zero = Eq(_a, ZERO)
    collapse = Cong("+", (Cong("*", (Assume(a_zero), Refl(j))), Assume(a_zero)))
    zero_sum = Trans(
        Cong("+", (lemma_rule(MUL_ZERO_LEFT, mul_zero_left()).instance({"n": j}), Refl(ZERO))),
        Inst(Axiom(ADD_ZERO_F), "x", ZERO),
    )  # 0*j! + 0 = 0
    zero_is_one_again = Trans(Trans(Sym(zero_sum), Sym(collapse)), sum_is_one)  # 0 = S(0)
    a_zero_arm = ImpIntro(
        a_zero,
        ExFalso(MP(Inst(Axiom(SUCC_NEQ_ZERO), "x", ZERO), Sym(zero_is_one_again)), goal),
    )

    #   a = S(m!): injectivity and the zero-sum split force m! = 0.
    a_succ = Eq(_a, S(m))
    shift = Cong("+", (Refl(mul(_a, j)), Assume(a_succ)))  # a*j! + a = a*j! + S(m!)
    push = Inst(Inst(Axiom(ADD_SUCC_F), "x", mul(_a, j)), "y", m)  # a*j! + S(m!) = S(a*j! + m!)
    succs_equal = Trans(Sym(push), Trans(Sym(shift), sum_is_one))  # S(a*j! + m!) = S(0)
    inject = Inst(Inst(Axiom(SUCC_INJ), "x", add(mul(_a, j), m)), "y", ZERO)
    split = MP(Inst(Inst(add_eq_zero(), "x", mul(_a, j)), "y", m), MP(inject, succs_equal))
    m_zero = and_right(Eq(mul(_a, j), ZERO), Eq(m, ZERO), split)  # m! = 0
    a_is_one = Trans(Assume(a_succ), Cong("S", (m_zero,)))  # a = S(0)
    ex_succ_a = exists("m", "", Eq(_a, S(Var("m"))))
    a_succ_arm = ImpIntro(ex_succ_a, ExistsElim("m!", Assume(ex_succ_a), a_is_one))

    by_a = or_elim(
        a_zero,
        ex_succ_a,
        goal,
        Inst(zero_or_succ(), "n", _a),
        a_zero_arm,
        a_succ_arm,
    )
    ex_succ_k = exists("m", "", Eq(k, S(Var("m"))))
    k_succ_arm = ImpIntro(ex_succ_k, ExistsElim("j!", Assume(ex_succ_k), by_a))

    by_k = or_elim(
        k_zero,
        ex_succ_k,
        goal,
        Inst(zero_or_succ(), "n", k),
        k_zero_arm,
        k_succ_arm,
    )
    return ImpIntro(hyp, ExistsElim("k!", Assume(hyp), by_k))


__all__ = [
    "DIVIDES_ADD",
    "DIVIDES_ADD_CANCEL",
    "DIVIDES_STEP",
    "DIVIDES_FACTOR",
    "DIVIDES_MUL_LEFT",
    "DIVIDES_ONE",
    "DIVIDES_PRODUCT",
    "DIVIDES_PRODUCT_RIGHT",
    "DIVIDES_REFL",
    "DIVIDES_TRANS",
    "DIVIDES_ZERO",
    "ONE_DIVIDES",
    "divides_add",
    "divides_add_cancel",
    "divides_factor",
    "divides_mul_left",
    "divides_one",
    "divides_step",
    "divides_product",
    "divides_product_right",
    "divides_refl",
    "divides_trans",
    "divides_zero",
    "one_divides",
    "peano_divides",
]
