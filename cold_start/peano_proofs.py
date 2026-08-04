"""Proof builders whose complete checking contract requires Peano arithmetic."""

from __future__ import annotations

from .peano import MUL_SUCC_F, MUL_ZERO_F, mul
from .presburger import SUCC_NEQ_ZERO, ZERO, S, add, induction, numeral
from .presburger_proofs import ADD_RULES, add_cancel_right, add_kit, add_proof
from .proof import (
    MP,
    Assume,
    Axiom,
    Cong,
    ExFalso,
    ForallElim,
    ForallIntro,
    ImpIntro,
    Inst,
    Pf,
    Refl,
    Sym,
    Trans,
)
from .syntax import Eq, Formula, Implies, Term, Var, forall
from .tactics import axiom_rule, by_induction, lemma_rule, normalize_equality

_x, _y, _z, _n = Var("x"), Var("y"), Var("z"), Var("n")


def mul_proof(a: int, b: int) -> Pf:
    """Proof term for  numeral(a) * numeral(b) = numeral(a*b).

    Climbs the second argument via the multiplication axioms, reusing
    `add_proof` to collapse the trailing addition at each rung. A Peano theorem
    -- it cites the multiplication axioms, so it does not check under
    Presburger. Iterative, for the reason given on `add_proof`.
    """
    big_a = numeral(a)
    pf: Pf = Inst(Axiom(MUL_ZERO_F), "x", big_a)  # a * 0 = 0
    for k in range(1, b + 1):
        #  a * S(k-1) = (a * (k-1)) + a
        succ_step = Inst(Inst(Axiom(MUL_SUCC_F), "x", big_a), "y", numeral(k - 1))
        #  (a * (k-1)) + a = numeral(a*(k-1)) + a     -- by the product so far
        fold_product = Cong("+", (pf, Refl(big_a)))
        #  numeral(a*(k-1)) + a = numeral(a*(k-1) + a) = numeral(a*k)
        collapse_sum = add_proof(a * (k - 1), a)
        pf = Trans(succ_step, Trans(fold_product, collapse_sum))
    return pf


# ---------------------------------------------------------------------------
# Multiplication: the same ladder, one rung higher
# ---------------------------------------------------------------------------
# Peano's two multiplication axioms recurse on the SECOND argument, exactly as
# addition's do, so every law here follows the same shape: peel a successor,
# rewrite by the induction hypothesis, and let the addition kit reconcile what
# is left. Each lemma joins the rule set of the next.

MUL_ZERO_LEFT: Formula = Eq(mul(ZERO, _n), ZERO)  # 0 * n = 0
MUL_SUCC_LEFT: Formula = Eq(mul(S(_x), _y), add(mul(_x, _y), _y))  # S(x)*y = x*y + y
MUL_COMM: Formula = Eq(mul(_x, _y), mul(_y, _x))  # x * y = y * x
DISTRIB_LEFT: Formula = Eq(  # x*(y+z) = x*y + x*z
    mul(_x, add(_y, _z)),
    add(mul(_x, _y), mul(_x, _z)),
)
DISTRIB_RIGHT: Formula = Eq(  # (x+y)*z = x*z + y*z
    mul(add(_x, _y), _z),
    add(mul(_x, _z), mul(_y, _z)),
)
MUL_ASSOC: Formula = Eq(mul(mul(_x, _y), _z), mul(_x, mul(_y, _z)))  # (x*y)*z = x*(y*z)
MUL_LEFT_COMM: Formula = Eq(mul(_x, mul(_y, _z)), mul(_y, mul(_x, _z)))  # x*(y*z) = y*(x*z)
MUL_CANCEL_RIGHT_SUCC: Formula = Implies(  # x*S(z) = y*S(z) -> x = y
    Eq(mul(_x, S(_z)), mul(_y, S(_z))),
    Eq(_x, _y),
)

MUL_RULES = (axiom_rule(MUL_ZERO_F), axiom_rule(MUL_SUCC_F))
"""The two multiplication axioms, read left to right."""


def mul_zero_left() -> Pf:
    """0 * n = 0, by induction on n -- the mirror of `left_identity`, and
    annoying for the same reason: the axioms recurse on the second argument, so
    a zero sitting in the first one never reduces on its own."""
    return by_induction("n", MUL_ZERO_LEFT, (*ADD_RULES, *MUL_RULES))


def mul_succ_left() -> Pf:
    """S(x) * y = x*y + y, by induction on y: the recursion law for the FIRST
    argument. The step leaves `(x*y + y) + x` against `(x*y + x) + y`, which is
    a pure rearrangement -- hence the addition kit."""
    rules = (*add_kit(), *MUL_RULES)
    return by_induction("y", MUL_SUCC_LEFT, rules)


def mul_comm() -> Pf:
    """x * y = y * x, by induction on y, over the two one-sided lemmas: the base
    case is `x*0 = 0*x` (mul-zero-left) and the step turns `S(y)*x` into
    `y*x + x` (mul-succ-left) -- exactly how `add_comm` uses its own pair."""
    rules = (
        *ADD_RULES,
        *MUL_RULES,
        lemma_rule(MUL_ZERO_LEFT, mul_zero_left()),
        lemma_rule(MUL_SUCC_LEFT, mul_succ_left()),
    )
    return by_induction("y", MUL_COMM, rules)


def distrib_left() -> Pf:
    """x*(y + z) = x*y + x*z, by induction on z. The one law that ties the two
    operations together -- and the reason arithmetic stops being decidable."""
    rules = (*add_kit(), *MUL_RULES)
    return by_induction("z", DISTRIB_LEFT, rules)


def distrib_right() -> Pf:
    """(x + y)*z = x*z + y*z, by induction on z -- distributivity on the other
    side. Provable from `distrib_left` and commutativity, but the direct
    induction is shorter than the rearrangement would be."""
    rules = (*add_kit(), *MUL_RULES)
    return by_induction("z", DISTRIB_RIGHT, rules)


def mul_assoc() -> Pf:
    """(x*y)*z = x*(y*z), by induction on z. The step needs distributivity: the
    right side becomes `x*(y*z + y)`, which only reduces once the product is
    pushed across the sum."""
    rules = (
        *add_kit(),
        *MUL_RULES,
        lemma_rule(DISTRIB_LEFT, distrib_left()),
    )
    return by_induction("z", MUL_ASSOC, rules)


def mul_left_comm() -> Pf:
    """x*(y*z) = y*(x*z), built by hand from `mul_assoc` and `mul_comm` exactly
    as `add_left_comm` is built from theirs."""
    assoc = lemma_rule(MUL_ASSOC, mul_assoc())
    return Trans(
        Sym(mul_assoc()),  # x*(y*z) = (x*y)*z
        Trans(
            Cong("*", (mul_comm(), Refl(_z))),  # (x*y)*z = (y*x)*z
            assoc.instance({"x": _y, "y": _x, "z": _z}),  # (y*x)*z = y*(x*z)
        ),
    )


def ring_kit() -> tuple:
    """Everything proved about `+` and `*` so far, as one rewrite kit.

    On top of `add_kit`: the multiplication recursion axioms and their
    first-argument mirrors reduce a product against a zero or successor;
    both distribution laws, read expansively, push every product across every
    sum; associativity right-nests a monomial and the two `ordered` rules sort
    its factors, exactly as the addition kit sorts summands. The normal form
    is a sorted right-nested sum of sorted right-nested monomials -- a
    POLYNOMIAL -- so `prove_eq` under this kit decides any identity of
    commutative semirings, which is what every payment core of the ring-of-
    integers bridge reduces to."""
    return (
        *add_kit(),
        *MUL_RULES,
        lemma_rule(MUL_ZERO_LEFT, mul_zero_left()),
        lemma_rule(MUL_SUCC_LEFT, mul_succ_left()),
        lemma_rule(DISTRIB_LEFT, distrib_left()),
        lemma_rule(DISTRIB_RIGHT, distrib_right()),
        lemma_rule(MUL_ASSOC, mul_assoc()),
        lemma_rule(MUL_COMM, mul_comm(), ordered=True),
        lemma_rule(MUL_LEFT_COMM, mul_left_comm(), ordered=True),
    )


def _positive_cancel_pred(x: Term, z: Term) -> Formula:
    """The explicitly quantified predicate used by multiplication induction."""
    y = Var("y")
    return forall(
        "y",
        "",
        Implies(Eq(mul(x, S(z)), mul(y, S(z))), Eq(x, y)),
    )


def _zero_product_cancel(z: Term) -> Pf:
    """|- forall y, 0*S(z) = y*S(z) -> 0 = y, by induction on y."""
    y = Var("y")
    pred = Implies(
        Eq(mul(ZERO, S(z)), mul(y, S(z))),
        Eq(ZERO, y),
    )

    base_hyp = Eq(mul(ZERO, S(z)), mul(ZERO, S(z)))
    base = ImpIntro(base_hyp, Refl(ZERO))

    step_hyp = Eq(mul(ZERO, S(z)), mul(S(y), S(z)))
    nonzero_rules = (
        *ADD_RULES,
        lemma_rule(MUL_ZERO_LEFT, mul_zero_left()),
        lemma_rule(MUL_SUCC_LEFT, mul_succ_left()),
    )
    zero_eq_succ = normalize_equality(step_hyp, Assume(step_hyp), nonzero_rules)
    successor = add(mul(y, S(z)), z)
    successor_ne_zero = Inst(Axiom(SUCC_NEQ_ZERO), "x", successor)
    contradiction = MP(successor_ne_zero, Sym(zero_eq_succ))
    step_result = ExFalso(contradiction, Eq(ZERO, S(y)))
    step = ImpIntro(pred, ImpIntro(step_hyp, step_result))

    return ForallIntro("y", "", induction("y", pred, base, step))


def mul_cancel_right_succ() -> Pf:
    """x*S(z) = y*S(z) -> x = y: every positive multiplier cancels in PEANO.

    Induction on ``x`` uses the stronger, explicitly quantified predicate
    ``forall y``.  The zero case is another induction on ``y``: a successor
    times a successor normalizes to a successor and therefore cannot be zero.
    In the successor case, a nested induction on ``y`` separates zero from
    successor; when both are successors, the multiplication recursion law
    exposes a common additive suffix, additive cancellation peels it, and the
    outer induction hypothesis finishes.  No cancellation or order axiom is
    added to the theory.
    """
    x, y, z = _x, _y, _z
    pred = _positive_cancel_pred(x, z)
    base = _zero_product_cancel(z)

    nested = Implies(
        Eq(mul(S(x), S(z)), mul(y, S(z))),
        Eq(S(x), y),
    )
    nested_base_hyp = Eq(mul(S(x), S(z)), mul(ZERO, S(z)))
    nonzero_rules = (
        *ADD_RULES,
        lemma_rule(MUL_ZERO_LEFT, mul_zero_left()),
        lemma_rule(MUL_SUCC_LEFT, mul_succ_left()),
    )
    succ_eq_zero = normalize_equality(
        nested_base_hyp,
        Assume(nested_base_hyp),
        nonzero_rules,
    )
    product_body = add(mul(x, S(z)), z)
    product_ne_zero = Inst(Axiom(SUCC_NEQ_ZERO), "x", product_body)
    base_contradiction = MP(product_ne_zero, succ_eq_zero)
    nested_base = ImpIntro(
        nested_base_hyp,
        ExFalso(base_contradiction, Eq(S(x), ZERO)),
    )

    nested_step_hyp = Eq(mul(S(x), S(z)), mul(S(y), S(z)))
    unfolded = normalize_equality(
        nested_step_hyp,
        Assume(nested_step_hyp),
        (lemma_rule(MUL_SUCC_LEFT, mul_succ_left()),),
    )
    # Instantiate z first: the x/y replacements contain z and must not be
    # rewritten again by a later sequential Inst node.
    add_cancel = Inst(
        Inst(
            Inst(add_cancel_right(), "z", S(z)),
            "x",
            mul(x, S(z)),
        ),
        "y",
        mul(y, S(z)),
    )
    products_equal = MP(add_cancel, unfolded)
    outer_ih_at_y = ForallElim(Assume(pred), y)
    predecessors_equal = MP(outer_ih_at_y, products_equal)
    successors_equal = Cong("S", (predecessors_equal,))
    nested_step_result = ImpIntro(nested_step_hyp, successors_equal)
    nested_step = ImpIntro(nested, nested_step_result)
    nested_induction = induction("y", nested, nested_base, nested_step)

    step = ImpIntro(pred, ForallIntro("y", "", nested_induction))
    all_x = induction("x", pred, base, step)
    return ForallElim(all_x, y)
