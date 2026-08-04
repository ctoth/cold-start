"""Worked proofs. Each function returns a proof term (proof.Pf), an inert
recipe. It asserts nothing until checker.check() re-derives its sequent.

Two styles live here. The first section builds proof terms *by hand*, node by
node -- that is the readable spelling of what a derivation actually is. The
second section builds them *by tactics* (`cold_start.tactics`), stating only the
theorem and letting an untrusted search emit the term. Both end up in front of
the same `check`, which is the point: the checker cannot tell, and does not care,
which one wrote the proof.
"""

from __future__ import annotations

from .peano import MUL_SUCC_F, MUL_ZERO_F, mul
from .presburger import (
    ADD_SUCC_F,
    ADD_ZERO_F,
    SUCC_INJ,
    SUCC_NEQ_ZERO,
    ZERO,
    S,
    add,
    induction,
    numeral,
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
from .prop import And, Or, and_intro, or_elim, or_left, or_right
from .robinson import ADD_ONE, ADD_SUCC
from .syntax import Eq, Formula, Implies, Term, Var, exists, forall
from .tactics import axiom_rule, by_induction, lemma_rule, normalize_equality


def left_identity_proof() -> Pf:
    """Proof term for  0 + n = n  by induction on n.

    The annoying one: `0 + n` does not reduce by the recursion axioms (they
    recurse on the second argument), so induction is the only way through.
    """
    n = Var("n")
    pred = Eq(add(ZERO, n), n)  # P(n) :=  0 + n = n

    # base:  0 + 0 = 0          -- (x + 0 = x) at x := 0
    base = Inst(Axiom(ADD_ZERO_F), "x", ZERO)

    # step:  (0 + n = n) -> (0 + S(n) = S(n))
    ih = Assume(pred)
    #   0 + S(n) = S(0 + n)     -- (x + S y = S(x+y)) at x:=0, y:=n
    unfold = Inst(Inst(Axiom(ADD_SUCC_F), "x", ZERO), "y", n)
    #   S(0 + n) = S(n)         -- congruence of S on the hypothesis
    cong_ih = Cong("S", (ih,))
    #   0 + S(n) = S(n)
    step_eq = Trans(unfold, cong_ih)
    step = ImpIntro(pred, step_eq)

    return induction("n", pred, base, step)


def add_proof(a: int, b: int) -> Pf:
    """Proof term for  numeral(a) + numeral(b) = numeral(a+b).

    Built by unfolding the ADD_SUCC axiom on the concrete second argument -- no
    induction needed, since `b` is a fixed numeral. Useful as a sound generator
    for tests: the checker must agree with it for every a, b.

    Built bottom-up from `a + 0 = a`, one loop iteration per unit of `b`. The
    recursive spelling of this same term was the more obvious one, but it spent
    a Python frame per unit and so could not build past b ~ 1000 -- a proof the
    iterative `check` would have been perfectly happy to verify.
    """
    big_a = numeral(a)
    pf: Pf = Inst(Axiom(ADD_ZERO_F), "x", big_a)  # a + 0 = a
    for k in range(1, b + 1):
        #  a + S(k-1) = S(a + (k-1)),  then fold the sum already proved
        succ_step = Inst(Inst(Axiom(ADD_SUCC_F), "x", big_a), "y", numeral(k - 1))
        pf = Trans(succ_step, Cong("S", (pf,)))
    return pf


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


def robinson_add_proof(a: int, b: int) -> Pf:
    """Proof term for  bridge(numeral(a), numeral(b), numeral(a+b))  in the
    (1, S, ·) theory -- addition computed with no `+` symbol anywhere.

    Climbs the second argument through Robinson's own §2 recursion laws: A4'
    (`a + 1 = S a`) is the base, and A5' (`a + b = c -> a + S b = S c`) is
    instantiated at the concrete numerals and discharged by modus ponens, one
    rung per unit of `b`. Both arguments must be positive -- Robinson's domain
    is the positive integers, and the bridge is the graph of addition only for
    c > 0. Iterative, for the reason given on `add_proof`.
    """
    if a < 1 or b < 1:
        raise ValueError(f"Robinson's domain is the positive integers, got a={a}, b={b}")
    big_a = numeral(a)
    pf: Pf = Inst(Axiom(ADD_ONE), "a", big_a)  # a + 1 = S a
    for k in range(2, b + 1):
        #  a + (k-1) = a+k-1  ->  a + S(k-1) = S(a+k-1),  i.e.  a + k = a+k
        succ_step = Inst(
            Inst(Inst(Axiom(ADD_SUCC), "a", big_a), "b", numeral(k - 1)),
            "c",
            numeral(a + k - 1),
        )
        pf = MP(succ_step, pf)
    return pf


# ---------------------------------------------------------------------------
# The same mathematics, built by tactics
# ---------------------------------------------------------------------------
# Below, nothing is spelled node by node: we state the theorem and let the
# untrusted rewriting engine in `tactics.py` emit the proof term. Each lemma is
# then handed to the next one as a rewrite rule -- a `lemma_rule` wraps the
# lemma's own (hypothesis-free) proof term, so instantiating it introduces no
# assumption and every theorem here still checks with an empty context.

_x, _y, _z, _n = Var("x"), Var("y"), Var("z"), Var("n")

LEFT_IDENTITY: Formula = Eq(add(ZERO, _n), _n)  # 0 + n = n
SUCC_ADD: Formula = Eq(add(S(_x), _y), S(add(_x, _y)))  # S(x) + y = S(x + y)
ADD_COMM: Formula = Eq(add(_x, _y), add(_y, _x))  # x + y = y + x
ADD_ASSOC: Formula = Eq(add(add(_x, _y), _z), add(_x, add(_y, _z)))  # (x+y)+z = x+(y+z)
ADD_LEFT_COMM: Formula = Eq(  # x + (y + z) = y + (x + z)
    add(_x, add(_y, _z)),
    add(_y, add(_x, _z)),
)
ADD_CANCEL_RIGHT: Formula = Implies(  # x + z = y + z -> x = y
    Eq(add(_x, _z), add(_y, _z)),
    Eq(_x, _y),
)
ADD_CANCEL_LEFT: Formula = Implies(  # z + x = z + y -> x = y
    Eq(add(_z, _x), add(_z, _y)),
    Eq(_x, _y),
)

ADD_RULES = (axiom_rule(ADD_ZERO_F), axiom_rule(ADD_SUCC_F))
"""The two recursion axioms, read left to right: the whole starting kit."""


def left_identity() -> Pf:
    """0 + n = n, by induction on n -- the tactic-built twin of
    `left_identity_proof`. Both derive the very same sequent."""
    return by_induction("n", LEFT_IDENTITY, ADD_RULES)


def succ_add() -> Pf:
    """S(x) + y = S(x + y), by induction on y. The axioms recurse on the SECOND
    argument, so moving a successor out of the first one needs induction."""
    return by_induction("y", SUCC_ADD, ADD_RULES)


def add_comm() -> Pf:
    """x + y = y + x, by induction on y, over the axioms plus both lemmas: the
    base case is `x + 0 = 0 + x` (left identity) and the step turns `S(y) + x`
    into `S(y + x)` (succ-add)."""
    rules = (
        *ADD_RULES,
        lemma_rule(LEFT_IDENTITY, left_identity()),
        lemma_rule(SUCC_ADD, succ_add()),
    )
    return by_induction("y", ADD_COMM, rules)


def add_assoc() -> Pf:
    """(x + y) + z = x + (y + z), by induction on z -- the axioms alone suffice,
    since both sides recurse on the same trailing argument."""
    return by_induction("z", ADD_ASSOC, ADD_RULES)


def add_left_comm() -> Pf:
    """x + (y + z) = y + (x + z), the third leg of the AC kit, built by hand
    from associativity and commutativity:

        x + (y + z) = (x + y) + z = (y + x) + z = y + (x + z).

    Hand-built because the tactics cannot reach it: `prove_eq` would need
    commutativity as a rewrite rule, and this very lemma is what an *ordered*
    commutativity rule is missing -- ordered rewriting sorts the arguments of
    one `+`, and this is what lets a swap reach past the head of a nested sum.
    """
    assoc = lemma_rule(ADD_ASSOC, add_assoc())
    return Trans(
        Sym(add_assoc()),  # x + (y + z) = (x + y) + z
        Trans(
            Cong("+", (add_comm(), Refl(_z))),  # (x + y) + z = (y + x) + z
            assoc.instance({"x": _y, "y": _x, "z": _z}),  # (y + x) + z = y + (x + z)
        ),
    )


def add_cancel_right() -> Pf:
    """x + z = y + z -> x = y, by induction on the common suffix ``z``.

    The base simply unfolds both zero sums.  In the step both sums unfold to
    successors; successor injectivity peels those, and the induction hypothesis
    cancels the remaining common suffix.  Unlike the equational laws above,
    this proof needs implication introduction and modus ponens, so
    ``normalize_equality`` supplies the algebraic transport inside each case.
    """
    base_hyp = Eq(add(_x, ZERO), add(_y, ZERO))
    base = ImpIntro(
        base_hyp,
        normalize_equality(base_hyp, Assume(base_hyp), ADD_RULES),
    )

    step_hyp = Eq(add(_x, S(_z)), add(_y, S(_z)))
    unfolded = normalize_equality(step_hyp, Assume(step_hyp), ADD_RULES)
    injective = Inst(
        Inst(Axiom(SUCC_INJ), "x", add(_x, _z)),
        "y",
        add(_y, _z),
    )
    peeled = MP(injective, unfolded)
    step_result = MP(Assume(ADD_CANCEL_RIGHT), peeled)
    step = ImpIntro(ADD_CANCEL_RIGHT, ImpIntro(step_hyp, step_result))

    return induction("z", ADD_CANCEL_RIGHT, base, step)


def add_cancel_left() -> Pf:
    """z + x = z + y -> x = y, from commutativity and right cancellation."""
    hyp = Eq(add(_z, _x), add(_z, _y))
    comm = lemma_rule(ADD_COMM, add_comm())
    zx_to_xz = comm.instance({"x": _z, "y": _x})
    zy_to_yz = comm.instance({"x": _z, "y": _y})
    right_cancel_hyp = Trans(Sym(zx_to_xz), Trans(Assume(hyp), zy_to_yz))
    return ImpIntro(hyp, MP(add_cancel_right(), right_cancel_hyp))


def add_kit() -> tuple:
    """Everything proved about `+` so far, as one rewrite kit.

    The two recursion axioms and their two mirror images reduce a sum whose
    second OR first argument is a zero or a successor; associativity right-nests
    it; commutativity and left-commutativity, both `ordered`, sort the summands.
    The result is a canonical arrangement -- so `prove_eq` decides any goal whose
    sides differ only in how their additions are bracketed and ordered, which is
    what every rung of the multiplication ladder above needs.

    The zero laws have to travel WITH the sorting rules: the order puts `0`
    first, so `x*y + 0` sorts to `0 + x*y`, and only `0 + n = n` finishes it."""
    return (
        *ADD_RULES,
        lemma_rule(LEFT_IDENTITY, left_identity()),
        lemma_rule(SUCC_ADD, succ_add()),
        lemma_rule(ADD_ASSOC, add_assoc()),
        lemma_rule(ADD_COMM, add_comm(), ordered=True),
        lemma_rule(ADD_LEFT_COMM, add_left_comm(), ordered=True),
    )


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


ZERO_OR_SUCC: Formula = Or(  # n = 0  or  exists m, n = S(m)
    Eq(_n, ZERO),
    exists("m", "", Eq(_n, S(Var("m")))),
)


def zero_or_succ() -> Pf:
    """Every number is zero or a successor -- the case-split principle.

    Induction on ``n`` where neither case needs its hypothesis: at zero the
    left disjunct is reflexivity, and at ``S(n)`` the right disjunct holds
    with witness ``n``. A Presburger theorem; classical only through the
    disjunction encoding itself."""
    ex_zero = exists("m", "", Eq(ZERO, S(Var("m"))))
    base = or_left(Eq(ZERO, ZERO), ex_zero, Refl(ZERO))

    ex_succ = exists("m", "", Eq(S(_n), S(Var("m"))))
    witness = ExistsIntro(ex_succ, _n, Refl(S(_n)))
    step = ImpIntro(ZERO_OR_SUCC, or_right(Eq(S(_n), ZERO), ex_succ, witness))

    return induction("n", ZERO_OR_SUCC, base, step)


ADD_EQ_ZERO: Formula = Implies(  # x + y = 0  ->  x = 0 and y = 0
    Eq(add(_x, _y), ZERO),
    And(Eq(_x, ZERO), Eq(_y, ZERO)),
)


def add_eq_zero() -> Pf:
    """A zero sum has zero summands -- by cases on ``y`` via ``zero_or_succ``.

    When ``y = 0`` the hypothesis collapses to ``x = 0`` through the zero
    axiom; when ``y = S(m)`` the sum is a successor, and a successor is never
    zero. The corner every subtraction-free divisibility argument hits."""
    hyp = Eq(add(_x, _y), ZERO)
    goal = And(Eq(_x, ZERO), Eq(_y, ZERO))
    y_zero = Eq(_y, ZERO)
    ex_succ = exists("m", "", Eq(_y, S(Var("m"))))

    x_plus_zero = Inst(Axiom(ADD_ZERO_F), "x", _x)  # x + 0 = x
    shift = Cong("+", (Refl(_x), Assume(y_zero)))  # x + y = x + 0
    x_zero = Trans(Trans(Sym(x_plus_zero), Sym(shift)), Assume(hyp))  # x = 0
    zero_arm = ImpIntro(y_zero, and_intro(Eq(_x, ZERO), y_zero, x_zero, Assume(y_zero)))

    m = Var("m!")
    y_succ = Eq(_y, S(m))
    unfold = Inst(Inst(Axiom(ADD_SUCC_F), "x", _x), "y", m)  # x + S(m!) = S(x + m!)
    shift_succ = Cong("+", (Refl(_x), Assume(y_succ)))  # x + y = x + S(m!)
    succ_is_zero = Trans(Trans(Sym(unfold), Sym(shift_succ)), Assume(hyp))  # S(x+m!) = 0
    boom = MP(Inst(Axiom(SUCC_NEQ_ZERO), "x", add(_x, m)), succ_is_zero)
    succ_arm = ImpIntro(ex_succ, ExistsElim("m!", Assume(ex_succ), ExFalso(boom, goal)))

    cases = or_elim(y_zero, ex_succ, goal, Inst(zero_or_succ(), "n", _y), zero_arm, succ_arm)
    return ImpIntro(hyp, cases)


if __name__ == "__main__":
    from .checker import check
    from .presburger import PRESBURGER

    print("left identity:", check(left_identity_proof(), PRESBURGER))
    for name, build in (
        ("left identity (tactic)", left_identity),
        ("succ-add", succ_add),
        ("commutativity", add_comm),
        ("associativity", add_assoc),
    ):
        print(f"{name}:", check(build(), PRESBURGER))
