"""The order kit: ``<=`` as a witnessed sum, and strong induction from it.

``le(a, b) := exists w, a + w = b`` -- order defined by addition, nothing new
trusted. The lemmas here are the small change of every descent argument:
reflexivity, the zero case, the successor split, the doubling bound, and the
halving descent step. On top of them, `course_of_values` compiles STRONG
induction down to the structural `Induct` rule through the reach predicate

    reach(n)  :=  forall z (z <= n -> P(z))

-- ordinary induction on `n` proves reach everywhere, and P(x) falls out at
`n := x` by reflexivity. The base and step transports (P at 0 becomes P at a
generic z below zero; P at S(n) becomes P at a z equal to it) go through the
`transport` tactic, so this module is where order, equality-rewriting, and
induction meet.

This kit is the shared frontier named by both open ledgers: the Skolem
bridge's product closure descends through dyadic layers with it, and the
formula (2) bounding argument (H2) is made of the same pieces.

Untrusted, like every prover module: `check` remains the only judge.
"""

from __future__ import annotations

from .parity import TWO
from .peano_proofs import MUL_RULES
from .presburger import ADD_SUCC_F, ADD_ZERO_F, SUCC_INJ, induction
from .presburger_proofs import (
    ADD_RULES,
    LEFT_IDENTITY,
    add_assoc,
    add_cancel_left,
    add_eq_zero,
    left_identity,
    zero_or_succ,
)
from .proof import (
    MP,
    Assume,
    Axiom,
    Cong,
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
from .prop import Or, and_left, or_elim, or_left, or_right
from .syntax import Eq, Formula, Implies, Term, Var, exists, forall, instantiate
from .tactics import Rule, lemma_rule, prove_eq, transport
from .vocabulary import ZERO, S, add, mul


def _fresh(stem: str, *terms: Term) -> str:
    used = {name for term in terms for name in term.free_vars()}
    if stem not in used:
        return stem
    index = 0
    while f"{stem}{index}" in used:
        index += 1
    return f"{stem}{index}"


def le(a: Term, b: Term) -> Formula:
    """``a <= b`` as ``exists w, a + w = b`` -- order from addition alone."""
    witness_name = _fresh("w", a, b)
    return exists(witness_name, "", Eq(add(a, Var(witness_name)), b))


_a, _b, _m, _n = Var("a"), Var("b"), Var("m"), Var("n")

LE_REFL: Formula = le(_a, _a)
LE_ZERO: Formula = Implies(le(_a, ZERO), Eq(_a, ZERO))
LE_ANTISYM: Formula = Implies(le(_a, _b), Implies(le(_b, _a), Eq(_a, _b)))
LE_SUCC_SPLIT: Formula = Implies(le(_a, S(_n)), Or(le(_a, _n), Eq(_a, S(_n))))
LE_DOUBLE: Formula = le(_a, mul(_a, TWO))
POS_HALF_LE: Formula = Implies(
    Eq(_a, S(_m)),
    Implies(Eq(mul(_a, TWO), S(_n)), le(_a, _n)),
)


def le_refl() -> Pf:
    """``a <= a``; the witness is 0."""
    return ExistsIntro(LE_REFL, ZERO, Inst(Axiom(ADD_ZERO_F), "x", _a))


def le_zero() -> Pf:
    """``a <= 0 -> a = 0``: a zero sum has zero summands."""
    hyp = le(_a, ZERO)
    w = Var("w!")
    witness = Eq(add(_a, w), ZERO)
    split = MP(Inst(Inst(add_eq_zero(), "x", _a), "y", w), Assume(witness))
    a_zero = and_left(Eq(_a, ZERO), Eq(w, ZERO), split)
    return ImpIntro(hyp, ExistsElim("w!", Assume(hyp), a_zero))


def le_antisym() -> Pf:
    """Mutual witnessed-sum bounds force equality."""
    ab, ba = le(_a, _b), le(_b, _a)
    w, v = Var("w!"), Var("v!")
    ab_w = instantiate(ab, w)
    ba_v = instantiate(ba, v)

    assoc = Inst(Inst(Inst(add_assoc(), "x", _a), "y", w), "z", v)
    replace_ab = Cong("+", (Assume(ab_w), Refl(v)))
    loop = Trans(Sym(assoc), Trans(replace_ab, Assume(ba_v)))
    a_zero = Inst(Axiom(ADD_ZERO_F), "x", _a)
    cancellable = Trans(loop, Sym(a_zero))
    cancel = Inst(
        Inst(Inst(add_cancel_left(), "z", _a), "x", add(w, v)),
        "y",
        ZERO,
    )
    sum_zero = MP(cancel, cancellable)
    split = MP(Inst(Inst(add_eq_zero(), "x", w), "y", v), sum_zero)
    w_zero = and_left(Eq(w, ZERO), Eq(v, ZERO), split)

    collapse = Cong("+", (Refl(_a), w_zero))
    result = Trans(Sym(a_zero), Trans(Sym(collapse), Assume(ab_w)))
    use_ba = ExistsElim("v!", Assume(ba), result)
    use_ab = ExistsElim("w!", Assume(ab), use_ba)
    return ImpIntro(ab, ImpIntro(ba, use_ab))


def le_succ_split() -> Pf:
    """``a <= S(n) -> a <= n or a = S(n)`` -- discreteness of the order.

    Split the witness: a zero witness makes the sum collapse to ``a`` itself,
    and a successor witness peels one rung into ``a <= n``."""
    hyp = le(_a, S(_n))
    goal = Or(le(_a, _n), Eq(_a, S(_n)))
    w, v = Var("w!"), Var("v!")
    witness = Eq(add(_a, w), S(_n))

    w_zero = Eq(w, ZERO)
    collapse = Trans(Sym(Cong("+", (Refl(_a), Assume(w_zero)))), Assume(witness))  # a+0 = S(n)
    a_eq = Trans(Sym(Inst(Axiom(ADD_ZERO_F), "x", _a)), collapse)  # a = S(n)
    zero_arm = ImpIntro(w_zero, or_right(le(_a, _n), Eq(_a, S(_n)), a_eq))

    w_succ = Eq(w, S(v))
    to_succ = Cong("+", (Refl(_a), Assume(w_succ)))  # a+w! = a+S(v!)
    unfold = Inst(Inst(Axiom(ADD_SUCC_F), "x", _a), "y", v)  # a+S(v!) = S(a+v!)
    succs = Trans(Sym(unfold), Trans(Sym(to_succ), Assume(witness)))  # S(a+v!) = S(n)
    peeled = MP(Inst(Inst(Axiom(SUCC_INJ), "x", add(_a, v)), "y", _n), succs)
    packed = ExistsIntro(le(_a, _n), v, peeled)
    ex_succ = exists("m", "", Eq(w, S(Var("m"))))
    succ_arm = ImpIntro(
        ex_succ,
        ExistsElim("v!", Assume(ex_succ), or_left(le(_a, _n), Eq(_a, S(_n)), packed)),
    )

    cases = or_elim(w_zero, ex_succ, goal, Inst(zero_or_succ(), "n", w), zero_arm, succ_arm)
    return ImpIntro(hyp, ExistsElim("w!", Assume(hyp), cases))


def _double_rules() -> tuple[Rule, ...]:
    return (*ADD_RULES, *MUL_RULES, lemma_rule(LEFT_IDENTITY, left_identity()))


def le_double() -> Pf:
    """``a <= a*2``; the witness is ``a`` itself."""
    return ExistsIntro(LE_DOUBLE, _a, prove_eq(Eq(add(_a, _a), mul(_a, TWO)), _double_rules()))


def pos_half_le() -> Pf:
    """``a = S(m) -> a*2 = S(n) -> a <= n``: a positive half sits strictly
    below its double, said discretely. The descent step of every dyadic
    argument."""
    h_pos, h_double = Eq(_a, S(_m)), Eq(mul(_a, TWO), S(_n))
    to_sum = prove_eq(Eq(mul(_a, TWO), add(_a, _a)), _double_rules())
    sum_eq = Trans(Sym(to_sum), Assume(h_double))  # a+a = S(n)
    shift = Cong("+", (Refl(_a), Assume(h_pos)))  # a+a = a+S(m)
    unfold = Inst(Inst(Axiom(ADD_SUCC_F), "x", _a), "y", _m)  # a+S(m) = S(a+m)
    succs = Trans(Sym(unfold), Trans(Sym(shift), sum_eq))  # S(a+m) = S(n)
    peeled = MP(Inst(Inst(Axiom(SUCC_INJ), "x", add(_a, _m)), "y", _n), succs)
    return ImpIntro(h_pos, ImpIntro(h_double, ExistsIntro(le(_a, _n), _m, peeled)))


# ---------------------------------------------------------------------------
# Strong induction, compiled to Induct
# ---------------------------------------------------------------------------


def reach(var: str, pred: Formula, bound: Term, z: str = "z!") -> Formula:
    """``forall z (z <= bound -> pred[var := z])`` -- everything at or below
    the bound. The step of `course_of_values` may assume exactly this."""
    zv = Var(z)
    return forall(z, "", Implies(le(zv, bound), pred.subst(var, zv)))


def course_of_values(var: str, pred: Formula, n: str, base: Pf, step: Pf, z: str = "z!") -> Pf:
    """Strong induction on ``var`` over ``pred``.

        base : |- pred[var := 0]
        step : |- pred[var := S(n)], may assume  reach(var, pred, Var(n), z)
        ----------------------------------------------------------------------
             : |- pred

    ``n`` and ``z`` name the bound and the reach binder; both must be fresh
    for `pred` (and absent from `base`/`step`'s other hypotheses -- `Induct`'s
    side condition enforces the honesty of that requirement). Ordinary
    induction proves the reach predicate at every bound: below zero everything
    IS zero (`le_zero`, transported), and below `S(n)` the successor split
    sends each `z` either under the reach hypothesis or onto `S(n)` itself
    (`step`, transported). `pred` then falls out at `n := var` by
    reflexivity."""
    nv, zv = Var(n), Var(z)
    everything_below = reach(var, pred, nv, z)
    pred_at_z = pred.subst(var, zv)

    below_zero = le(zv, ZERO)
    z_is_zero = MP(Inst(le_zero(), "a", zv), Assume(below_zero))
    based = transport(pred, var, Eq(ZERO, zv), Sym(z_is_zero), base)
    base_reach = ForallIntro(z, "", ImpIntro(below_zero, based))

    below_succ = le(zv, S(nv))
    split = MP(Inst(Inst(le_succ_split(), "a", zv), "n", nv), Assume(below_succ))
    under = ForallElim(Assume(everything_below), zv)  # z <= n -> P(z)
    z_is_top = Eq(zv, S(nv))
    stepped = transport(pred, var, Eq(S(nv), zv), Sym(Assume(z_is_top)), step)
    at_top = ImpIntro(z_is_top, stepped)
    cases = or_elim(le(zv, nv), z_is_top, pred_at_z, split, under, at_top)
    step_reach = ImpIntro(everything_below, ForallIntro(z, "", ImpIntro(below_succ, cases)))

    everywhere = induction(n, everything_below, base_reach, step_reach)
    at_var = ForallElim(Inst(everywhere, n, Var(var)), Var(var))
    return MP(at_var, Inst(le_refl(), "a", Var(var)))


__all__ = [
    "LE_ANTISYM",
    "LE_DOUBLE",
    "LE_REFL",
    "LE_SUCC_SPLIT",
    "LE_ZERO",
    "POS_HALF_LE",
    "course_of_values",
    "le",
    "le_antisym",
    "le_double",
    "le_refl",
    "le_succ_split",
    "le_zero",
    "pos_half_le",
    "reach",
]
