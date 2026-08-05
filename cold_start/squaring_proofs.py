"""Proof builders for addition arithmetic with primitive squaring."""

from __future__ import annotations

from .combination import by_combination
from .presburger import SUCC_INJ, SUCC_NEQ_ZERO, ZERO, S, add, induction
from .presburger_proofs import add_eq_zero, add_kit, zero_or_succ
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
    Sym,
    Trans,
)
from .prop import and_left, or_elim
from .squaring import (
    SQUARE_SUCC_F,
    SQUARE_ZERO_F,
    double,
    square_product,
)
from .syntax import Eq, Formula, Implies, Var, exists, forall
from .tactics import axiom_rule, normalize_equality, prove_eq

_x, _y = Var("x"), Var("y")
_x0, _x1, _c, _d = Var("x!0"), Var("x!1"), Var("c!"), Var("d!")


def square_kit() -> tuple:
    """Additive canonicalization plus the two square recursions."""
    return (
        *add_kit(),
        axiom_rule(SQUARE_ZERO_F),
        axiom_rule(SQUARE_SUCC_F),
    )


DOUBLE_INJECTIVE: Formula = Implies(Eq(double(_x), double(_y)), Eq(_x, _y))


def double_injective() -> Pf:
    """Addition-only proof that ``x+x = y+y`` implies ``x=y``."""
    y = Var("y")
    pred = forall(
        "y",
        "",
        Implies(Eq(double(_x), double(y)), Eq(_x, y)),
    )

    base_hyp = Eq(double(ZERO), double(y))
    base_normal = normalize_equality(base_hyp, Assume(base_hyp), add_kit())
    both_zero = MP(
        Inst(Inst(add_eq_zero(), "x", y), "y", y),
        Sym(base_normal),
    )
    y_zero = and_left(Eq(y, ZERO), Eq(y, ZERO), both_zero)
    base = ForallIntro("y", "", ImpIntro(base_hyp, Sym(y_zero)))

    step_hyp = Eq(double(S(_x)), double(y))
    goal = Eq(S(_x), y)
    y_is_zero = Eq(y, ZERO)
    y_is_succ = exists("w", "", Eq(y, S(Var("w"))))

    shifted_zero = Trans(
        Assume(step_hyp),
        Cong("+", (Assume(y_is_zero), Assume(y_is_zero))),
    )
    normalized_zero = normalize_equality(
        Eq(double(S(_x)), double(ZERO)),
        shifted_zero,
        add_kit(),
    )
    impossible = MP(Inst(Axiom(SUCC_NEQ_ZERO), "x", S(double(_x))), normalized_zero)
    zero_arm = ImpIntro(y_is_zero, ExFalso(impossible, goal))

    w = Var("w")
    y_eq_succ = Eq(y, S(w))
    shifted_succ = Trans(
        Assume(step_hyp),
        Cong("+", (Assume(y_eq_succ), Assume(y_eq_succ))),
    )
    normalized_succ = normalize_equality(
        Eq(double(S(_x)), double(S(w))),
        shifted_succ,
        add_kit(),
    )
    peel_once = MP(
        Inst(Inst(Axiom(SUCC_INJ), "x", S(double(_x))), "y", S(double(w))),
        normalized_succ,
    )
    peel_twice = MP(
        Inst(Inst(Axiom(SUCC_INJ), "x", double(_x)), "y", double(w)),
        peel_once,
    )
    ih_at_w = ForallElim(Assume(pred), w)
    x_eq_w = MP(ih_at_w, peel_twice)
    sx_eq_sw = Cong("S", (x_eq_w,))
    succ_result = Trans(sx_eq_sw, Sym(Assume(y_eq_succ)))
    succ_arm = ImpIntro(y_is_succ, ExistsElim("w", Assume(y_is_succ), succ_result))

    cases = or_elim(
        y_is_zero,
        y_is_succ,
        goal,
        Inst(zero_or_succ(), "n", y),
        zero_arm,
        succ_arm,
    )
    step = ImpIntro(pred, ForallIntro("y", "", ImpIntro(step_hyp, cases)))
    all_y = induction("x", pred, base, step)
    return ForallElim(all_y, _y)


def _totality_at(right) -> Formula:
    return exists("c!", "", square_product(_x0, right, Var("c!")))


def square_product_total() -> Pf:
    """The polarization graph is total, by addition-only induction on ``y``."""
    pred = _totality_at(_x1)
    base_graph = square_product(_x0, ZERO, ZERO)
    base = ExistsIntro(_totality_at(ZERO), ZERO, prove_eq(base_graph, square_kit()))

    z = Var("z")
    current_graph = square_product(_x0, _x1, z)
    next_graph = square_product(_x0, S(_x1), add(z, _x0))
    stepped = by_combination(
        next_graph,
        ((current_graph, Assume(current_graph), None),),
        square_kit(),
    )
    packed = ExistsIntro(_totality_at(S(_x1)), add(z, _x0), stepped)
    used = ExistsElim("z", Assume(pred), packed)
    step = ImpIntro(pred, used)
    return induction("x!1", pred, base, step)


def square_product_unique() -> Pf:
    """The polarization graph is functional by cancellation and double injection."""
    left = square_product(_x0, _x1, _c)
    right = square_product(_x0, _x1, _d)
    doubles = Eq(double(_c), double(_d))
    same_square = Trans(Assume(left), Sym(Assume(right)))
    doubles_pf = by_combination(
        doubles,
        ((Eq(left.lhs, right.lhs), same_square, None),),
        add_kit(),
    )
    result = MP(
        Inst(Inst(double_injective(), "x", _c), "y", _d),
        doubles_pf,
    )
    return ImpIntro(left, ImpIntro(right, result))


__all__ = [
    "DOUBLE_INJECTIVE",
    "double_injective",
    "square_kit",
    "square_product_total",
    "square_product_unique",
]
