"""Shared Grothendieck-pair translation and additive payment mechanics."""

from __future__ import annotations

from collections.abc import Callable

from .combination import Hypothesis, by_combination
from .presburger_proofs import add_kit
from .proof import Assume, ExistsIntro, ForallIntro, ImpIntro, Pf, Refl, Sym
from .quotient import Vec, VecSymbol, vec
from .syntax import Eq, Formula, Term, exists
from .vocabulary import add

Orientation = Callable[[tuple[Eq, ...], Eq, Eq], tuple[Hypothesis, ...]]


def int_eq(left: Vec, right: Vec) -> Eq:
    return Eq(add(left[0], right[1]), add(right[0], left[1]))


def zero_graph(args: tuple[Vec, ...], result: Vec) -> Eq:
    return Eq(result[0], result[1])


def add_graph(args: tuple[Vec, ...], result: Vec) -> Eq:
    left, right = args
    return int_eq(
        (add(left[0], right[0]), add(left[1], right[1])),
        result,
    )


def neg_graph(args: tuple[Vec, ...], result: Vec) -> Eq:
    (value,) = args
    return int_eq((value[1], value[0]), result)


ZERO_AS_DIAGONAL = VecSymbol("0", 0, zero_graph)
ADD_COMPONENTWISE = VecSymbol("+", 2, add_graph)
NEG_AS_SWAP = VecSymbol("neg", 1, neg_graph)

_KIT = add_kit()


def cancel(goal: Eq, hypotheses: tuple[Hypothesis, ...]) -> Pf:
    return by_combination(goal, hypotheses, _KIT)


def assume(equality: Eq) -> Hypothesis:
    return equality, Assume(equality), None


def flip(equality: Eq) -> Hypothesis:
    return Eq(equality.rhs, equality.lhs), Sym(Assume(equality)), None


_A, _B, _C = vec("x!", 2), vec("y!", 2), vec("z!", 2)


def pay_equivalence_refl() -> Pf:
    return Refl(add(_A[0], _A[1]))


def pay_equivalence_sym() -> Pf:
    hypothesis = int_eq(_A, _B)
    return ImpIntro(hypothesis, Sym(Assume(hypothesis)))


def pay_equivalence_trans() -> Pf:
    first, second = int_eq(_A, _B), int_eq(_B, _C)
    core = cancel(int_eq(_A, _C), (assume(first), assume(second)))
    return ImpIntro(first, ImpIntro(second, core))


def pay_totality(symbol: VecSymbol, image: tuple[Term, Term]) -> Pf:
    args = symbol.canonical_args(2)
    claim = symbol.graph(args, vec("c!", 2))
    outer: Formula = exists("c!.1", "", exists("c!.2", "", claim))
    inner = exists("c!.2", "", symbol.graph(args, (image[0], vec("c!", 2)[1])))
    ground = symbol.graph(args, image)
    if type(ground) is not Eq or ground.lhs != ground.rhs:
        raise ValueError(f"totality image does not make {symbol.fun!r} reflexive")
    return ExistsIntro(outer, image[0], ExistsIntro(inner, image[1], Refl(ground.lhs)))


def pay_respect(symbol: VecSymbol, orient: Orientation) -> Pf:
    args, primed = symbol.canonical_args(2), symbol.primed_args(2)
    result, other = vec("c!", 2), vec("d!", 2)
    equivalences = tuple(
        int_eq(old, new) for old, new in zip(args, primed, strict=True)
    )
    first_graph = symbol.graph(args, result)
    second_graph = symbol.graph(primed, other)
    if type(first_graph) is not Eq or type(second_graph) is not Eq:
        raise ValueError(f"respect for {symbol.fun!r} requires equation graphs")
    core = cancel(
        int_eq(result, other),
        orient(equivalences, first_graph, second_graph),
    )
    out = ImpIntro(first_graph, ImpIntro(second_graph, core))
    for hypothesis in reversed(equivalences):
        out = ImpIntro(hypothesis, out)
    return out


def orient_zero(
    equivalences: tuple[Eq, ...],
    first_graph: Eq,
    second_graph: Eq,
) -> tuple[Hypothesis, ...]:
    return (assume(first_graph), flip(second_graph))


def orient_add(
    equivalences: tuple[Eq, ...],
    first_graph: Eq,
    second_graph: Eq,
) -> tuple[Hypothesis, ...]:
    return (
        flip(first_graph),
        assume(second_graph),
        assume(equivalences[0]),
        assume(equivalences[1]),
    )


def orient_neg(
    equivalences: tuple[Eq, ...],
    first_graph: Eq,
    second_graph: Eq,
) -> tuple[Hypothesis, ...]:
    return (flip(equivalences[0]), flip(first_graph), assume(second_graph))


def guarded_axiom_payment(
    guards: tuple[tuple[str, Formula], ...],
    core: Pf,
) -> Pf:
    out = core
    for marker, guard in reversed(guards):
        out = ImpIntro(guard, out)
        for index in reversed(range(2)):
            out = ForallIntro(f"{marker}.{index + 1}", "", out)
    return out


_X, _Y, _Z = vec("x", 2), vec("y", 2), vec("z", 2)
_U, _U0, _U1, _U2 = vec("u!", 2), vec("u!0", 2), vec("u!1", 2), vec("u!2", 2)


def pay_add_zero() -> Pf:
    zero = zero_graph((), _U)
    summed = add_graph((_X, _U), _U0)
    core = cancel(int_eq(_U0, _X), (flip(summed), assume(zero)))
    return guarded_axiom_payment((("u!", zero), ("u!0", summed)), core)


def pay_add_comm() -> Pf:
    right = add_graph((_Y, _X), _U)
    left = add_graph((_X, _Y), _U0)
    core = cancel(int_eq(_U0, _U), (flip(left), assume(right)))
    return guarded_axiom_payment((("u!", right), ("u!0", left)), core)


def pay_add_assoc() -> Pf:
    first = add_graph((_Y, _Z), _U)
    second = add_graph((_X, _U), _U0)
    third = add_graph((_X, _Y), _U1)
    fourth = add_graph((_U1, _Z), _U2)
    core = cancel(
        int_eq(_U2, _U0),
        (assume(first), assume(second), flip(third), flip(fourth)),
    )
    return guarded_axiom_payment(
        (("u!", first), ("u!0", second), ("u!1", third), ("u!2", fourth)),
        core,
    )


def pay_add_neg() -> Pf:
    zero = zero_graph((), _U)
    negated = neg_graph((_X,), _U0)
    summed = add_graph((_X, _U0), _U1)
    core = cancel(int_eq(_U1, _U), (flip(summed), flip(negated), flip(zero)))
    return guarded_axiom_payment(
        (("u!", zero), ("u!0", negated), ("u!1", summed)),
        core,
    )


__all__ = [
    "ADD_COMPONENTWISE",
    "NEG_AS_SWAP",
    "ZERO_AS_DIAGONAL",
    "Orientation",
    "add_graph",
    "assume",
    "cancel",
    "flip",
    "guarded_axiom_payment",
    "int_eq",
    "neg_graph",
    "orient_add",
    "orient_neg",
    "orient_zero",
    "pay_add_assoc",
    "pay_add_comm",
    "pay_add_neg",
    "pay_add_zero",
    "pay_equivalence_refl",
    "pay_equivalence_sym",
    "pay_equivalence_trans",
    "pay_respect",
    "pay_totality",
    "zero_graph",
]
