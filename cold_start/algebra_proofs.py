"""Derived proof recipes for the generic commutative-ring normalizer."""

from __future__ import annotations

from collections.abc import Callable

from .algebra import (
    ADD_ASSOC,
    ADD_COMM,
    ADD_NEG,
    ADD_ZERO,
    COMM,
    DIST_LEFT,
    DIST_RIGHT,
    MUL_ASSOC,
    MUL_LEFT_ID,
    MUL_RIGHT_ID,
)
from .proof import MP, Assume, Cong, ImpIntro, Pf, Refl, Sym, Trans
from .ring_nf import AlgebraContext, instantiate_right_cancellation
from .syntax import Eq, Formula, Term, Var
from .tactics import Rule, axiom_rule, lemma_rule, prove_eq
from .vocabulary import ONE, ZERO, add, mul, neg

_x, _y, _z = Var("x"), Var("y"), Var("z")


def _rotate_rule(
    assoc: Formula,
    comm: Formula,
    name: str,
    operation: Callable[[Term, Term], Term],
) -> Rule:
    assoc_rule = axiom_rule(assoc)
    proof = Trans(
        Trans(
            Sym(assoc_rule.instance({"x": _x, "y": _y, "z": _z})),
            Cong(name, (axiom_rule(comm).instance({"x": _x, "y": _y}), Refl(_z))),
        ),
        assoc_rule.instance({"x": _y, "y": _x, "z": _z}),
    )
    return Rule(
        Eq(operation(_x, operation(_y, _z)), operation(_y, operation(_x, _z))),
        proof,
        frozenset({"x", "y", "z"}),
        ordered=True,
    )


def _zero_add_rule() -> Rule:
    proof = Trans(
        axiom_rule(ADD_COMM).instance({"x": ZERO, "y": _x}),
        axiom_rule(ADD_ZERO).instance({"x": _x}),
    )
    return lemma_rule(Eq(add(ZERO, _x), _x), proof)


def _cancel_pair_rule() -> Rule:
    proof = Trans(
        Sym(axiom_rule(ADD_ASSOC).instance({"x": _x, "y": neg(_x), "z": _y})),
        Trans(
            Cong(
                "+",
                (axiom_rule(ADD_NEG).instance({"x": _x}), Refl(_y)),
            ),
            _zero_add_rule().instance({"x": _y}),
        ),
    )
    return lemma_rule(Eq(add(_x, add(neg(_x), _y)), _y), proof)


def ring_add_cancel_right() -> Pf:
    """Derive ``x+z=y+z -> x=y`` from the abelian-group axioms."""
    hypothesis = Eq(add(_x, _z), add(_y, _z))
    extended = Cong("+", (Assume(hypothesis), Refl(neg(_z))))

    def remove_suffix(head: Term) -> Pf:
        return Trans(
            axiom_rule(ADD_ASSOC).instance({"x": head, "y": _z, "z": neg(_z)}),
            Trans(
                Cong(
                    "+",
                    (Refl(head), axiom_rule(ADD_NEG).instance({"x": _z})),
                ),
                axiom_rule(ADD_ZERO).instance({"x": head}),
            ),
        )

    return ImpIntro(
        hypothesis,
        Trans(Sym(remove_suffix(_x)), Trans(extended, remove_suffix(_y))),
    )


def _cancel(lhs: Term, rhs: Term, suffix: Term) -> Pf:
    return instantiate_right_cancellation(ring_add_cancel_right(), lhs, rhs, suffix)


def _zero_mul_rule() -> Rule:
    product = mul(ZERO, _x)
    duplicate = Trans(
        Cong(
            "*",
            (Sym(axiom_rule(ADD_ZERO).instance({"x": ZERO})), Refl(_x)),
        ),
        axiom_rule(DIST_RIGHT).instance({"x": ZERO, "y": ZERO, "z": _x}),
    )
    cancellable = Trans(_zero_add_rule().instance({"x": product}), duplicate)
    proof = Sym(MP(_cancel(ZERO, product, product), cancellable))
    return lemma_rule(Eq(product, ZERO), proof)


def _mul_zero_rule() -> Rule:
    proof = Trans(
        axiom_rule(COMM).instance({"x": _x, "y": ZERO}),
        _zero_mul_rule().instance({"x": _x}),
    )
    return lemma_rule(Eq(mul(_x, ZERO), ZERO), proof)


def _neg_zero_rule() -> Rule:
    proof = Trans(
        Sym(_zero_add_rule().instance({"x": neg(ZERO)})),
        axiom_rule(ADD_NEG).instance({"x": ZERO}),
    )
    return lemma_rule(Eq(neg(ZERO), ZERO), proof)


def _neg_neg_rule() -> Rule:
    left_zero = Trans(
        axiom_rule(ADD_COMM).instance({"x": neg(neg(_x)), "y": neg(_x)}),
        axiom_rule(ADD_NEG).instance({"x": neg(_x)}),
    )
    right_zero = axiom_rule(ADD_NEG).instance({"x": _x})
    cancellable = Trans(left_zero, Sym(right_zero))
    proof = MP(_cancel(neg(neg(_x)), _x, neg(_x)), cancellable)
    return lemma_rule(Eq(neg(neg(_x)), _x), proof)


def _additive_rules() -> tuple[Rule, ...]:
    return (
        _zero_add_rule(),
        axiom_rule(ADD_ZERO),
        axiom_rule(ADD_NEG),
        _neg_zero_rule(),
        _neg_neg_rule(),
        axiom_rule(ADD_ASSOC),
        axiom_rule(ADD_COMM, ordered=True),
        _rotate_rule(ADD_ASSOC, ADD_COMM, "+", add),
        _cancel_pair_rule(),
    )


def _neg_add_rule() -> Rule:
    lhs = neg(add(_x, _y))
    rhs = add(neg(_x), neg(_y))
    suffix = add(_x, _y)
    left_zero = Trans(
        axiom_rule(ADD_COMM).instance({"x": lhs, "y": suffix}),
        axiom_rule(ADD_NEG).instance({"x": suffix}),
    )
    right_zero = prove_eq(Eq(add(rhs, suffix), ZERO), _additive_rules(), 10_000)
    proof = MP(_cancel(lhs, rhs, suffix), Trans(left_zero, Sym(right_zero)))
    return lemma_rule(Eq(lhs, rhs), proof)


def _neg_mul_right_rule() -> Rule:
    product = mul(_x, _y)
    signed = mul(_x, neg(_y))
    inverse_zero = Trans(
        Sym(axiom_rule(DIST_LEFT).instance({"x": _x, "y": _y, "z": neg(_y)})),
        Trans(
            Cong(
                "*",
                (Refl(_x), axiom_rule(ADD_NEG).instance({"x": _y})),
            ),
            _mul_zero_rule().instance({"x": _x}),
        ),
    )
    signed_zero = Trans(
        axiom_rule(ADD_COMM).instance({"x": signed, "y": product}),
        inverse_zero,
    )
    canonical_zero = Trans(
        axiom_rule(ADD_COMM).instance({"x": neg(product), "y": product}),
        axiom_rule(ADD_NEG).instance({"x": product}),
    )
    cancellable = Trans(signed_zero, Sym(canonical_zero))
    proof = MP(_cancel(signed, neg(product), product), cancellable)
    return lemma_rule(Eq(signed, neg(product)), proof)


def _neg_mul_left_rule() -> Rule:
    proof = Trans(
        axiom_rule(COMM).instance({"x": neg(_x), "y": _y}),
        Trans(
            _neg_mul_right_rule().instance({"x": _y, "y": _x}),
            Cong("neg", (axiom_rule(COMM).instance({"x": _y, "y": _x}),)),
        ),
    )
    return lemma_rule(Eq(mul(neg(_x), _y), neg(mul(_x, _y))), proof)


def _merge_rules() -> tuple[Rule, ...]:
    return (
        *_additive_rules(),
        _neg_add_rule(),
        _zero_mul_rule(),
        _mul_zero_rule(),
        axiom_rule(MUL_LEFT_ID),
        axiom_rule(MUL_RIGHT_ID),
        _neg_mul_left_rule(),
        _neg_mul_right_rule(),
        axiom_rule(DIST_LEFT),
        axiom_rule(DIST_RIGHT),
        axiom_rule(MUL_ASSOC),
        axiom_rule(COMM, ordered=True),
        _rotate_rule(MUL_ASSOC, COMM, "*", mul),
    )


COMM_RING_CONTEXT = AlgebraContext(
    zero=ZERO,
    one=ONE,
    add="+",
    mul="*",
    neg="neg",
    successor=None,
    coefficient_domain="integer",
    atoms=frozenset(),
    merge_rules=_merge_rules(),
    right_cancellation=ring_add_cancel_right(),
    rewrite_budget=200_000,
)


__all__ = ["COMM_RING_CONTEXT"]
