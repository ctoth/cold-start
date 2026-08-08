"""Derived characteristic-2 ring lemmas and sparse-normalizer context.

Everything here is an untrusted proof recipe. ``DIFF_RING_2_CONTEXT`` can cite
the characteristic-two axiom, but only the ordinary checker under a theory that
actually contains that axiom can accept the emitted proof.
"""

from __future__ import annotations

from collections.abc import Callable

from .algebra import (
    ADD_ASSOC,
    ADD_COMM,
    ADD_ZERO,
    COMM,
    DIST_LEFT,
    DIST_RIGHT,
    MUL_ASSOC,
    MUL_LEFT_ID,
    MUL_RIGHT_ID,
)
from .diffring2 import CHAR2, D_AXIOMS, GENERATORS, dx, dy, dz
from .proof import Cong, Pf, Refl, Sym, Trans
from .ring_nf import AlgebraContext
from .syntax import Eq, Formula, Term, Var
from .tactics import Rule, axiom_rule, lemma_rule
from .vocabulary import ONE, ZERO, add, mul

_a = Var("a")
_x, _y, _z = Var("x"), Var("y"), Var("z")


def zero_mul_rule() -> Rule:
    """Prove ``0*a = 0`` without subtraction."""
    char2_at_one = axiom_rule(CHAR2).instance({"x": ONE})
    mul_id_at_a = axiom_rule(MUL_LEFT_ID).instance({"x": _a})
    proof = Trans(
        Trans(
            Trans(
                Cong("*", (Sym(char2_at_one), Refl(_a))),
                axiom_rule(DIST_RIGHT).instance({"x": ONE, "y": ONE, "z": _a}),
            ),
            Cong("+", (mul_id_at_a, mul_id_at_a)),
        ),
        axiom_rule(CHAR2).instance({"x": _a}),
    )
    return lemma_rule(Eq(mul(ZERO, _a), ZERO), proof)


def mul_zero_rule() -> Rule:
    proof = Trans(
        axiom_rule(COMM).instance({"x": _a, "y": ZERO}),
        zero_mul_rule().proof,
    )
    return lemma_rule(Eq(mul(_a, ZERO), ZERO), proof)


def zero_add_rule() -> Rule:
    proof = Trans(
        axiom_rule(ADD_COMM).instance({"x": ZERO, "y": _a}),
        axiom_rule(ADD_ZERO).instance({"x": _a}),
    )
    return lemma_rule(Eq(add(ZERO, _a), _a), proof)


def _rotate_rule(
    assoc: Formula,
    comm: Formula,
    name: str,
    op: Callable[[Term, Term], Term],
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
        Eq(op(_x, op(_y, _z)), op(_y, op(_x, _z))),
        proof,
        frozenset({"x", "y", "z"}),
        ordered=True,
    )


def add_rotate_rule() -> Rule:
    return _rotate_rule(ADD_ASSOC, ADD_COMM, "+", add)


def mul_rotate_rule() -> Rule:
    return _rotate_rule(MUL_ASSOC, COMM, "*", mul)


def cancel_pair_rule() -> Rule:
    proof = Trans(
        Trans(
            Sym(axiom_rule(ADD_ASSOC).instance({"x": _x, "y": _x, "z": _y})),
            Cong("+", (axiom_rule(CHAR2).instance({"x": _x}), Refl(_y))),
        ),
        Trans(
            axiom_rule(ADD_COMM).instance({"x": ZERO, "y": _y}),
            axiom_rule(ADD_ZERO).instance({"x": _y}),
        ),
    )
    return lemma_rule(Eq(add(_x, add(_x, _y)), _y), proof)


def evaluation_rules() -> tuple[Rule, ...]:
    """Local proved simplifications for zero, one, and duplicate bits."""
    return (
        zero_mul_rule(),
        mul_zero_rule(),
        axiom_rule(MUL_LEFT_ID),
        axiom_rule(MUL_RIGHT_ID),
        zero_add_rule(),
        axiom_rule(ADD_ZERO),
        axiom_rule(CHAR2),
    )


def derivation_zero_proofs() -> tuple[Pf, ...]:
    """Prove D(0)=0 for all three registered derivations."""
    out: list[Pf] = []
    for index, derivation in enumerate((dx, dy, dz)):
        name = ("DX", "DY", "DZ")[index]
        additivity = D_AXIOMS[5 * index]
        out.append(
            Trans(
                Trans(
                    Cong(name, (Sym(axiom_rule(ADD_ZERO).instance({"x": ZERO})),)),
                    axiom_rule(additivity).instance({"x": ZERO, "y": ZERO}),
                ),
                axiom_rule(CHAR2).instance({"x": derivation(ZERO)}),
            )
        )
    return tuple(out)


def derivation_one_proofs() -> tuple[Pf, ...]:
    """Prove D(1)=0 for all three registered derivations."""
    out: list[Pf] = []
    for index, derivation in enumerate((dx, dy, dz)):
        name = ("DX", "DY", "DZ")[index]
        leibniz = D_AXIOMS[5 * index + 1]
        d1 = derivation(ONE)
        out.append(
            Trans(
                Trans(
                    Trans(
                        Cong(
                            name,
                            (Sym(axiom_rule(MUL_LEFT_ID).instance({"x": ONE})),),
                        ),
                        axiom_rule(leibniz).instance({"x": ONE, "y": ONE}),
                    ),
                    Cong(
                        "+",
                        (
                            axiom_rule(MUL_RIGHT_ID).instance({"x": d1}),
                            axiom_rule(MUL_LEFT_ID).instance({"x": d1}),
                        ),
                    ),
                ),
                axiom_rule(CHAR2).instance({"x": d1}),
            )
        )
    return tuple(out)


def _merge_rules() -> tuple[Rule, ...]:
    """Private proof recipes used only to justify sparse fold merge steps."""
    return (
        *evaluation_rules(),
        axiom_rule(DIST_LEFT),
        axiom_rule(DIST_RIGHT),
        axiom_rule(ADD_ASSOC),
        axiom_rule(MUL_ASSOC),
        axiom_rule(ADD_COMM, ordered=True),
        axiom_rule(COMM, ordered=True),
        add_rotate_rule(),
        mul_rotate_rule(),
        cancel_pair_rule(),
    )


DIFF_RING_2_CONTEXT = AlgebraContext(
    zero="0",
    one="1",
    add="+",
    mul="*",
    neg=None,
    coefficient_domain="mod2",
    atoms=frozenset(GENERATORS),
    merge_rules=_merge_rules(),
    rewrite_budget=200_000,
)


__all__ = [
    "DIFF_RING_2_CONTEXT",
    "add_rotate_rule",
    "cancel_pair_rule",
    "derivation_one_proofs",
    "derivation_zero_proofs",
    "evaluation_rules",
    "mul_rotate_rule",
    "mul_zero_rule",
    "zero_add_rule",
    "zero_mul_rule",
]
