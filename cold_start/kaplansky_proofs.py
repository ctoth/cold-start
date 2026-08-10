"""Checked certificates for the SAT-found unit in the Promislow group ring.

The prover side is deliberately untrusted.  It derives a normal-form lemma
library from the two presentation relations and the four inverse axioms, then
uses those lemmas to certify the concrete products found by ``jc.kaplansky``.
No coordinate multiplication result is admitted as an axiom.
"""

from __future__ import annotations

import json
from collections.abc import Sequence
from functools import cache
from pathlib import Path
from typing import TypeAlias, cast

from .algebra import (
    ADD_ASSOC,
    ADD_COMM,
    ADD_ZERO,
    DIST_LEFT,
    DIST_RIGHT,
    MUL_ASSOC,
    MUL_LEFT_ID,
    MUL_RIGHT_ID,
)
from .algebra_proofs import rotate_rule, zero_add_rule
from .groupring2 import (
    A_INV,
    A_LEFT_INV,
    A_RIGHT_INV,
    B_INV,
    B_LEFT_INV,
    B_RIGHT_INV,
    CHAR2,
    GROUP_REL_A,
    GROUP_REL_B,
    A,
    B,
)
from .proof import Axiom, Cong, Pf, Refl, Sym, Trans, proof_size
from .syntax import Eq, Formula, Fun, Term, Var
from .tactics import (
    Rule,
    axiom_rule,
    lemma_rule,
    normalize,
    normalize_equality,
    prove_eq,
    rewrite_step,
)
from .vocabulary import ONE, ZERO, add, mul, product, summation

GElem: TypeAlias = tuple[int, int, int, int]


X = product(A, A)
X_INV = product(A_INV, A_INV)
Y = product(B, B)
Y_INV = product(B_INV, B_INV)
Z = product(A, B, A, B)
Z_INV = product(B_INV, A_INV, B_INV, A_INV)

_tail = Var("tail")


def _as_eq(formula: Formula) -> Eq:
    if type(formula) is not Eq:
        raise TypeError(f"expected an equation, got {formula!r}")
    return formula


def _cancel_tail_rule(
    generator: Term,
    inverse: Term,
    inverse_axiom: Formula,
) -> Rule:
    """inverse * (generator * tail) = tail."""
    goal = Eq(mul(inverse, mul(generator, _tail)), _tail)
    pf = Trans(
        Trans(
            Sym(
                axiom_rule(MUL_ASSOC).instance(
                    {"x": inverse, "y": generator, "z": _tail}
                )
            ),
            Cong("*", (Axiom(inverse_axiom), Refl(_tail))),
        ),
        axiom_rule(MUL_LEFT_ID).instance({"x": _tail}),
    )
    return lemma_rule(goal, pf)


@cache
def cancellation_rules() -> tuple[Rule, ...]:
    return (
        _cancel_tail_rule(A, A_INV, A_LEFT_INV),
        _cancel_tail_rule(A_INV, A, A_RIGHT_INV),
        _cancel_tail_rule(B, B_INV, B_LEFT_INV),
        _cancel_tail_rule(B_INV, B, B_RIGHT_INV),
    )


@cache
def _base_rules() -> tuple[Rule, ...]:
    return (
        axiom_rule(MUL_ASSOC),
        axiom_rule(MUL_LEFT_ID),
        axiom_rule(MUL_RIGHT_ID),
        axiom_rule(A_RIGHT_INV),
        axiom_rule(A_LEFT_INV),
        axiom_rule(B_RIGHT_INV),
        axiom_rule(B_LEFT_INV),
        *cancellation_rules(),
    )


def _normalize_congruence(
    source: Eq,
    proof: Pf,
    factor: Term,
    *,
    left: bool = False,
) -> tuple[Eq, Pf]:
    """Multiply an equality on one side, then expose its normal-form result."""
    raw = (
        Eq(mul(factor, source.lhs), mul(factor, source.rhs))
        if left
        else Eq(mul(source.lhs, factor), mul(source.rhs, factor))
    )
    congruence = (
        Cong("*", (Refl(factor), proof))
        if left
        else Cong("*", (proof, Refl(factor)))
    )
    return normalize_equality(raw, congruence, _base_rules(), 2_000)


def _sandwich(
    source: Eq,
    proof: Pf,
    left: Term,
    right: Term,
) -> tuple[Eq, Pf]:
    middle, middle_pf = _normalize_congruence(source, proof, left, left=True)
    return _normalize_congruence(middle, middle_pf, right)


def _flipped(equation: Eq, proof: Pf) -> tuple[Eq, Pf]:
    return Eq(equation.rhs, equation.lhs), Sym(proof)


def _tail_lift(equation: Eq, proof: Pf) -> Rule:
    """Lift ``lhs = rhs`` to a right-nested rule that preserves a tail."""
    raw = Eq(mul(equation.lhs, _tail), mul(equation.rhs, _tail))
    congruence = Cong("*", (proof, Refl(_tail)))
    lifted, pf = normalize_equality(raw, congruence, (axiom_rule(MUL_ASSOC),), 20)
    return lemma_rule(lifted, pf)


def _action_family(
    seed: tuple[Eq, Pf],
    normal: Term,
    normal_inverse: Term,
    section_inverse: Term,
) -> tuple[tuple[Eq, Pf], ...]:
    """From ``s*N = N^-1*s``, derive all sign choices for s and N."""
    positive, positive_pf = seed

    step, step_pf = _normalize_congruence(
        positive, positive_pf, normal_inverse
    )
    inverse_normal_raw, inverse_normal_raw_pf = _normalize_congruence(
        step, step_pf, normal, left=True
    )
    inverse_normal = _flipped(inverse_normal_raw, inverse_normal_raw_pf)

    step, step_pf = _normalize_congruence(
        positive, positive_pf, section_inverse, left=True
    )
    inverse_section_raw, inverse_section_raw_pf = _normalize_congruence(
        step, step_pf, section_inverse
    )
    inverse_section_inverse_normal = _flipped(
        inverse_section_raw, inverse_section_raw_pf
    )

    step, step_pf = _normalize_congruence(
        inverse_section_inverse_normal[0],
        inverse_section_inverse_normal[1],
        normal,
    )
    inverse_section_raw, inverse_section_raw_pf = _normalize_congruence(
        step, step_pf, normal_inverse, left=True
    )
    inverse_section = _flipped(inverse_section_raw, inverse_section_raw_pf)
    return seed, inverse_normal, inverse_section, inverse_section_inverse_normal


def _canonical_action_family(
    seed: tuple[Eq, Pf],
    normal: Term,
    normal_inverse: Term,
    section: Term,
    section_inverse: Term,
) -> tuple[tuple[Eq, Pf], ...]:
    """Expose the four action consequences with the normal factors grouped."""
    raw = _action_family(seed, normal, normal_inverse, section_inverse)
    rules = (*((lemma_rule(equation, proof)) for equation, proof in raw), *_base_rules())
    goals = (
        Eq(mul(section, normal), mul(normal_inverse, section)),
        Eq(mul(section, normal_inverse), mul(normal, section)),
        Eq(mul(section_inverse, normal), mul(normal_inverse, section_inverse)),
        Eq(mul(section_inverse, normal_inverse), mul(normal, section_inverse)),
    )
    return tuple((goal, prove_eq(goal, rules, 50_000)) for goal in goals)


def _trivial_action_family(
    section: Term,
    section_inverse: Term,
    normal: Term,
    normal_inverse: Term,
) -> tuple[tuple[Eq, Pf], ...]:
    goals = tuple(
        Eq(mul(s, n), mul(n, s))
        for s in (section, section_inverse)
        for n in (normal, normal_inverse)
    )
    return tuple((goal, prove_eq(goal, _base_rules(), 20_000)) for goal in goals)


@cache
def _xy_seed_actions() -> tuple[tuple[Eq, Pf], tuple[Eq, Pf]]:
    """Derive A*Y=Y^-1*A and B*X=X^-1*B from the presentation."""
    rel_b = _as_eq(GROUP_REL_B)
    rel_a = _as_eq(GROUP_REL_A)
    step, step_pf = _normalize_congruence(rel_b, Axiom(rel_b), Y)
    a_y = _normalize_congruence(step, step_pf, Y_INV, left=True)

    step, step_pf = _normalize_congruence(rel_a, Axiom(rel_a), X)
    b_x = _normalize_congruence(step, step_pf, X_INV, left=True)
    return a_y, b_x


@cache
def _z_seed_actions() -> tuple[tuple[Eq, Pf], tuple[Eq, Pf]]:
    a_y, _ = _xy_seed_actions()
    rel_b = _as_eq(GROUP_REL_B)
    rel_a = _as_eq(GROUP_REL_A)

    step, step_pf = _normalize_congruence(
        rel_b, Axiom(rel_b), A_INV, left=True
    )
    a_inv_y = _normalize_congruence(step, step_pf, A_INV)
    step, step_pf = _normalize_congruence(
        rel_a, Axiom(rel_a), B_INV, left=True
    )
    b_inv_x = _normalize_congruence(step, step_pf, B_INV)

    b_a_b = _sandwich(a_y[0], a_y[1], B, B_INV)
    b_a_inv_b = _sandwich(a_inv_y[0], a_inv_y[1], B, B_INV)
    a_b_inv_a = _sandwich(b_inv_x[0], b_inv_x[1], A, A_INV)

    rel_a_tail = _tail_lift(rel_a, Axiom(rel_a))
    b_a_inv_b_tail = _tail_lift(*b_a_inv_b)
    a_z_goal = Eq(mul(A, Z), mul(Z_INV, A))
    a_z_pf = prove_eq(
        a_z_goal,
        (rel_a_tail, lemma_rule(*b_a_inv_b), b_a_inv_b_tail, *_base_rules()),
        20_000,
    )

    b_a_b_tail = _tail_lift(*b_a_b)
    a_b_inv_a_tail = _tail_lift(*a_b_inv_a)
    b_z_goal = Eq(mul(B, Z), mul(Z_INV, B))
    b_z_pf = prove_eq(
        b_z_goal,
        (
            lemma_rule(*b_a_b),
            b_a_b_tail,
            lemma_rule(*a_b_inv_a),
            a_b_inv_a_tail,
            *_base_rules(),
        ),
        20_000,
    )
    return (a_z_goal, a_z_pf), (b_z_goal, b_z_pf)


@cache
def action_lemmas() -> tuple[Rule, ...]:
    """All signed generator actions on X, Y and Z, derived from the axioms."""
    a_y, b_x = _xy_seed_actions()
    a_z, b_z = _z_seed_actions()
    pairs = (
        *_trivial_action_family(A, A_INV, X, X_INV),
        *_canonical_action_family(a_y, Y, Y_INV, A, A_INV),
        *_canonical_action_family(b_x, X, X_INV, B, B_INV),
        *_trivial_action_family(B, B_INV, Y, Y_INV),
        *_canonical_action_family(a_z, Z, Z_INV, A, A_INV),
        *_canonical_action_family(b_z, Z, Z_INV, B, B_INV),
    )
    return tuple(lemma_rule(equation, proof) for equation, proof in pairs)


def _prove_to(goal: Eq, rules: Sequence[Rule], budget: int = 20_000) -> Pf:
    """Rewrite the left side and stop as soon as the exact target is reached."""
    current = goal.lhs
    proof: Pf = Refl(current)
    for _ in range(budget + 1):
        if current == goal.rhs:
            return proof
        step = rewrite_step(current, rules)
        if step is None:
            break
        current, step_pf = step
        proof = Trans(proof, step_pf)
    raise ValueError(f"could not rewrite {goal.lhs!r} to {goal.rhs!r}; got {current!r}")


@cache
def commutation_lemmas() -> tuple[Rule, ...]:
    """Pairwise signed commutation of X, Y and Z."""
    actions = action_lemmas()
    specs = (
        (X, A, Y, Y_INV),
        (X_INV, A_INV, Y, Y_INV),
        (X, A, Z, Z_INV),
        (X_INV, A_INV, Z, Z_INV),
        (Y, B, Z, Z_INV),
        (Y_INV, B_INV, Z, Z_INV),
    )
    out: list[Rule] = []
    for left_normal, section, right_normal, right_inverse in specs:
        direct_rules: list[Rule] = []
        for rule in actions:
            lhs = rule.eq.lhs
            if type(lhs) is not Fun or lhs.name != "*" or lhs.args[0] != section:
                continue
            operand = lhs.args[1]
            if operand in (right_normal, right_inverse):
                direct_rules.append(rule)
        section_rules = (
            *direct_rules,
            *(_tail_lift(rule.eq, rule.proof) for rule in direct_rules),
        )
        for right in (right_normal, right_inverse):
            goal = Eq(mul(left_normal, right), mul(right, left_normal))
            proof = prove_eq(
                goal,
                (*section_rules, axiom_rule(MUL_ASSOC)),
                20_000,
            )
            out.append(lemma_rule(goal, proof))
    return tuple(out)


@cache
def lemma_library() -> tuple[Rule, ...]:
    return (*cancellation_rules(), *action_lemmas(), *commutation_lemmas())


def _factor_product(factors: Sequence[Term]) -> Term:
    if not factors:
        return ONE
    return product(*factors)


_SECTION = (ONE, A, B, product(A, B))


def group_factors(g: GElem) -> tuple[Term, ...]:
    """Canonical X^i Y^j Z^k w factors, preserving each macro as a subtree."""
    i, j, k, w = g
    if w not in range(4):
        raise ValueError(f"invalid transversal label: {w}")
    factors: list[Term] = []
    for exponent, positive, negative in (
        (i, X, X_INV),
        (j, Y, Y_INV),
        (k, Z, Z_INV),
    ):
        factors.extend([positive if exponent > 0 else negative] * abs(exponent))
    if w:
        factors.append(_SECTION[w])
    return tuple(factors)


def group_term(g: GElem) -> Term:
    return _factor_product(group_factors(g))


_COCYCLE: tuple[tuple[tuple[int, int, int], ...], ...] = (
    ((0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)),
    ((0, 0, 0), (1, 0, 0), (0, 0, 0), (1, 0, 0)),
    ((0, 0, 0), (-1, 1, -1), (0, 1, 0), (-1, 0, -1)),
    ((0, 0, 0), (0, -1, 1), (0, -1, 0), (0, 0, 1)),
)


def _coordinate_action(w: int, n: tuple[int, int, int]) -> tuple[int, int, int]:
    i, j, k = n
    signs = ((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1))[w]
    return signs[0] * i, signs[1] * j, signs[2] * k


def coordinate_product(g: GElem, h: GElem) -> GElem:
    """Untrusted target selection; the proof checker validates every result."""
    i, j, k, w = g
    ai, aj, ak = _coordinate_action(w, h[:3])
    ci, cj, ck = _COCYCLE[w][h[3]]
    return i + ai + ci, j + aj + cj, k + ak + ck, w ^ h[3]


@cache
def _section_action_rules() -> tuple[Rule, ...]:
    """Actions of A, B and AB on signed normal generators."""
    direct_actions = action_lemmas()

    def action(section: Term, normal: Term) -> Rule:
        for rule in direct_actions:
            lhs = rule.eq.lhs
            if (
                type(lhs) is Fun
                and lhs.name == "*"
                and lhs.args == (section, normal)
            ):
                return rule
        raise ValueError(f"missing action for {section!r} on {normal!r}")

    ab = _SECTION[3]
    ab_specs = (
        (X, X_INV, X_INV),
        (X_INV, X, X),
        (Y, Y, Y_INV),
        (Y_INV, Y_INV, Y),
        (Z, Z_INV, Z),
        (Z_INV, Z, Z_INV),
    )
    ab_rules: list[Rule] = []
    for normal, after_b, image in ab_specs:
        goal = Eq(mul(ab, normal), mul(image, ab))
        b_rule = action(B, normal)
        a_rule = action(A, after_b)
        assoc = axiom_rule(MUL_ASSOC)
        target_nf, target_pf = normalize(goal.rhs, (assoc,), 100)
        left_pf = _prove_to(
            Eq(goal.lhs, target_nf),
            (
                b_rule,
                _tail_lift(b_rule.eq, b_rule.proof),
                a_rule,
                _tail_lift(a_rule.eq, a_rule.proof),
                assoc,
            ),
            50_000,
        )
        proof = Trans(left_pf, Sym(target_pf))
        ab_direct = lemma_rule(goal, proof)
        ab_rules.append(ab_direct)
    direct = (*direct_actions, *ab_rules)
    tails: list[Rule] = []
    for rule in direct:
        lhs = rule.eq.lhs
        rhs = rule.eq.rhs
        if type(lhs) is not Fun or type(rhs) is not Fun:
            raise TypeError("action equations must be binary products")
        tails.append(_factor_tail_lift(rule, lhs.args, rhs.args))
    return (*direct, *tails)


def _section_goal(left: int, right: int) -> Eq:
    c = _COCYCLE[left][right]
    return Eq(
        mul(_SECTION[left], _SECTION[right]),
        group_term((*c, left ^ right)),
    )


def _commutation_collection_rules() -> tuple[Rule, ...]:
    out: list[Rule] = []
    for rule in commutation_lemmas():
        oriented = rule.flipped
        lhs = oriented.eq.lhs
        rhs = oriented.eq.rhs
        if type(lhs) is not Fun or type(rhs) is not Fun:
            raise TypeError("commutation equations must be binary products")
        out.extend((oriented, _factor_tail_lift(oriented, lhs.args, rhs.args)))
    return tuple(out)


@cache
def _section_product_rules() -> tuple[Rule, ...]:
    """The 16 transversal products, in an acyclic proof dependency order."""
    special = {(2, 1), (2, 3), (3, 1)}
    known: dict[tuple[int, int], Rule] = {}
    simple_rules = (*action_lemmas(), *_base_rules())
    for left in range(4):
        for right in range(4):
            if (left, right) in special:
                continue
            goal = _section_goal(left, right)
            known[left, right] = lemma_rule(
                goal,
                prove_eq(goal, simple_rules, 50_000),
            )

    # B*X=X^-1*B, followed by A^-1 on the right, gives the only hard pair B*A.
    b_x = next(rule for rule in action_lemmas() if rule.eq.lhs == mul(B, X))
    ba_simple, ba_simple_pf = _normalize_congruence(b_x.eq, b_x.proof, A_INV)
    ba_goal = _section_goal(2, 1)
    ba_rule = lemma_rule(
        ba_goal,
        prove_eq(
            ba_goal,
            (lemma_rule(ba_simple, ba_simple_pf), *_base_rules()),
            20_000,
        ),
    )
    known[2, 1] = ba_rule

    factor_rules = (
        ba_rule,
        _factor_tail_lift(
            ba_rule,
            (_SECTION[2], _SECTION[1]),
            group_factors((*_COCYCLE[2][1], 3)),
        ),
        *(rule for rule in known.values() if rule.eq.lhs != rule.eq.rhs),
        *_macro_cancellation_rules(),
        *_commutation_collection_rules(),
        axiom_rule(MUL_LEFT_ID),
        axiom_rule(MUL_RIGHT_ID),
    )
    b_ab_goal = _section_goal(2, 3)
    known[2, 3] = lemma_rule(
        b_ab_goal,
        _prove_to(b_ab_goal, factor_rules, 50),
    )

    a_collection: list[Rule] = []
    for rule in action_lemmas():
        lhs = rule.eq.lhs
        rhs = rule.eq.rhs
        if (
            type(lhs) is Fun
            and type(rhs) is Fun
            and lhs.name == "*"
            and lhs.args[0] == A
            and lhs.args[1] in (X_INV, Y, Z_INV)
        ):
            a_collection.extend((rule, _factor_tail_lift(rule, lhs.args, rhs.args)))

    ab_a_goal = _section_goal(3, 1)
    ba_factors = group_factors((*_COCYCLE[2][1], 3))
    stage1 = Eq(ab_a_goal.lhs, _factor_product((A, *ba_factors)))
    stage1_pf = _prove_to(
        stage1,
        (ba_rule, axiom_rule(MUL_ASSOC)),
        20,
    )

    stage2_target = _factor_product((X_INV, Y_INV, Z, A, _SECTION[3]))
    stage2 = Eq(stage1.rhs, stage2_target)
    stage2_pf = _prove_to(stage2, tuple(a_collection), 20)

    a_ab = known[1, 3]
    stage3_target = _factor_product((X_INV, Y_INV, Z, X, B))
    stage3 = Eq(stage2.rhs, stage3_target)
    stage3_pf = _prove_to(stage3, (a_ab,), 10)

    commutations = _commutation_collection_rules()
    z_x = tuple(rule for rule in commutations if rule.eq.lhs == mul(Z, mul(X, _tail)))
    y_x = tuple(
        rule for rule in commutations if rule.eq.lhs == mul(Y_INV, mul(X, _tail))
    )
    stage4_target = _factor_product((X_INV, X, Y_INV, Z, B))
    stage4 = Eq(stage3.rhs, stage4_target)
    stage4_pf = _prove_to(stage4, (*z_x, *y_x), 10)

    cancellations = _macro_cancellation_rules()
    x_cancel = tuple(
        rule
        for rule in cancellations
        if rule.eq.lhs == mul(X_INV, mul(X, _tail))
    )
    stage5 = Eq(stage4.rhs, ab_a_goal.rhs)
    stage5_pf = _prove_to(stage5, x_cancel, 10)
    known[3, 1] = lemma_rule(
        ab_a_goal,
        Trans(
            stage1_pf,
            Trans(stage2_pf, Trans(stage3_pf, Trans(stage4_pf, stage5_pf))),
        ),
    )

    return tuple(known[left, right] for left in range(4) for right in range(4))


@cache
def _macro_cancellation_rules() -> tuple[Rule, ...]:
    out: list[Rule] = []
    proof_rules = _base_rules()
    for positive, negative in ((X, X_INV), (Y, Y_INV), (Z, Z_INV)):
        for left, right in ((positive, negative), (negative, positive)):
            goal = Eq(mul(left, right), ONE)
            proof = prove_eq(goal, proof_rules, 20_000)
            direct = lemma_rule(goal, proof)
            out.extend((direct, _factor_tail_lift(direct, (left, right), ())))
    return tuple(out)


def _concatenation_proof(
    left: tuple[Term, ...],
    right: tuple[Term, ...],
) -> Pf:
    """Reassociate ``product(left) * product(right)`` to one factor list."""
    left_term = _factor_product(left)
    right_term = _factor_product(right)
    if not left:
        return axiom_rule(MUL_LEFT_ID).instance({"x": right_term})
    if not right:
        return axiom_rule(MUL_RIGHT_ID).instance({"x": left_term})
    if len(left) == 1:
        return Refl(mul(left[0], right_term))
    first, rest = left[0], left[1:]
    return Trans(
        axiom_rule(MUL_ASSOC).instance(
            {"x": first, "y": _factor_product(rest), "z": right_term}
        ),
        Cong("*", (Refl(first), _concatenation_proof(rest, right))),
    )


def _factor_tail_lift(
    rule: Rule,
    left: Sequence[Term],
    right: Sequence[Term],
) -> Rule:
    """Lift a ground factor rewrite without flattening any factor subtree."""
    raw = Cong("*", (rule.proof, Refl(_tail)))
    left_pf = _concatenation_proof(tuple(left), (_tail,))
    right_pf = _concatenation_proof(tuple(right), (_tail,))
    goal = Eq(
        _factor_product((*left, _tail)),
        _factor_product((*right, _tail)),
    )
    return lemma_rule(goal, Trans(Sym(left_pf), Trans(raw, right_pf)))


def _apply_factor_rule(
    factors: tuple[Term, ...],
    index: int,
    left: tuple[Term, ...],
    right: tuple[Term, ...],
    rule: Rule,
) -> tuple[tuple[Term, ...], Pf]:
    """Apply one ground rule at an exact factor index, never inside a macro."""
    if factors[index : index + len(left)] != left:
        raise ValueError(f"factor rule does not match at index {index}: {rule.eq!r}")
    prefix = factors[:index]
    suffix = factors[index + len(left) :]
    if suffix:
        tail = _factor_product(suffix)
        lifted = _factor_tail_lift(rule, left, right)
        step_pf = lifted.instance({_tail.name: tail})
        raw_left = _factor_product((*left, tail))
        raw_right = _factor_product((*right, tail))
    else:
        step_pf = rule.proof
        raw_left = rule.eq.lhs
        raw_right = rule.eq.rhs
    for factor in reversed(prefix):
        step_pf = Cong("*", (Refl(factor), step_pf))
        raw_left = mul(factor, raw_left)
        raw_right = mul(factor, raw_right)

    source = _factor_product(factors)
    if raw_left != source:
        raise ValueError(f"factor lifting changed its source: {raw_left!r} != {source!r}")
    result = (*prefix, *right, *suffix)
    target = _factor_product(result)
    if raw_right != target:
        cleaned, cleanup_pf = normalize(
            raw_right,
            (axiom_rule(MUL_LEFT_ID), axiom_rule(MUL_RIGHT_ID)),
            len(prefix) + 1,
        )
        if cleaned != target:
            raise ValueError(
                f"factor lifting changed its target: {cleaned!r} != {target!r}"
            )
        step_pf = Trans(step_pf, cleanup_pf)
    return result, step_pf


def _binary_rule(rules: Sequence[Rule], left: Term, right: Term) -> Rule:
    lhs = mul(left, right)
    for rule in rules:
        if rule.eq.lhs == lhs:
            return rule
    raise ValueError(f"missing factor rule for {lhs!r}")


def _normal_kind(factor: Term) -> tuple[int, int]:
    for axis, positive, negative in (
        (0, X, X_INV),
        (1, Y, Y_INV),
        (2, Z, Z_INV),
    ):
        if factor == positive:
            return axis, 1
        if factor == negative:
            return axis, -1
    raise ValueError(f"not a canonical normal factor: {factor!r}")


@cache
def ground_multiplication_lemma(g: GElem, h: GElem) -> Rule:
    """Prove one concrete canonical-word multiplication equation."""
    left_factors = group_factors(g)
    right_factors = group_factors(h)
    source = mul(group_term(g), group_term(h))
    target = group_term(coordinate_product(g, h))
    concat_pf = _concatenation_proof(left_factors, right_factors)
    factors = (*left_factors, *right_factors)
    proof: Pf = concat_pf

    left_normal = group_factors((*g[:3], 0))
    right_normal = group_factors((*h[:3], 0))
    section_index = len(left_normal)
    if g[3]:
        section = _SECTION[g[3]]
        for normal in right_normal:
            action = _binary_rule(_section_action_rules(), section, normal)
            rhs = action.eq.rhs
            if type(rhs) is not Fun or rhs.name != "*" or rhs.args[1] != section:
                raise ValueError(f"malformed section action: {action.eq!r}")
            factors, step_pf = _apply_factor_rule(
                factors,
                section_index,
                (section, normal),
                rhs.args,
                action,
            )
            proof = Trans(proof, step_pf)
            section_index += 1

    if g[3] and h[3]:
        section_rule = _section_product_rules()[4 * g[3] + h[3]]
        section_right = group_factors(
            (*_COCYCLE[g[3]][h[3]], g[3] ^ h[3])
        )
        factors, step_pf = _apply_factor_rule(
            factors,
            section_index,
            (_SECTION[g[3]], _SECTION[h[3]]),
            section_right,
            section_rule,
        )
        proof = Trans(proof, step_pf)

    result_section = g[3] ^ h[3]
    normal_end = len(factors) - bool(result_section)
    while True:
        for index in range(normal_end - 1):
            left_kind = _normal_kind(factors[index])
            right_kind = _normal_kind(factors[index + 1])
            if left_kind[0] == right_kind[0] and left_kind[1] != right_kind[1]:
                cancellation = _binary_rule(
                    _macro_cancellation_rules(),
                    factors[index],
                    factors[index + 1],
                )
                factors, step_pf = _apply_factor_rule(
                    factors,
                    index,
                    (factors[index], factors[index + 1]),
                    (),
                    cancellation,
                )
                normal_end -= 2
                proof = Trans(proof, step_pf)
                break
            if left_kind[0] > right_kind[0]:
                commutation = _binary_rule(
                    _commutation_collection_rules(),
                    factors[index],
                    factors[index + 1],
                )
                replacement = (factors[index + 1], factors[index])
                factors, step_pf = _apply_factor_rule(
                    factors,
                    index,
                    (replacement[1], replacement[0]),
                    replacement,
                    commutation,
                )
                proof = Trans(proof, step_pf)
                break
        else:
            break

    normal = _factor_product(factors)
    if normal != target:
        raise ValueError(
            f"collector disagrees on {g!r} * {h!r}: {normal!r} != {target!r}"
        )
    return lemma_rule(Eq(source, target), proof)


def witness_coordinates() -> tuple[tuple[GElem, ...], tuple[GElem, ...]]:
    path = Path(__file__).resolve().parents[2] / "jc" / "data" / "kaplansky_unit.json"
    raw_payload = cast(object, json.loads(path.read_text(encoding="utf-8")))
    if type(raw_payload) is not dict:
        raise ValueError("Kaplansky witness must be a JSON object")
    payload = cast(dict[object, object], raw_payload)

    def decode(name: str) -> tuple[GElem, ...]:
        raw_rows = payload.get(name)
        if type(raw_rows) is not list:
            raise ValueError(f"{name} support must be a list")
        rows = cast(list[object], raw_rows)
        out: list[GElem] = []
        for raw_row in rows:
            if type(raw_row) is not list:
                raise ValueError(f"malformed {name} coordinate: {raw_row!r}")
            row = cast(list[object], raw_row)
            if len(row) != 4 or any(type(value) is not int for value in row):
                raise ValueError(f"malformed {name} coordinate: {row!r}")
            out.append(cast(GElem, tuple(row)))
        return tuple(out)

    return decode("u"), decode("v")


def ground_multiplication_lemmas(
    left: Sequence[GElem],
    right: Sequence[GElem],
) -> tuple[Rule, ...]:
    return tuple(ground_multiplication_lemma(g, h) for g in left for h in right)


_add_x, _add_y = Var("add_x"), Var("add_y")


@cache
def _cancel_pair_rule() -> Rule:
    """x+(x+y) = y, by associativity, characteristic two, and additive zero."""
    proof = Trans(
        Trans(
            Sym(
                axiom_rule(ADD_ASSOC).instance(
                    {"x": _add_x, "y": _add_x, "z": _add_y}
                )
            ),
            Cong(
                "+",
                (
                    axiom_rule(CHAR2).instance({"x": _add_x}),
                    Refl(_add_y),
                ),
            ),
        ),
        Trans(
            axiom_rule(ADD_COMM).instance({"x": ZERO, "y": _add_y}),
            axiom_rule(ADD_ZERO).instance({"x": _add_y}),
        ),
    )
    return lemma_rule(
        Eq(add(_add_x, add(_add_x, _add_y)), _add_y),
        proof,
    )


@cache
def _additive_rules() -> tuple[Rule, ...]:
    """Canonical additive normalization and cancellation in characteristic two.

    Associativity, ordered commutativity and the shared rotation rule sort a
    sum; CHAR2 and the cancellation pair it proves collapse duplicate terms --
    this kit's inverse recipe is CHAR2, never ADD_NEG, which the theory does
    not have."""
    return (
        axiom_rule(ADD_ASSOC),
        axiom_rule(ADD_COMM, ordered=True),
        rotate_rule(ADD_ASSOC, ADD_COMM, "+", add),
        axiom_rule(CHAR2),
        _cancel_pair_rule(),
        axiom_rule(ADD_ZERO),
        zero_add_rule(),
    )


@cache
def u_term() -> Term:
    u, _ = witness_coordinates()
    return summation(*(group_term(g) for g in u))


@cache
def v_term() -> Term:
    _, v = witness_coordinates()
    return summation(*(group_term(g) for g in v))


@cache
def unit_product_statements() -> tuple[Eq, Eq]:
    return Eq(mul(u_term(), v_term()), ONE), Eq(mul(v_term(), u_term()), ONE)


@cache
def _row_product_lemma(
    left: GElem,
    right: tuple[GElem, ...],
    budget: int,
) -> Rule:
    """Expand and reduce one group word times one 21-term ring element."""
    source = mul(group_term(left), summation(*(group_term(g) for g in right)))
    products = tuple(mul(group_term(left), group_term(g)) for g in right)
    expanded = summation(*products)
    expanded_term, expansion_pf = normalize(
        source,
        (axiom_rule(DIST_LEFT),),
        len(right),
    )
    if expanded_term != expanded:
        raise ValueError(
            f"column expansion disagrees: {expanded_term!r} != {expanded!r}"
        )

    ground = ground_multiplication_lemmas((left,), right)

    def map_products(index: int) -> Pf:
        if index == len(ground) - 1:
            return ground[index].proof
        return Cong("+", (ground[index].proof, map_products(index + 1)))

    mapped = summation(*(rule.eq.rhs for rule in ground))
    mapping_pf = map_products(0)
    normal, normal_pf = normalize(mapped, _additive_rules(), budget)
    proof = Trans(expansion_pf, Trans(mapping_pf, normal_pf))
    return lemma_rule(Eq(source, normal), proof)


def _staged_product_proof(
    statement: Eq,
    left: tuple[GElem, ...],
    right: tuple[GElem, ...],
    budget: int,
) -> Pf:
    """Reduce 21 rows, then combine their normal forms from right to left."""
    rows = tuple(
        mul(group_term(g), summation(*(group_term(h) for h in right))) for g in left
    )
    expanded = summation(*rows)
    expanded_term, expansion_pf = normalize(
        statement.lhs,
        (axiom_rule(DIST_RIGHT),),
        len(left),
    )
    if expanded_term != expanded:
        raise ValueError(
            f"row expansion disagrees: {expanded_term!r} != {expanded!r}"
        )

    row_rules = tuple(_row_product_lemma(g, right, budget) for g in left)

    def combine(index: int) -> tuple[Term, Pf]:
        row = row_rules[index]
        if index == len(row_rules) - 1:
            return row.eq.rhs, row.proof
        tail_normal, tail_pf = combine(index + 1)
        joined = Cong("+", (row.proof, tail_pf))
        raw = add(row.eq.rhs, tail_normal)
        normal, normal_pf = normalize(raw, _additive_rules(), budget)
        return normal, Trans(joined, normal_pf)

    normal, rows_pf = combine(0)
    if normal != statement.rhs:
        raise ValueError(
            f"staged product normalization disagrees: {normal!r} != {statement.rhs!r}"
        )
    return Trans(expansion_pf, rows_pf)


@cache
def uv_product_proof(budget: int = 200_000) -> Pf:
    u, v = witness_coordinates()
    uv_statement, _ = unit_product_statements()
    return _staged_product_proof(uv_statement, u, v, budget)


@cache
def vu_product_proof(budget: int = 200_000) -> Pf:
    u, v = witness_coordinates()
    _, vu_statement = unit_product_statements()
    return _staged_product_proof(vu_statement, v, u, budget)


def unit_product_proofs(budget: int = 200_000) -> tuple[Pf, Pf]:
    """Checked certificates of u*v=1 and v*u=1 in the presented group ring."""
    return uv_product_proof(budget), vu_product_proof(budget)


def main() -> None:
    """Rebuild, re-check, and toll every exported certificate theorem."""
    from .checker import check
    from .groupring2 import GROUP_RING_P2
    from .sequent import Sequent

    uv_statement, vu_statement = unit_product_statements()
    uv_proof, vu_proof = unit_product_proofs()
    groups: tuple[tuple[str, tuple[tuple[Pf, Formula], ...]], ...] = (
        (
            "normal-form lemmas (40)",
            tuple((rule.proof, rule.eq) for rule in lemma_library()),
        ),
        ("u*v = 1 (441 products)", ((uv_proof, uv_statement),)),
        ("v*u = 1 (441 products)", ((vu_proof, vu_statement),)),
    )
    total = 0
    for label, theorems in groups:
        toll = 0
        for proof, statement in theorems:
            expected = Sequent(frozenset(), statement)
            if check(proof, GROUP_RING_P2) != expected:
                raise AssertionError(f"checker conclusion drifted for {label}")
            toll += proof_size(proof)
        total += toll
        print(f"{label:<30} toll {toll:>12,}")
    print(f"{'TOTAL':<30} toll {total:>12,}")


if __name__ == "__main__":
    main()


__all__ = [
    "X",
    "Y",
    "Z",
    "ground_multiplication_lemmas",
    "group_term",
    "lemma_library",
    "unit_product_proofs",
    "unit_product_statements",
    "u_term",
    "uv_product_proof",
    "v_term",
    "witness_coordinates",
]
