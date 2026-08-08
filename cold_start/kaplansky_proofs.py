"""Checked certificates for the SAT-found unit in the Promislow group ring.

The prover side is deliberately untrusted.  It derives a normal-form lemma
library from the two presentation relations and the four inverse axioms, then
uses those lemmas to certify the concrete products found by ``jc.kaplansky``.
No coordinate multiplication result is admitted as an axiom.
"""

from __future__ import annotations

from functools import reduce

from .algebra import MUL_ASSOC, MUL_LEFT_ID, MUL_RIGHT_ID
from .groupring2 import (
    A_INV,
    A_LEFT_INV,
    A_RIGHT_INV,
    B_INV,
    B_LEFT_INV,
    B_RIGHT_INV,
    GROUP_REL_A,
    GROUP_REL_B,
    A,
    B,
)
from .proof import Axiom, Cong, Pf, Refl, Sym, Trans
from .syntax import Eq, Formula, Fun, Term, Var
from .tactics import Rule, axiom_rule, lemma_rule, normalize, prove_eq
from .vocabulary import mul


def _m(*factors: Term) -> Term:
    """A right-nested nonempty product."""
    return reduce(lambda acc, factor: mul(factor, acc), reversed(factors[:-1]), factors[-1])


X = _m(A, A)
X_INV = _m(A_INV, A_INV)
Y = _m(B, B)
Y_INV = _m(B_INV, B_INV)
Z = _m(A, B, A, B)
Z_INV = _m(B_INV, A_INV, B_INV, A_INV)

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


def cancellation_rules() -> tuple[Rule, ...]:
    return (
        _cancel_tail_rule(A, A_INV, A_LEFT_INV),
        _cancel_tail_rule(A_INV, A, A_RIGHT_INV),
        _cancel_tail_rule(B, B_INV, B_LEFT_INV),
        _cancel_tail_rule(B_INV, B, B_RIGHT_INV),
    )


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
    left_nf, left_pf = normalize(raw.lhs, _base_rules(), 2_000)
    right_nf, right_pf = normalize(raw.rhs, _base_rules(), 2_000)
    return Eq(left_nf, right_nf), Trans(Sym(left_pf), Trans(congruence, right_pf))


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
    left_nf, left_pf = normalize(raw.lhs, (axiom_rule(MUL_ASSOC),), 20)
    right_nf, right_pf = normalize(raw.rhs, (axiom_rule(MUL_ASSOC),), 20)
    pf = Trans(Sym(left_pf), Trans(congruence, right_pf))
    return lemma_rule(Eq(left_nf, right_nf), pf)


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


def _xy_seed_actions() -> tuple[tuple[Eq, Pf], tuple[Eq, Pf]]:
    """Derive A*Y=Y^-1*A and B*X=X^-1*B from the presentation."""
    rel_b = _as_eq(GROUP_REL_B)
    rel_a = _as_eq(GROUP_REL_A)
    step, step_pf = _normalize_congruence(rel_b, Axiom(rel_b), Y)
    a_y = _normalize_congruence(step, step_pf, Y_INV, left=True)

    step, step_pf = _normalize_congruence(rel_a, Axiom(rel_a), X)
    b_x = _normalize_congruence(step, step_pf, X_INV, left=True)
    return a_y, b_x


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


def action_lemmas() -> tuple[Rule, ...]:
    """All signed generator actions on X, Y and Z, derived from the axioms."""
    a_y, b_x = _xy_seed_actions()
    a_z, b_z = _z_seed_actions()
    pairs = (
        *_canonical_action_family(a_y, Y, Y_INV, A, A_INV),
        *_canonical_action_family(b_x, X, X_INV, B, B_INV),
        *_canonical_action_family(a_z, Z, Z_INV, A, A_INV),
        *_canonical_action_family(b_z, Z, Z_INV, B, B_INV),
    )
    return tuple(lemma_rule(equation, proof) for equation, proof in pairs)


def action_rules() -> tuple[Rule, ...]:
    """Direct and tail-preserving forms of every action lemma."""
    direct = action_lemmas()
    return (*direct, *(_tail_lift(rule.eq, rule.proof) for rule in direct))


def commutation_lemmas() -> tuple[Rule, ...]:
    """Pairwise signed commutation of X, Y and Z."""
    actions = action_rules()
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
        section_rules = tuple(
            rule
            for rule in actions
            if type(rule.eq.lhs) is Fun
            and rule.eq.lhs.args
            and rule.eq.lhs.args[0] == section
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


def lemma_library() -> tuple[Rule, ...]:
    return (*cancellation_rules(), *action_lemmas(), *commutation_lemmas())


__all__ = [
    "X",
    "X_INV",
    "Y",
    "Y_INV",
    "Z",
    "Z_INV",
    "action_lemmas",
    "action_rules",
    "cancellation_rules",
    "commutation_lemmas",
    "lemma_library",
]
