"""The trusted proof checker.

``check`` validates an inert proof tree with exact-type dispatch, then derives
its sequent iteratively.  Proof nodes contain no validation or inference
behavior; every accepted rule is visible in this module.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import cast

from .proof import (
    CANONICAL_PROOF_TYPES,
    MP,
    RAA,
    Assume,
    Axiom,
    Cong,
    ExFalso,
    ExistsElim,
    ExistsIntro,
    ForallElim,
    ForallIntro,
    ImpIntro,
    Induct,
    Inst,
    Pf,
    Refl,
    Sym,
    Trans,
)
from .sequent import Sequent
from .syntax import (
    Bottom,
    Eq,
    Exists,
    Forall,
    Formula,
    Fun,
    Implies,
    Not,
    Var,
    forall,
    instantiate,
    validate,
)
from .theory import Signature, Theory, validate_theory

ProofChildren = tuple[Pf, ...]
Derived = Callable[[Pf], Sequent]

# Deliberately independent from CANONICAL_PROOF_TYPES: equality between these
# inventories is a fail-closed exhaustiveness contract checked before use.
CHECKER_PROOF_TYPES: frozenset[type[Pf]] = frozenset(
    {
        Axiom,
        Assume,
        Refl,
        Sym,
        Trans,
        Cong,
        MP,
        ImpIntro,
        Inst,
        Induct,
        ExFalso,
        RAA,
        ForallElim,
        ForallIntro,
        ExistsIntro,
        ExistsElim,
    }
)


def sort_check_formula(formula: Formula, signature: Signature) -> None:
    """Check a formula under one closed signature."""
    Sequent(frozenset(), formula).sort_check(signature)


def _validate_node(proof: Pf) -> ProofChildren:
    proof_type = type(proof)
    if proof_type is Axiom:
        validate(cast(Axiom, proof).formula)
        return ()
    if proof_type is Assume:
        validate(cast(Assume, proof).formula)
        return ()
    if proof_type is Refl:
        validate(cast(Refl, proof).term)
        return ()
    if proof_type is Sym:
        return (cast(Sym, proof).sub,)
    if proof_type is Trans:
        node = cast(Trans, proof)
        return (node.left, node.right)
    if proof_type is Cong:
        node = cast(Cong, proof)
        if type(node.fun) is not str:
            raise TypeError("Cong.fun must be a genuine str")
        if type(node.args) is not tuple:
            raise TypeError("Cong.args must be a tuple")
        return node.args
    if proof_type is MP:
        node = cast(MP, proof)
        return (node.imp, node.ant)
    if proof_type is ImpIntro:
        node = cast(ImpIntro, proof)
        validate(node.hyp)
        return (node.body,)
    if proof_type is Inst:
        node = cast(Inst, proof)
        if type(node.var) is not str:
            raise TypeError("Inst.var must be a genuine str")
        validate(node.term)
        return (node.sub,)
    if proof_type is Induct:
        node = cast(Induct, proof)
        if type(node.var) is not str:
            raise TypeError("Induct.var must be a genuine str")
        validate(node.pred)
        return (node.base, node.step)
    if proof_type is ExFalso:
        node = cast(ExFalso, proof)
        validate(node.concl)
        return (node.sub,)
    if proof_type is RAA:
        node = cast(RAA, proof)
        validate(node.goal)
        return (node.sub,)
    if proof_type is ForallElim:
        node = cast(ForallElim, proof)
        validate(node.term)
        return (node.sub,)
    if proof_type is ForallIntro:
        node = cast(ForallIntro, proof)
        if type(node.var) is not str or type(node.sort) is not str:
            raise TypeError("ForallIntro.var and .sort must be genuine strs")
        return (node.sub,)
    if proof_type is ExistsIntro:
        node = cast(ExistsIntro, proof)
        validate(node.claim)
        validate(node.witness)
        return (node.sub,)
    if proof_type is ExistsElim:
        node = cast(ExistsElim, proof)
        if type(node.eigenvar) is not str:
            raise TypeError("ExistsElim.eigenvar must be a genuine str")
        return (node.sub_ex, node.sub_use)
    raise TypeError(f"not a proof term: {proof!r}")


def validate_proof(proof: object) -> None:
    """Iteratively validate one exact canonical proof tree."""
    if CHECKER_PROOF_TYPES != CANONICAL_PROOF_TYPES:
        raise TypeError("checker proof dispatch is not exhaustive")
    stack: list[object] = [proof]
    while stack:
        candidate = stack.pop()
        if type(candidate) not in CHECKER_PROOF_TYPES:
            raise TypeError(f"not a proof term: {candidate!r}")
        stack.extend(_validate_node(cast(Pf, candidate)))


def _derive_rule(proof: Pf, theory: Theory, derived: Derived) -> Sequent:
    proof_type = type(proof)
    if proof_type is Axiom:
        node = cast(Axiom, proof)
        if not theory.accepts(node.formula):
            raise ValueError(f"not an axiom of this theory: {node.formula!r}")
        return Sequent(frozenset(), node.formula)
    if proof_type is Assume:
        formula = cast(Assume, proof).formula
        return Sequent(frozenset({formula}), formula)
    if proof_type is Refl:
        term = cast(Refl, proof).term
        return Sequent(frozenset(), Eq(term, term))
    if proof_type is Sym:
        sequent = derived(cast(Sym, proof).sub)
        if type(sequent.concl) is not Eq:
            raise ValueError(f"sym needs an equality, got {sequent.concl!r}")
        return Sequent(sequent.hyps, Eq(sequent.concl.rhs, sequent.concl.lhs))
    if proof_type is Trans:
        node = cast(Trans, proof)
        left = derived(node.left)
        right = derived(node.right)
        if type(left.concl) is not Eq or type(right.concl) is not Eq:
            raise ValueError("trans needs two equalities")
        if left.concl.rhs != right.concl.lhs:
            raise ValueError(
                f"trans: middle terms differ: {left.concl.rhs!r} vs {right.concl.lhs!r}"
            )
        return Sequent(left.hyps | right.hyps, Eq(left.concl.lhs, right.concl.rhs))
    if proof_type is Cong:
        node = cast(Cong, proof)
        hypotheses: frozenset[Formula] = frozenset()
        left_terms = []
        right_terms = []
        for subproof in node.args:
            sequent = derived(subproof)
            if type(sequent.concl) is not Eq:
                raise ValueError(f"cong needs equalities, got {sequent.concl!r}")
            hypotheses |= sequent.hyps
            left_terms.append(sequent.concl.lhs)
            right_terms.append(sequent.concl.rhs)
        return Sequent(
            hypotheses,
            Eq(Fun(node.fun, tuple(left_terms)), Fun(node.fun, tuple(right_terms))),
        )
    if proof_type is MP:
        node = cast(MP, proof)
        implication = derived(node.imp)
        antecedent = derived(node.ant)
        if type(implication.concl) is not Implies:
            raise ValueError(f"mp needs an implication, got {implication.concl!r}")
        if implication.concl.ant != antecedent.concl:
            raise ValueError(
                "mp: antecedent mismatch:\n"
                f"  needs: {implication.concl.ant!r}\n"
                f"  has:   {antecedent.concl!r}"
            )
        return Sequent(implication.hyps | antecedent.hyps, implication.concl.con)
    if proof_type is ImpIntro:
        node = cast(ImpIntro, proof)
        body = derived(node.body)
        return Sequent(body.hyps - {node.hyp}, Implies(node.hyp, body.concl))
    if proof_type is Inst:
        node = cast(Inst, proof)
        sequent = derived(node.sub)
        for hypothesis in sequent.hyps:
            if node.var in hypothesis.free_vars():
                raise ValueError(
                    f"cannot instantiate {node.var!r}: free in hypothesis {hypothesis!r}"
                )
        signature = theory.signature
        if signature is not None:
            variable_sorts = {
                sort for name, sort in sequent.concl.free_var_sorts() if name == node.var
            }
            if variable_sorts:
                term_sort = node.term.sort_of(signature)
                if term_sort not in variable_sorts:
                    raise ValueError(
                        f"cannot instantiate {node.var!r}:{variable_sorts} "
                        f"with a term of sort {term_sort!r}"
                    )
        return Sequent(sequent.hyps, sequent.concl.subst(node.var, node.term))
    if proof_type is Induct:
        node = cast(Induct, proof)
        if theory.zero is None or type(theory.succ) is not str:
            raise ValueError("theory defines no induction principle (no zero/succ)")
        base = derived(node.base)
        step = derived(node.step)
        predicate_at_zero = node.pred.subst(node.var, theory.zero)
        induction_sort = theory.induction_sort()
        induction_variable = Var(node.var, induction_sort)
        predicate_at_successor = node.pred.subst(
            node.var,
            Fun(theory.succ, (induction_variable,)),
        )
        if base.concl != predicate_at_zero:
            raise ValueError(
                f"induction base must prove {predicate_at_zero!r}, got {base.concl!r}"
            )
        expected_step = Implies(node.pred, predicate_at_successor)
        if step.concl != expected_step:
            raise ValueError(
                f"induction step must prove {expected_step!r}, got {step.concl!r}"
            )
        hypotheses = base.hyps | step.hyps
        for hypothesis in hypotheses:
            if node.var in hypothesis.free_vars():
                raise ValueError(
                    f"induction variable {node.var!r} is free in hypothesis {hypothesis!r}"
                )
        return Sequent(hypotheses, node.pred)
    if proof_type is ExFalso:
        node = cast(ExFalso, proof)
        sequent = derived(node.sub)
        if type(sequent.concl) is not Bottom:
            raise ValueError(f"ex falso needs a proof of Bottom, got {sequent.concl!r}")
        return Sequent(sequent.hyps, node.concl)
    if proof_type is RAA:
        node = cast(RAA, proof)
        sequent = derived(node.sub)
        if type(sequent.concl) is not Bottom:
            raise ValueError(f"reductio needs a proof of Bottom, got {sequent.concl!r}")
        return Sequent(sequent.hyps - {Not(node.goal)}, node.goal)
    if proof_type is ForallElim:
        node = cast(ForallElim, proof)
        sequent = derived(node.sub)
        if type(sequent.concl) is not Forall:
            raise ValueError(f"forall-elim needs a universal, got {sequent.concl!r}")
        signature = theory.signature
        if signature is not None and sequent.concl.sort:
            term_sort = node.term.sort_of(signature)
            if term_sort != sequent.concl.sort:
                raise ValueError(
                    f"cannot instantiate forall :{sequent.concl.sort!r} "
                    f"with a term of sort {term_sort!r}"
                )
        return Sequent(sequent.hyps, instantiate(sequent.concl, node.term))
    if proof_type is ForallIntro:
        node = cast(ForallIntro, proof)
        sequent = derived(node.sub)
        for hypothesis in sequent.hyps:
            if node.var in hypothesis.free_vars():
                raise ValueError(
                    f"cannot generalize {node.var!r}: free in hypothesis {hypothesis!r}"
                )
        return Sequent(sequent.hyps, forall(node.var, node.sort, sequent.concl))
    if proof_type is ExistsIntro:
        node = cast(ExistsIntro, proof)
        if type(node.claim) is not Exists:
            raise ValueError(f"exists-intro needs an existential claim, got {node.claim!r}")
        sequent = derived(node.sub)
        expected = instantiate(node.claim, node.witness)
        if sequent.concl != expected:
            raise ValueError(
                f"exists-intro: sub-proof must prove {expected!r}, got {sequent.concl!r}"
            )
        signature = theory.signature
        if signature is not None and node.claim.sort:
            witness_sort = node.witness.sort_of(signature)
            if witness_sort != node.claim.sort:
                raise ValueError(
                    f"exists-intro witness has sort {witness_sort!r}, "
                    f"expected {node.claim.sort!r}"
                )
        return Sequent(sequent.hyps, node.claim)
    if proof_type is ExistsElim:
        node = cast(ExistsElim, proof)
        existential = derived(node.sub_ex)
        if type(existential.concl) is not Exists:
            raise ValueError(f"exists-elim needs an existential, got {existential.concl!r}")
        instance = instantiate(
            existential.concl,
            Var(node.eigenvar, existential.concl.sort),
        )
        use = derived(node.sub_use)
        if instance not in use.hyps:
            raise ValueError(
                f"exists-elim: the using proof must assume the instance {instance!r}"
            )
        conclusion = use.concl
        hypotheses = existential.hyps | (use.hyps - {instance})
        if node.eigenvar in conclusion.free_vars():
            raise ValueError(
                f"exists-elim eigenvariable {node.eigenvar!r} escapes into "
                f"the conclusion {conclusion!r}"
            )
        for hypothesis in hypotheses:
            if node.eigenvar in hypothesis.free_vars():
                raise ValueError(
                    f"exists-elim eigenvariable {node.eigenvar!r} is free in "
                    f"hypothesis {hypothesis!r}"
                )
        return Sequent(hypotheses, conclusion)
    raise TypeError(f"checker has no rule for proof term: {proof!r}")


def _derive(proof: Pf, theory: Theory) -> Sequent:
    order: list[Pf] = []
    stack = [proof]
    while stack:
        candidate = stack.pop()
        order.append(candidate)
        stack.extend(_validate_node(candidate))

    signature = theory.signature
    results: dict[int, Sequent] = {}

    def derived(child: Pf) -> Sequent:
        return results[id(child)]

    for candidate in reversed(order):
        sequent = _derive_rule(candidate, theory, derived)
        if signature is not None:
            sequent.sort_check(signature)
        results[id(candidate)] = sequent
    return results[id(proof)]


def check(proof: object, theory: object) -> Sequent:
    """Validate and iteratively re-derive the sequent proved by ``proof``."""
    checked_theory = validate_theory(theory)
    validate_proof(proof)
    return _derive(cast(Pf, proof), checked_theory)


__all__ = ["CHECKER_PROOF_TYPES", "check", "sort_check_formula", "validate_proof"]
