"""Property-based tests (Hypothesis). Example tests only check the cases I
imagined; these check invariants over *generated* terms, formulas, and proofs.

Run: ``uv run pytest test_properties.py``.
"""

from __future__ import annotations

from hypothesis import assume, given, settings
from hypothesis import strategies as st

import cold_start.proof as P
from cold_start.checker import Sequent, check
from cold_start.peano import (
    ADD_SUCC_F,
    ADD_ZERO_F,
    PEANO,
    ZERO,
    add,
    induction,
    numeral,
)
from cold_start.proof import from_json, to_dict, to_json
from cold_start.proofs import add_proof as prove_add
from cold_start.syntax import (
    Bottom,
    Eq,
    Exists,
    Forall,
    Formula,
    Fun,
    Implies,
    Term,
    Var,
    formula_free_vars,
    formula_from_dict,
    formula_subst,
    formula_to_dict,
    term_free_vars,
    term_from_dict,
    term_subst,
    term_to_dict,
    validate_formula,
    validate_term,
)

# --- strategies -----------------------------------------------------------

VAR_NAMES = st.sampled_from(["x", "y", "z", "n", "m", "a", "b"])
FUN_NAMES = st.sampled_from(["0", "S", "+", "f", "g"])


def terms():
    return st.recursive(
        st.builds(Var, VAR_NAMES),
        lambda kids: st.builds(
            lambda nm, ar: Fun(nm, tuple(ar)), FUN_NAMES, st.lists(kids, max_size=3)
        ),
        max_leaves=8,
    )


def formulas():
    return st.recursive(
        st.one_of(st.builds(Eq, terms(), terms()), st.builds(Bottom)),
        lambda kids: st.one_of(
            st.builds(Implies, kids, kids),
            st.builds(Forall, VAR_NAMES, st.just(""), kids),
            st.builds(Exists, VAR_NAMES, st.just(""), kids),
        ),
        max_leaves=6,
    )


def proofs():
    """Arbitrary (mostly invalid) proof terms -- for totality and round-trip."""
    leaf = st.one_of(
        st.builds(P.Axiom, formulas()),
        st.builds(P.Assume, formulas()),
        st.builds(P.Refl, terms()),
    )
    return st.recursive(
        leaf,
        lambda kids: st.one_of(
            st.builds(P.Sym, kids),
            st.builds(P.Trans, kids, kids),
            st.builds(lambda nm, ar: P.Cong(nm, tuple(ar)), FUN_NAMES, st.lists(kids, max_size=3)),
            st.builds(P.MP, kids, kids),
            st.builds(P.ImpIntro, formulas(), kids),
            st.builds(P.Inst, kids, VAR_NAMES, terms()),
            st.builds(P.Induct, VAR_NAMES, formulas(), kids, kids),
            st.builds(P.ExFalso, kids, formulas()),
            st.builds(P.RAA, formulas(), kids),
            st.builds(P.ForallElim, kids, terms()),
            st.builds(P.ForallIntro, VAR_NAMES, st.just(""), kids),
            st.builds(P.ExistsIntro, formulas(), terms(), kids),
            st.builds(P.ExistsElim, VAR_NAMES, kids, kids),
        ),
        max_leaves=12,
    )


BASE_TERM = Var("x")
BASE_FORMULA = Eq(BASE_TERM, BASE_TERM)
BASE_PROOF = P.Assume(BASE_FORMULA)

TERM_JSON_EXAMPLES = {
    Var: BASE_TERM,
    Fun: Fun("f", (BASE_TERM,)),
}

FORMULA_JSON_EXAMPLES = {
    Eq: BASE_FORMULA,
    Implies: Implies(BASE_FORMULA, BASE_FORMULA),
    Bottom: Bottom(),
    Forall: Forall("x", "", BASE_FORMULA),
    Exists: Exists("x", "", BASE_FORMULA),
}

PROOF_JSON_EXAMPLES = {
    P.Axiom: P.Axiom(BASE_FORMULA),
    P.Assume: BASE_PROOF,
    P.Refl: P.Refl(BASE_TERM),
    P.Sym: P.Sym(BASE_PROOF),
    P.Trans: P.Trans(BASE_PROOF, BASE_PROOF),
    P.Cong: P.Cong("f", (BASE_PROOF,)),
    P.MP: P.MP(BASE_PROOF, BASE_PROOF),
    P.ImpIntro: P.ImpIntro(BASE_FORMULA, BASE_PROOF),
    P.Inst: P.Inst(BASE_PROOF, "x", BASE_TERM),
    P.Induct: P.Induct("x", BASE_FORMULA, BASE_PROOF, BASE_PROOF),
    P.ExFalso: P.ExFalso(BASE_PROOF, BASE_FORMULA),
    P.RAA: P.RAA(BASE_FORMULA, BASE_PROOF),
    P.ForallElim: P.ForallElim(BASE_PROOF, BASE_TERM),
    P.ForallIntro: P.ForallIntro("x", "", BASE_PROOF),
    P.ExistsIntro: P.ExistsIntro(Exists("x", "", BASE_FORMULA), BASE_TERM, BASE_PROOF),
    P.ExistsElim: P.ExistsElim("x", BASE_PROOF, BASE_PROOF),
}


def class_names(classes):
    return {cls.__name__ for cls in classes if cls.__module__.startswith("cold_start.")}


# --- serialization round-trips --------------------------------------------


def test_json_examples_cover_every_concrete_node_class():
    assert class_names(TERM_JSON_EXAMPLES) == class_names(Term.__subclasses__())
    assert class_names(FORMULA_JSON_EXAMPLES) == class_names(Formula.__subclasses__())
    assert class_names(PROOF_JSON_EXAMPLES) == class_names(P.Pf.__subclasses__())


@given(st.sampled_from(list(TERM_JSON_EXAMPLES.items())))
def test_every_term_json_kind_has_a_term_and_vice_versa(item):
    cls, term = item
    encoded = term_to_dict(term)
    assert encoded["k"] == cls.__name__
    decoded = term_from_dict(encoded)
    assert type(decoded) is cls
    assert decoded == term


@given(st.sampled_from(list(FORMULA_JSON_EXAMPLES.items())))
def test_every_formula_json_kind_has_a_formula_and_vice_versa(item):
    cls, formula = item
    encoded = formula_to_dict(formula)
    assert encoded["k"] == cls.__name__
    decoded = formula_from_dict(encoded)
    assert type(decoded) is cls
    assert decoded == formula


@given(st.sampled_from(list(PROOF_JSON_EXAMPLES.items())))
def test_every_proof_json_kind_has_a_proof_and_vice_versa(item):
    cls, proof = item
    encoded = to_dict(proof)
    assert encoded["k"] == cls.__name__
    decoded = P.from_dict(encoded)
    assert type(decoded) is cls
    assert decoded == proof


@given(terms())
def test_term_roundtrips(t):
    assert term_from_dict(term_to_dict(t)) == t


@given(formulas())
def test_formula_roundtrips(f):
    assert formula_from_dict(formula_to_dict(f)) == f


@given(proofs())
def test_proof_roundtrips(pf):
    assert from_json(to_json(pf)) == pf
    assert from_json(to_json(pf)) == from_json(to_json(pf))
    assert to_dict(pf) == to_dict(pf)


# --- checker is total: only Sequent or a declared failure -----------------


@given(proofs())
def test_check_is_total(pf):
    try:
        result = check(pf, PEANO)
    except (TypeError, ValueError):
        return  # the only sanctioned failure modes
    assert isinstance(result, Sequent)


# --- validation never false-rejects a genuinely canonical value -----------


@given(terms())
def test_validate_accepts_canonical_terms(t):
    validate_term(t)  # must not raise


@given(formulas())
def test_validate_accepts_canonical_formulas(f):
    validate_formula(f)  # must not raise


# --- substitution algebra -------------------------------------------------


@given(formulas(), VAR_NAMES, terms())
def test_subst_of_nonfree_var_is_identity(f, x, t):
    assume(x not in formula_free_vars(f))
    assert formula_subst(f, x, t) == f


@given(formulas(), VAR_NAMES, terms())
def test_free_vars_after_subst(f, x, t):
    ff = formula_free_vars(f)
    expected = (ff - {x}) | (term_free_vars(t) if x in ff else frozenset())
    assert formula_free_vars(formula_subst(f, x, t)) == expected


@given(terms(), VAR_NAMES, terms())
def test_subst_idempotent_when_var_absent_from_replacement(t, x, repl):
    assume(x not in term_free_vars(repl))
    once = term_subst(t, x, repl)
    assert term_subst(once, x, repl) == once  # no x left to replace


# --- the sound generator: the checker must agree with arithmetic ----------


@given(st.integers(0, 25), st.integers(0, 25))
@settings(deadline=None)
def test_checker_agrees_with_addition(a, b):
    seq = check(prove_add(a, b), PEANO)
    assert seq.concl == Eq(add(numeral(a), numeral(b)), numeral(a + b))
    assert seq.hyps == frozenset()


@given(st.integers(0, 20), st.integers(0, 20))
@settings(deadline=None)
def test_serialization_preserves_checked_sequent(a, b):
    pf = prove_add(a, b)
    assert check(pf, PEANO) == check(from_json(to_json(pf)), PEANO)


@given(st.integers(0, 20), st.integers(0, 20))
@settings(deadline=None)
def test_check_is_deterministic(a, b):
    pf = prove_add(a, b)
    assert check(pf, PEANO) == check(pf, PEANO)


# --- the first-class induction rule ---------------------------------------


def _left_identity_induction():
    """An Induct proof term for  0 + n = n  (genuine base + step)."""
    n = Var("n")
    pred = Eq(add(ZERO, n), n)
    base = P.Inst(P.Axiom(ADD_ZERO_F), "x", ZERO)
    ih = P.Assume(pred)
    unfold = P.Inst(P.Inst(P.Axiom(ADD_SUCC_F), "x", ZERO), "y", n)
    step = P.ImpIntro(pred, P.Trans(unfold, P.Cong("S", (ih,))))
    return pred, induction("n", pred, base, step)


def test_induction_proof_checks_and_serializes():
    pred, pf = _left_identity_induction()
    assert check(pf, PEANO).concl == pred
    assert check(from_json(to_json(pf)), PEANO) == check(pf, PEANO)


@given(VAR_NAMES)
def test_induction_rejects_var_free_in_hypothesis(v):
    """The side condition that blocks the 1=0 exploit: if the induction variable
    is free in an undischarged hypothesis of base/step, reject. Here base leaks
    a hypothesis mentioning the variable."""
    var = Var(v)
    pred = Eq(var, var)  # trivially has the variable free
    leaky_base = P.Assume(Eq(var, var))  # undischarged hyp keeps `v` free
    step = P.ImpIntro(pred, P.Refl(Fun("S", (var,))))  # |- pred -> (S v = S v)
    pf = P.Induct(v, pred, leaky_base, step)
    try:
        check(pf, PEANO)
    except (ValueError, TypeError):
        return
    raise AssertionError("induction allowed its variable free in a hypothesis")
