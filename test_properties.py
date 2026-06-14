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
    S,
    add,
    is_induction_instance,
    numeral,
)
from cold_start.proof import from_json, to_dict, to_json
from cold_start.syntax import (
    Eq,
    Fun,
    Implies,
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
        st.builds(Eq, terms(), terms()),
        lambda kids: st.builds(Implies, kids, kids),
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
        ),
        max_leaves=12,
    )


def prove_add(a: int, b: int) -> P.Pf:
    """A *sound by construction* proof of  numeral(a) + numeral(b) = numeral(a+b),
    built by unfolding the recursion axioms on the (concrete) second argument.
    The checker must agree with it for every a, b.
    """
    big_a = numeral(a)
    if b == 0:
        return P.Inst(P.Axiom(ADD_ZERO_F), "x", big_a)  # a + 0 = a
    b_minus = numeral(b - 1)
    # a + S(b-1) = S(a + (b-1))
    succ_step = P.Inst(P.Inst(P.Axiom(ADD_SUCC_F), "x", big_a), "y", b_minus)
    # S(a + (b-1)) = S(numeral(a+b-1)) = numeral(a+b)
    return P.Trans(succ_step, P.Cong("S", (prove_add(a, b - 1),)))


# --- serialization round-trips --------------------------------------------


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


# --- the trusted induction-schema recognizer ------------------------------


@given(formulas(), VAR_NAMES)
def test_induction_recognizer_is_complete(pred, x):
    """Every genuine schema instance must be accepted (else induction is
    incompletely recognized and valid proofs get rejected)."""
    schema = Implies(
        formula_subst(pred, x, ZERO),
        Implies(Implies(pred, formula_subst(pred, x, S(Var(x)))), pred),
    )
    assert is_induction_instance(schema)


@given(formulas(), formulas(), formulas())
def test_induction_recognizer_rejects_wrong_shape(a, b, c):
    """If the step's antecedent isn't the recurring predicate, it's not the
    schema and must be rejected."""
    assume(b != c)
    bogus = Implies(a, Implies(Implies(b, a), c))  # step.ant=b but predicate=c
    assert not is_induction_instance(bogus)
