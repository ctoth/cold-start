"""Property-based tests (Hypothesis). Example tests only check the cases I
imagined; these check invariants over *generated* terms, formulas, and proofs.

Run: ``uv run pytest test_properties.py``.
"""

from __future__ import annotations

from hypothesis import assume, given, settings
from hypothesis import strategies as st

import cold_start.proof as P
from cold_start.checker import Sequent, check
from cold_start.peano import PEANO
from cold_start.presburger import (
    ADD_SUCC_F,
    ADD_ZERO_F,
    ZERO,
    add,
    induction,
    numeral,
)
from cold_start.proof import from_bytes, to_bytes
from cold_start.proofs import add_proof as prove_add
from cold_start.syntax import (
    Bottom,
    BVar,
    Eq,
    Exists,
    Forall,
    Formula,
    Fun,
    Implies,
    Term,
    Var,
    exists,
    forall,
    formula_from_bytes,
    formula_to_bytes,
    term_from_bytes,
    term_to_bytes,
    validate,
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
            st.builds(forall, VAR_NAMES, st.just(""), kids),
            st.builds(exists, VAR_NAMES, st.just(""), kids),
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

TERM_EXAMPLES = {
    Var: BASE_TERM,
    BVar: BVar(0),
    Fun: Fun("f", (BASE_TERM,)),
}

FORMULA_EXAMPLES = {
    Eq: BASE_FORMULA,
    Implies: Implies(BASE_FORMULA, BASE_FORMULA),
    Bottom: Bottom(),
    Forall: forall("x", "", BASE_FORMULA),
    Exists: exists("x", "", BASE_FORMULA),
}

PROOF_EXAMPLES = {
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
    P.ExistsIntro: P.ExistsIntro(exists("x", "", BASE_FORMULA), BASE_TERM, BASE_PROOF),
    P.ExistsElim: P.ExistsElim("x", BASE_PROOF, BASE_PROOF),
}


def class_names(classes):
    return {cls.__name__ for cls in classes if cls.__module__.startswith("cold_start.")}


# --- serialization round-trips --------------------------------------------


def test_examples_cover_every_concrete_node_class():
    assert class_names(TERM_EXAMPLES) == class_names(Term.__subclasses__())
    assert class_names(FORMULA_EXAMPLES) == class_names(Formula.__subclasses__())
    assert class_names(PROOF_EXAMPLES) == class_names(P.Pf.__subclasses__())


@given(st.sampled_from(list(TERM_EXAMPLES.items())))
def test_every_term_kind_round_trips(item):
    cls, term = item
    decoded = term_from_bytes(term_to_bytes(term))
    assert type(decoded) is cls
    assert decoded == term


@given(st.sampled_from(list(FORMULA_EXAMPLES.items())))
def test_every_formula_kind_round_trips(item):
    cls, formula = item
    decoded = formula_from_bytes(formula_to_bytes(formula))
    assert type(decoded) is cls
    assert decoded == formula


@given(st.sampled_from(list(PROOF_EXAMPLES.items())))
def test_every_proof_kind_round_trips(item):
    cls, proof = item
    decoded = from_bytes(to_bytes(proof))
    assert type(decoded) is cls
    assert decoded == proof


@given(terms())
def test_term_roundtrips(t):
    assert term_from_bytes(term_to_bytes(t)) == t


@given(formulas())
def test_formula_roundtrips(f):
    assert formula_from_bytes(formula_to_bytes(f)) == f


@given(proofs())
def test_proof_roundtrips(pf):
    assert from_bytes(to_bytes(pf)) == pf
    assert from_bytes(to_bytes(pf)) == from_bytes(to_bytes(pf))
    assert to_bytes(pf) == to_bytes(pf)  # encoding is deterministic


def test_deep_proof_survives_serialization_without_recursion():
    """The verifier's front door + trust path: a proof whose term is nested far
    deeper than the recursion limit serializes to bytes and is decoded + re-checked
    with NO RecursionError. The old JSON path died exactly here (json.loads, and the
    recursive dict decoder, both blow the call stack). hamblin's postfix codec does
    not, so the only bound is memory. (The human-readable repr of a result this deep
    still recurses -- that is the output path, not the trust path; tracked separately.)"""
    import sys as _sys

    from cold_start.checker import Theory

    t = Var("x")
    for _ in range(50_000):
        t = Fun("s", (t,))
    pf = P.Refl(t)
    theory = Theory(axioms=frozenset())

    old = _sys.getrecursionlimit()
    _sys.setrecursionlimit(300)  # < 1% of the term depth
    try:
        seq = check(from_bytes(to_bytes(pf)), theory)
    finally:
        _sys.setrecursionlimit(old)
    assert seq.concl == Eq(t, t)


# --- checker is total: only Sequent or a declared failure -----------------


@given(proofs())
def test_check_is_total(pf):
    try:
        result = check(pf, PEANO)
    except (TypeError, ValueError):
        return  # the only sanctioned failure modes
    assert isinstance(result, Sequent)


def test_check_is_total_on_pathologically_deep_input():
    # Totality must hold even for input deep enough to exhaust Python's call
    # stack: `check` returns a Sequent or raises TypeError/ValueError -- NEVER a
    # RecursionError. A 5000-deep successor term forces the issue.
    deep = numeral(5000)  # S(S(...(0)...)), 5000 deep -- built iteratively
    try:
        result = check(P.Refl(deep), PEANO)
    except (TypeError, ValueError):
        return  # the only sanctioned failure modes
    assert isinstance(result, Sequent)


def test_check_handles_arbitrarily_deep_proofs_without_recursion():
    # check() is iterative end to end: validation, derivation, substitution,
    # sort-checking, and even ==/hash on the nodes walk a heap agenda, not the call
    # stack. Each construction below is ~6000 deep -- far past Python's recursion
    # limit -- and each previously raised RecursionError. They must now succeed.
    n = 6000
    x = Var("x")

    # (1) a deep PROOF chain: Sym^n over a reflexive equality.
    sym = P.Refl(x)
    for _ in range(n):
        sym = P.Sym(sym)
    assert isinstance(check(sym, PEANO), Sequent)

    # (2) a deep TERM built by the derivation: Cong^n over S, concl = Eq(Sⁿx, Sⁿx).
    cong = P.Refl(x)
    for _ in range(n):
        cong = P.Cong("S", (cong,))
    assert isinstance(check(cong, PEANO), Sequent)

    # (3) deep `==`: Trans must compare the two deep middle terms (distinct objects,
    # so it is a real structural compare, not an identity short-circuit).
    trans = P.Trans(P.Refl(numeral(n)), P.Refl(numeral(n)))
    seq = check(trans, PEANO)
    assert seq.concl == Eq(numeral(n), numeral(n))

    # (4) deep substitution: Inst rewriting a free variable across the deep concl.
    assert isinstance(check(P.Inst(cong, "y", x), PEANO), Sequent)


# --- validation never false-rejects a genuinely canonical value -----------


@given(st.one_of(terms(), formulas()))
def test_validate_accepts_canonical_nodes(node):

    validate(node)  # one validator for terms and formulas alike, must not raise


# --- substitution algebra -------------------------------------------------


@given(formulas(), VAR_NAMES, terms())
def test_subst_of_nonfree_var_is_identity(f, x, t):
    assume(x not in f.free_vars())
    assert f.subst(x, t) == f


@given(formulas(), VAR_NAMES, terms())
def test_free_vars_after_subst(f, x, t):
    ff = f.free_vars()
    expected = (ff - {x}) | (t.free_vars() if x in ff else frozenset())
    assert f.subst(x, t).free_vars() == expected


@given(terms(), VAR_NAMES, terms())
def test_subst_idempotent_when_var_absent_from_replacement(t, x, repl):
    assume(x not in repl.free_vars())
    once = t.subst(x, repl)
    assert once.subst(x, repl) == once  # no x left to replace


@given(formulas())
def test_alpha_equivalence_is_structural_equality(body):
    # The bound NAME is irrelevant: abstracting the same variable under two
    # different (fresh) names yields identical locally-nameless data, so
    # alpha-equivalence is literal `==`. ("Q1"/"Q2" are not in VAR_NAMES, so they
    # cannot already occur free in `body`.)
    fa = forall("Q1", "", body.subst("x", Var("Q1")))
    fb = forall("Q2", "", body.subst("x", Var("Q2")))
    assert fa == fb




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
    assert check(pf, PEANO) == check(from_bytes(to_bytes(pf)), PEANO)


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
    assert check(from_bytes(to_bytes(pf)), PEANO) == check(pf, PEANO)


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
