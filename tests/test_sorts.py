"""Many-sorted soundness and sort-checking (Hypothesis).

Sorts give a whole new family of invariants: every theorem stays well-sorted,
you cannot instantiate across sorts, ill-sorted terms are rejected, and proofs
hold in a *sorted* model with disjoint carriers per sort. Exercised on a monoid
M acting on a set X -- the shape that becomes scalars acting on vectors.
"""

from __future__ import annotations

from dataclasses import dataclass

from hypothesis import assume, given, settings
from hypothesis import strategies as st
from semantics import evaluate

import cold_start.proof as P
from cold_start.algebra import (
    ACT_ID,
    ACTION_SIG,
    M_LEFT_ID,
    MONOID_ACTION,
    E,
    act,
    mul,
)
from cold_start.checker import check, sort_check_formula
from cold_start.syntax import Eq, Fun, Implies, Var, exists, forall
from cold_start.theory import Signature, Theory

M_VARS = [Var("m", "M"), Var("n", "M"), Var("p", "M")]
X_VARS = [Var("x", "X"), Var("y", "X")]


# --- a sorted model: T_2 (transformations of {0,1}) acting on {0,1} --------


@dataclass
class SortedModel:
    name: str
    carriers: dict  # sort -> Hypothesis strategy
    interp: dict  # symbol -> callable


def _compose(g, f):  # (g o f)(i) = g(f(i)); transformations are tuples (h0, h1)
    return (g[f[0]], g[f[1]])


ACT_MODEL = SortedModel(
    "T_2 acting on {0,1}",
    carriers={
        "M": st.sampled_from([(0, 0), (0, 1), (1, 0), (1, 1)]),
        "X": st.sampled_from([0, 1]),
    },
    interp={"e": lambda: (0, 1), "*": _compose, "act": lambda f, x: f[x]},
)


def _vars_with_sorts(obj, out: set) -> None:
    if type(obj) is Var:
        out.add((obj.name, obj.sort))
    elif type(obj) is Fun:
        for a in obj.args:
            _vars_with_sorts(a, out)
    elif type(obj) is Eq:
        _vars_with_sorts(obj.lhs, out)
        _vars_with_sorts(obj.rhs, out)
    elif type(obj) is Implies:
        _vars_with_sorts(obj.ant, out)
        _vars_with_sorts(obj.con, out)


def env_for(concl, model: SortedModel, data) -> dict:
    out: set = set()
    _vars_with_sorts(concl, out)
    return {name: data.draw(model.carriers[sort]) for name, sort in out}


@given(st.data())
@settings(max_examples=200)
def test_model_satisfies_action_axioms(data):
    for ax in MONOID_ACTION.axioms:
        env = env_for(ax, ACT_MODEL, data)
        assert evaluate(ax, ACT_MODEL, env), f"model fails {ax!r}"


# --- a worked sorted proof ------------------------------------------------


def test_repeated_subterms_sort_check():
    # Sort-checking is the polymorphic `term.sort_of(sig)` method walking the term.
    # A term with a repeated subterm (`e` twice in act(e, act(e, x))) must still
    # sort-check cleanly -- each occurrence is resolved on its own.
    x = Var("x", "X")
    seq = check(P.Refl(act(E, act(E, x))), MONOID_ACTION)
    assert seq.concl == Eq(act(E, act(E, x)), act(E, act(E, x)))


def test_sorted_proof_checks():
    # act(e, act(e, x)) = x : inst ACT_ID at x := act(e,x), then trans with ACT_ID
    x = Var("x", "X")
    inner = act(E, x)
    step1 = P.Inst(P.Axiom(ACT_ID), "x", inner)  # act(e, act(e,x)) = act(e,x)
    step2 = P.Axiom(ACT_ID)  # act(e,x) = x
    seq = check(P.Trans(step1, step2), MONOID_ACTION)
    assert seq.concl == Eq(act(E, act(E, x)), x)
    assert seq.hyps == frozenset()


# --- sort-checking rejects malformed proofs -------------------------------


def test_cross_sort_instantiation_rejected():
    # M_LEFT_ID is `e*m = m` with m : M. Instantiating m with an X-term is a
    # sort error -- the heart of why sorts matter.
    bad = P.Inst(P.Axiom(M_LEFT_ID), "m", Var("x", "X"))
    try:
        check(bad, MONOID_ACTION)
    except ValueError:
        return
    raise AssertionError("instantiated an M-variable with an X-term")


def test_ill_sorted_term_rejected():
    # act expects (M, X); feeding (X, M) is ill-sorted.
    bad = P.Refl(Fun("act", (Var("x", "X"), Var("m", "M"))))
    try:
        check(bad, MONOID_ACTION)
    except ValueError:
        return
    raise AssertionError("accepted act(X, M) against rank act:(M,X)->X")


def test_equality_across_sorts_rejected():
    bad = P.Assume(Eq(Var("m", "M"), Var("x", "X")))
    try:
        check(bad, MONOID_ACTION)
    except ValueError:
        return
    raise AssertionError("accepted an equality between an M and an X")


def test_impintro_rejects_ill_sorted_hypothesis():
    # ImpIntro(Eq(m:M, x:X), Refl(e)) would yield |- (m=x) -> (e=e) with an
    # ill-sorted antecedent -- the same thing Assume rejects, so ImpIntro must
    # reject it too.
    bad = P.ImpIntro(Eq(Var("m", "M"), Var("x", "X")), P.Refl(E))
    try:
        check(bad, MONOID_ACTION)
    except ValueError:
        return
    raise AssertionError("ImpIntro accepted an ill-sorted hypothesis")


def test_variable_name_at_two_sorts_rejected():
    # A formula using `x` at both M and X is ill-formed: name-based substitution
    # would otherwise rewrite the X-positions with an M-term. Must be rejected.
    phi = Implies(
        Eq(act(Var("m", "M"), Var("x", "X")), Var("x", "X")),
        Eq(Var("x", "M"), Var("x", "M")),
    )
    try:
        check(P.Assume(phi), MONOID_ACTION)
    except ValueError:
        return
    raise AssertionError("accepted a formula using one name at two sorts")


def test_unknown_symbol_rejected():
    bad = P.Refl(Fun("bogus", ()))
    try:
        check(bad, MONOID_ACTION)
    except ValueError:
        return
    raise AssertionError("accepted an undeclared function symbol")


def test_wrong_arity_rejected():
    bad = P.Refl(Fun("act", (Var("m", "M"),)))  # act needs 2 args
    try:
        check(bad, MONOID_ACTION)
    except ValueError:
        return
    raise AssertionError("accepted act/1 against rank act:(M,X)->X")


# --- forward proofs: well-sorted and sound in the model -------------------


def m_terms():
    return st.recursive(
        st.one_of(st.sampled_from(M_VARS), st.just(E)),
        lambda kids: st.builds(mul, kids, kids),
        max_leaves=4,
    )


def x_terms():
    return st.recursive(
        st.sampled_from(X_VARS),
        lambda kids: st.builds(act, m_terms(), kids),
        max_leaves=4,
    )


@st.composite
def action_proofs(draw):
    facts: list[tuple] = []

    def add(pf) -> None:
        try:
            seq = check(pf, MONOID_ACTION)
        except (TypeError, ValueError):
            return
        facts.append((pf, seq))

    for ax in MONOID_ACTION.axioms:
        add(P.Axiom(ax))
    add(P.Refl(draw(m_terms())))
    add(P.Refl(draw(x_terms())))

    def pick():
        return draw(st.sampled_from(facts))[0]

    well_sorted_eq = st.one_of(
        st.builds(Eq, m_terms(), m_terms()),
        st.builds(Eq, x_terms(), x_terms()),
    )
    for _ in range(draw(st.integers(2, 8))):
        rule = draw(
            st.sampled_from(["sym", "trans", "cong*", "congact", "instM", "instX", "impintro"])
        )
        if rule == "sym":
            add(P.Sym(pick()))
        elif rule == "trans":
            add(P.Trans(pick(), pick()))
        elif rule == "cong*":
            add(P.Cong("*", (pick(), pick())))
        elif rule == "congact":
            add(P.Cong("act", (pick(), pick())))
        elif rule == "instM":
            add(P.Inst(pick(), draw(st.sampled_from(M_VARS)).name, draw(m_terms())))
        elif rule == "instX":
            add(P.Inst(pick(), draw(st.sampled_from(X_VARS)).name, draw(x_terms())))
        elif rule == "impintro":
            add(P.ImpIntro(draw(well_sorted_eq), pick()))

    return draw(st.sampled_from([pf for pf, _ in facts]))


@given(action_proofs())
@settings(deadline=None, max_examples=300)
def test_proofs_stay_well_sorted(pf):
    seq = check(pf, MONOID_ACTION)
    sort_check_formula(seq.concl, ACTION_SIG)  # must not raise
    for h in seq.hyps:
        sort_check_formula(h, ACTION_SIG)


@given(action_proofs(), st.data())
@settings(deadline=None, max_examples=300)
def test_proofs_sound_in_sorted_model(pf, data):
    seq = check(pf, MONOID_ACTION)
    assume(not seq.hyps)
    env = env_for(seq.concl, ACT_MODEL, data)
    assert evaluate(seq.concl, ACT_MODEL, env), f"UNSOUND: {seq!r} at {env}"


# --- sorts and quantifiers COEXIST: the sort scope threads through binders -----
# Earlier the sort-checker rejected every quantified formula. A quantifier just
# introduces a bound variable of a known sort, so sort-checking threads that sort
# through the binder (BVar(i) has the i-th enclosing binder's sort), exactly as
# evaluation threads a value and instantiation threads a depth.


def test_quantified_sorted_theorem_checks():
    # Generalize the action identity over x:X to |- forall x:X. act(e,x) = x.
    # The derived (quantified, sorted) sequent must pass the sort invariant.
    seq = check(P.ForallIntro("x", "X", P.Axiom(ACT_ID)), MONOID_ACTION)
    assert seq.concl == forall("x", "X", ACT_ID)
    assert seq.hyps == frozenset()


def test_many_sorted_induction_uses_the_theory_induction_sort():
    nat = "N"
    zero = Fun("0", ())

    def succ(term):
        return Fun("S", (term,))

    signature = Signature(
        sorts=frozenset({nat}),
        ranks=(("0", (), nat), ("S", (nat,), nat)),
    )
    theory = Theory(axioms=frozenset(), zero=zero, succ="S", signature=signature)
    n = Var("n", nat)
    pred = Eq(n, n)
    proof = P.Induct(
        "n",
        pred,
        P.Refl(zero),
        P.ImpIntro(pred, P.Refl(succ(n))),
    )

    seq = check(proof, theory)

    assert seq.hyps == frozenset()
    assert seq.concl == pred


def test_quantified_well_sorted_formula_sort_checks():
    # forall m:M. e*m = m -- under the binder the bound variable has sort M, so
    # e*m (both M) is M, matching m. Must not raise.
    sort_check_formula(forall("m", "M", M_LEFT_ID), ACTION_SIG)


def test_quantified_ill_sorted_body_rejected():
    # Under x:X, act(x, e) is ill-sorted: act expects (M, X) but its first argument
    # is the X-sorted bound variable. The binder sort must be ENFORCED on the body.
    bad = forall("x", "X", Eq(act(Var("x", "X"), E), Var("x", "X")))
    try:
        sort_check_formula(bad, ACTION_SIG)
    except ValueError:
        return
    raise AssertionError("ill-sorted quantifier body was accepted")


def test_exists_quantified_sorted_formula_sort_checks():
    # The existential side works the same way: exists x:X. act(e,x) = x.
    sort_check_formula(exists("x", "X", ACT_ID), ACTION_SIG)


def test_cross_sort_instantiation_under_quantifier_rejected():
    # The Inst cross-sort guard must see a free variable even inside a quantified
    # conclusion: instantiating m:M with an X-term stays a sort error.
    phi = forall("y", "X", M_LEFT_ID)  # forall y:X. e*m = m  (m:M still free)
    bad = P.Inst(P.Assume(phi), "m", Var("z", "X"))  # m:M <- z:X
    try:
        check(bad, MONOID_ACTION)
    except ValueError:
        return
    raise AssertionError("cross-sort instantiation under a quantifier was allowed")
