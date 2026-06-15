"""Model-soundness probes (Hypothesis).

The induction bug slipped past every example test because they all checked that
*valid* things pass. The invariant that actually matters is the converse: the
checker must never accept a proof of something *false*. So we interpret the
arithmetic signature in the standard model N and assert:

    if check(pf, PEANO) returns a closed sequent  |- phi,
    then phi is true in N (for every assignment to its free variables).

Free variables are implicitly universally quantified, so we sample assignments
(the var pool is fixed and small, so one fixed-dict draw covers them all).
"""

from __future__ import annotations

from hypothesis import HealthCheck, assume, given, settings
from hypothesis import strategies as st
from semantics import Model, evaluate

import cold_start.proof as P
from cold_start.checker import Theory, check
from cold_start.peano import ADD_SUCC_F, ADD_ZERO_F, PEANO, ZERO, S, add, numeral
from cold_start.proofs import add_proof
from cold_start.syntax import (
    Bottom,
    Eq,
    Fun,
    Implies,
    Var,
    subst,
)

VAR_POOL = ["x", "y", "z", "n", "m", "a", "b"]
VAR_NAMES = st.sampled_from(VAR_POOL)
# One environment binds every name in the pool, so any free var is covered.
ENV = st.fixed_dictionaries({name: st.integers(0, 8) for name in VAR_POOL})


# --- the standard model N -------------------------------------------------


N = Model(
    "N",
    interp={"0": lambda: 0, "S": lambda x: x + 1, "+": lambda a, b: a + b},
)


def test_evaluator_sanity():
    # The interpreter itself must agree with arithmetic, or the probes are moot.
    assert evaluate(numeral(3), N, {}) == 3
    assert evaluate(add(numeral(2), numeral(2)), N, {}) == 4
    assert evaluate(Eq(add(numeral(2), numeral(2)), numeral(4)), N, {})
    assert not evaluate(Eq(numeral(1), ZERO), N, {})
    assert evaluate(Eq(add(ZERO, Var("n")), Var("n")), N, {"n": 5})  # 0+n=n


# --- arithmetic-signature strategies --------------------------------------


def nat_terms():
    return st.recursive(
        st.one_of(st.builds(Var, VAR_NAMES), st.just(ZERO)),
        lambda kids: st.one_of(
            st.builds(lambda t: Fun("S", (t,)), kids),
            st.builds(lambda a, b: Fun("+", (a, b)), kids, kids),
        ),
        max_leaves=6,
    )


def nat_formulas():
    return st.recursive(
        st.one_of(st.builds(Eq, nat_terms(), nat_terms()), st.just(Bottom())),
        lambda kids: st.builds(Implies, kids, kids),
        max_leaves=5,
    )


def nat_proofs():
    """Arbitrary proof terms over the arithmetic signature. Most are rejected;
    the ones the checker *accepts* are what we hold to the model."""
    leaf = st.one_of(
        st.just(P.Axiom(ADD_ZERO_F)),
        st.just(P.Axiom(ADD_SUCC_F)),
        st.builds(P.Axiom, nat_formulas()),  # probes Theory.accepts directly
        st.builds(P.Refl, nat_terms()),
        st.builds(P.Assume, nat_formulas()),
    )
    return st.recursive(
        leaf,
        lambda kids: st.one_of(
            st.builds(P.Sym, kids),
            st.builds(P.Trans, kids, kids),
            st.builds(lambda a: P.Cong("S", (a,)), kids),
            st.builds(lambda a, b: P.Cong("+", (a, b)), kids, kids),
            st.builds(P.MP, kids, kids),
            st.builds(P.ImpIntro, nat_formulas(), kids),
            st.builds(P.Inst, kids, VAR_NAMES, nat_terms()),
            st.builds(P.Induct, VAR_NAMES, nat_formulas(), kids, kids),
            st.builds(P.ExFalso, kids, nat_formulas()),
            st.builds(P.RAA, nat_formulas(), kids),
        ),
        max_leaves=12,
    )


@st.composite
def checked_proofs(draw):
    """Forward-construct proofs by applying rule constructors to facts already
    derived, keeping only those the checker accepts. Returns a random accepted
    proof -- reaches deeper real theorems than blind random generation."""
    facts: list[tuple] = []  # (Pf, Sequent)

    def add(pf) -> None:
        try:
            seq = check(pf, PEANO)
        except (TypeError, ValueError):
            return
        facts.append((pf, seq))

    add(P.Axiom(ADD_ZERO_F))
    add(P.Axiom(ADD_SUCC_F))
    for t in (ZERO, Var("n"), Var("m")):
        add(P.Refl(t))

    for _ in range(draw(st.integers(2, 10))):
        rule = draw(st.sampled_from(["sym", "trans", "congS", "inst", "impintro", "mp"]))
        if rule == "sym":
            add(P.Sym(draw(st.sampled_from(facts))[0]))
        elif rule == "trans":
            add(P.Trans(draw(st.sampled_from(facts))[0], draw(st.sampled_from(facts))[0]))
        elif rule == "congS":
            add(P.Cong("S", (draw(st.sampled_from(facts))[0],)))
        elif rule == "inst":
            add(P.Inst(draw(st.sampled_from(facts))[0], draw(VAR_NAMES), draw(nat_terms())))
        elif rule == "impintro":
            add(P.ImpIntro(draw(nat_formulas()), draw(st.sampled_from(facts))[0]))
        elif rule == "mp":
            add(P.MP(draw(st.sampled_from(facts))[0], draw(st.sampled_from(facts))[0]))

    return draw(st.sampled_from([pf for pf, _ in facts]))


# --- the probes -----------------------------------------------------------


@given(nat_proofs(), ENV)
@settings(max_examples=400, deadline=None)
def test_arbitrary_proofs_are_model_sound(pf, env):
    try:
        seq = check(pf, PEANO)
    except (TypeError, ValueError):
        return
    assume(not seq.hyps)  # only closed theorems carry unconditional truth
    assert evaluate(seq.concl, N, env), f"UNSOUND: derived {seq!r}, false at {env}"


@given(checked_proofs(), ENV)
@settings(max_examples=300, deadline=None, suppress_health_check=[HealthCheck.too_slow])
def test_forward_proofs_are_model_sound(pf, env):
    seq = check(pf, PEANO)  # accepted by construction
    assume(not seq.hyps)
    assert evaluate(seq.concl, N, env), f"UNSOUND: derived {seq!r}, false at {env}"


@given(ENV)
def test_declared_axioms_are_true_in_N(env):
    for ax in PEANO.axioms:
        assert evaluate(ax, N, env), f"false axiom in the trusted base: {ax!r}"


@given(nat_formulas(), VAR_NAMES, ENV)
@settings(max_examples=400)
def test_no_accepted_formula_is_false(pred, x, env):
    """The axiom-soundness invariant that the induction bug violated: anything
    Theory.accepts must be true in N. We probe the danger zone explicitly by
    building induction-schema-shaped formulas -- exactly what the old recognizer
    wrongly accepted as axioms."""
    schema = Implies(
        subst(pred, x, ZERO),
        Implies(Implies(pred, subst(pred, x, S(Var(x)))), pred),
    )
    for f in (schema, pred):
        if PEANO.accepts(f):
            assert evaluate(f, N, env), f"accepted-but-FALSE axiom: {f!r} at {env}"


def test_induction_schema_formula_is_false_in_N():
    """Why the old design was unsound, stated in the model: the schema formula
    P[0] -> ((P -> P[Sx]) -> P), for P(n):=n=0, is FALSE at x=1. Asserting it as
    an axiom was the bug; the fixed checker does not accept it."""
    x = Var("x")
    pred = Eq(x, ZERO)
    schema = Implies(
        subst(pred, "x", ZERO),
        Implies(Implies(pred, subst(pred, "x", S(x))), pred),
    )
    assert not evaluate(schema, N, {"x": 1})  # 0=0 -> ((1=0->2=0) -> 1=0) is False
    assert not PEANO.accepts(schema)  # and the rule-based checker won't take it


def test_model_probe_is_not_vacuous():
    """Meta-test: the soundness invariant (accepted ==> true in N) would actually
    fire on a theory that wrongly accepts the false induction schema. Guards the
    probes from silently passing because they never see anything bad."""
    x = Var("x")
    pred = Eq(x, ZERO)
    schema = Implies(
        subst(pred, "x", ZERO),
        Implies(Implies(pred, subst(pred, "x", S(x))), pred),
    )
    bad = Theory(axioms=frozenset({schema}), zero=ZERO, succ="S")
    assert bad.accepts(schema) and not evaluate(schema, N, {"x": 1})


def test_model_net_catches_end_to_end_unsoundness():
    """End-to-end proof the net works: against a theory that wrongly accepts the
    induction schema, the original exploit derives |- 1=0, and the evaluator
    flags it false. This is exactly what the broad probes surface for any
    reachable unsoundness -- here forced deterministically."""
    x = Var("x")
    pred = Eq(x, ZERO)
    one = S(ZERO)
    schema = Implies(Eq(ZERO, ZERO), Implies(Implies(pred, Eq(S(x), ZERO)), pred))
    bad = Theory(axioms=frozenset({schema}), zero=ZERO, succ="S")
    inst = P.Inst(P.Axiom(schema), "x", one)
    assume1 = P.Assume(Eq(one, ZERO))
    step = P.ImpIntro(Eq(one, ZERO), P.Trans(P.Cong("S", (assume1,)), assume1))
    exploit = P.MP(P.MP(inst, P.Refl(ZERO)), step)
    seq = check(exploit, bad)  # the BAD theory accepts it
    assert seq.hyps == frozenset()
    assert not evaluate(seq.concl, N, {}), "evaluator failed to flag |- 1=0"


@given(st.integers(0, 40), st.integers(0, 40))
@settings(deadline=None)
def test_addition_proofs_are_true_in_N(a, b):
    """The checker's addition proofs conclude an equation that holds in N: both
    sides evaluate to a + b. A checker that proved numeral(a) = numeral(c) for
    c != a+b would be caught here."""
    seq = check(add_proof(a, b), PEANO)
    assert isinstance(seq.concl, Eq)
    lhs, rhs = evaluate(seq.concl.lhs, N, {}), evaluate(seq.concl.rhs, N, {})
    assert lhs == rhs == a + b


# --- each inference rule preserves model truth ----------------------------
# Local soundness: a rule, applied to model-valid premises, yields a model-valid
# conclusion. Together with "the checker only applies the rules" (the broad/
# forward nets above) this gives global soundness. A sequent is valid at an
# assignment when its hypotheses being all true forces its conclusion true.


def model_valid(seq, env) -> bool:
    if any(not evaluate(h, N, env) for h in seq.hyps):
        return True  # vacuously valid: some hypothesis is false here
    return evaluate(seq.concl, N, env)


def eq_proofs():
    """Proof terms that always check to an equality true in N for *every*
    assignment: reflexivity, and the concrete addition proofs."""
    return st.one_of(
        st.builds(P.Refl, nat_terms()),
        st.builds(add_proof, st.integers(0, 6), st.integers(0, 6)),
    )


@given(eq_proofs(), ENV)
def test_sym_preserves_validity(p, env):
    premise = check(p, PEANO)
    concl = check(P.Sym(p), PEANO)
    if model_valid(premise, env):
        assert model_valid(concl, env)


@given(eq_proofs(), ENV)
def test_trans_preserves_validity(p, env):
    premise = check(p, PEANO)
    assert isinstance(premise.concl, Eq)
    chained = check(P.Trans(p, P.Refl(premise.concl.rhs)), PEANO)  # a=b then b=b
    if model_valid(premise, env):
        assert model_valid(chained, env)


@given(eq_proofs(), ENV)
def test_cong_preserves_validity(p, env):
    premise = check(p, PEANO)
    concl = check(P.Cong("S", (p,)), PEANO)  # a = b  ==>  S a = S b
    if model_valid(premise, env):
        assert model_valid(concl, env)


@given(eq_proofs(), ENV)
def test_mp_preserves_validity(p, env):
    a = check(p, PEANO).concl
    imp = P.ImpIntro(a, P.Assume(a))  # |- a -> a
    concl = check(P.MP(imp, p), PEANO)  # |- a
    if model_valid(check(p, PEANO), env):
        assert model_valid(concl, env)


@given(eq_proofs(), nat_formulas(), ENV)
def test_impintro_preserves_validity(p, h, env):
    premise = check(p, PEANO)
    concl = check(P.ImpIntro(h, p), PEANO)  # G\{h} |- h -> premise
    if model_valid(premise, env):
        assert model_valid(concl, env)


@given(eq_proofs(), VAR_NAMES, nat_terms(), ENV)
def test_inst_preserves_validity(p, x, t, env):
    # eq_proofs are valid for every assignment, so every instance is valid too.
    concl = check(P.Inst(p, x, t), PEANO)
    assert model_valid(concl, env)


@given(nat_formulas(), VAR_NAMES, nat_terms(), ENV)
def test_substitution_lemma(phi, x, t, env):
    """The semantic core of Inst: evaluating after substitution equals
    evaluating in the shifted environment. A subst/eval mismatch breaks this."""
    shifted = dict(env)
    shifted[x] = evaluate(t, N, env)
    assert evaluate(subst(phi, x, t), N, env) == evaluate(phi, N, shifted)


@given(nat_formulas(), VAR_NAMES, st.integers(1, 6), ENV)
@settings(suppress_health_check=[HealthCheck.filter_too_much])
def test_induction_principle_holds_in_N(pred, x, bound, env):
    """The semantic justification of the Induct rule: in N, base + step up to a
    bound forces the predicate up to that bound."""
    base_ok = evaluate(subst(pred, x, ZERO), N, env)
    step_ok = all(
        evaluate(
            Implies(
                subst(pred, x, numeral(k)),
                subst(pred, x, numeral(k + 1)),
            ), N,
            env,
        )
        for k in range(bound)
    )
    assume(base_ok and step_ok)
    assert all(
        evaluate(subst(pred, x, numeral(k)), N, env) for k in range(bound + 1)
    )
