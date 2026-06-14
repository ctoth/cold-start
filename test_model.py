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

import cold_start.proof as P
from cold_start.checker import Theory, check
from cold_start.peano import ADD_SUCC_F, ADD_ZERO_F, PEANO, ZERO, S, add, numeral
from cold_start.proofs import add_proof
from cold_start.syntax import (
    Eq,
    Formula,
    Fun,
    Implies,
    Term,
    Var,
    formula_subst,
)

VAR_POOL = ["x", "y", "z", "n", "m", "a", "b"]
VAR_NAMES = st.sampled_from(VAR_POOL)
# One environment binds every name in the pool, so any free var is covered.
ENV = st.fixed_dictionaries({name: st.integers(0, 8) for name in VAR_POOL})


# --- the standard model N -------------------------------------------------


class Uninterpretable(Exception):
    """A term/formula outside the arithmetic signature {0, S, +, =, ->}."""


def eval_term(t: Term, env: dict) -> int:
    if isinstance(t, Var):
        return env[t.name]
    if isinstance(t, Fun):
        if t.name == "0" and len(t.args) == 0:
            return 0
        if t.name == "S" and len(t.args) == 1:
            return eval_term(t.args[0], env) + 1
        if t.name == "+" and len(t.args) == 2:
            return eval_term(t.args[0], env) + eval_term(t.args[1], env)
    raise Uninterpretable(repr(t))


def eval_formula(f: Formula, env: dict) -> bool:
    if isinstance(f, Eq):
        return eval_term(f.lhs, env) == eval_term(f.rhs, env)
    if isinstance(f, Implies):
        return (not eval_formula(f.ant, env)) or eval_formula(f.con, env)
    raise Uninterpretable(repr(f))


def test_evaluator_sanity():
    # The interpreter itself must agree with arithmetic, or the probes are moot.
    assert eval_term(numeral(3), {}) == 3
    assert eval_term(add(numeral(2), numeral(2)), {}) == 4
    assert eval_formula(Eq(add(numeral(2), numeral(2)), numeral(4)), {})
    assert not eval_formula(Eq(numeral(1), ZERO), {})
    assert eval_formula(Eq(add(ZERO, Var("n")), Var("n")), {"n": 5})  # 0+n=n


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
        st.builds(Eq, nat_terms(), nat_terms()),
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
    assert eval_formula(seq.concl, env), f"UNSOUND: derived {seq!r}, false at {env}"


@given(checked_proofs(), ENV)
@settings(max_examples=300, deadline=None, suppress_health_check=[HealthCheck.too_slow])
def test_forward_proofs_are_model_sound(pf, env):
    seq = check(pf, PEANO)  # accepted by construction
    assume(not seq.hyps)
    assert eval_formula(seq.concl, env), f"UNSOUND: derived {seq!r}, false at {env}"


@given(ENV)
def test_declared_axioms_are_true_in_N(env):
    for ax in PEANO.axioms:
        assert eval_formula(ax, env), f"false axiom in the trusted base: {ax!r}"


@given(nat_formulas(), VAR_NAMES, ENV)
@settings(max_examples=400)
def test_no_accepted_formula_is_false(pred, x, env):
    """The axiom-soundness invariant that the induction bug violated: anything
    Theory.accepts must be true in N. We probe the danger zone explicitly by
    building induction-schema-shaped formulas -- exactly what the old recognizer
    wrongly accepted as axioms."""
    schema = Implies(
        formula_subst(pred, x, ZERO),
        Implies(Implies(pred, formula_subst(pred, x, S(Var(x)))), pred),
    )
    for f in (schema, pred):
        if PEANO.accepts(f):
            assert eval_formula(f, env), f"accepted-but-FALSE axiom: {f!r} at {env}"


def test_induction_schema_formula_is_false_in_N():
    """Why the old design was unsound, stated in the model: the schema formula
    P[0] -> ((P -> P[Sx]) -> P), for P(n):=n=0, is FALSE at x=1. Asserting it as
    an axiom was the bug; the fixed checker does not accept it."""
    x = Var("x")
    pred = Eq(x, ZERO)
    schema = Implies(
        formula_subst(pred, "x", ZERO),
        Implies(Implies(pred, formula_subst(pred, "x", S(x))), pred),
    )
    assert not eval_formula(schema, {"x": 1})  # 0=0 -> ((1=0->2=0) -> 1=0) is False
    assert not PEANO.accepts(schema)  # and the rule-based checker won't take it


def test_model_probe_is_not_vacuous():
    """Meta-test: the soundness invariant (accepted ==> true in N) would actually
    fire on a theory that wrongly accepts the false induction schema. Guards the
    probes from silently passing because they never see anything bad."""
    x = Var("x")
    pred = Eq(x, ZERO)
    schema = Implies(
        formula_subst(pred, "x", ZERO),
        Implies(Implies(pred, formula_subst(pred, "x", S(x))), pred),
    )
    bad = Theory(axioms=frozenset({schema}), zero=ZERO, succ="S")
    assert bad.accepts(schema) and not eval_formula(schema, {"x": 1})


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
    assert not eval_formula(seq.concl, {}), "evaluator failed to flag |- 1=0"


@given(st.integers(0, 40), st.integers(0, 40))
@settings(deadline=None)
def test_addition_proofs_are_true_in_N(a, b):
    """The checker's addition proofs conclude an equation that holds in N: both
    sides evaluate to a + b. A checker that proved numeral(a) = numeral(c) for
    c != a+b would be caught here."""
    seq = check(add_proof(a, b), PEANO)
    assert isinstance(seq.concl, Eq)
    lhs, rhs = eval_term(seq.concl.lhs, {}), eval_term(seq.concl.rhs, {})
    assert lhs == rhs == a + b
