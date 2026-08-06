"""Interpretations as checked artifacts: the bridge machinery.

An interpretation translates a source theory's language into a target theory's
and owes one proof obligation per source axiom plus definedness (totality and
uniqueness) per relationally-translated function symbol. `verify` drives every
payment through the trusted `check` and reports bridge size against toll paid.
Authority stays with the checker: this module is untrusted tooling, and a wrong
payment must be rejected, not massaged.

The concrete landmark exercised here is Robinson's §2: translating base-1
Presburger's addition into the (1, S, ·) theory over her bridge identity. The
translator must land the two addition axioms EXACTLY on Robinson's axioms
A4' and A5' -- the bridge carries axioms onto axioms.
"""

from __future__ import annotations

import pytest

from cold_start.interp import (
    GraphSymbol,
    InterpError,
    Interpretation,
    ObligationKey,
    obligations,
    translate,
    verify,
)
from cold_start.proof import Axiom, Refl
from cold_start.robinson import ADD_ONE, ADD_SUCC, ONE, ROBINSON_PEANO, bridge
from cold_start.syntax import Eq, Implies, Not, Var, exists, forall
from cold_start.vocabulary import S, add

_a, _b, _c, _d = Var("a"), Var("b"), Var("c"), Var("d")

PLUS = GraphSymbol("+", 2, lambda args, res: bridge(args[0], args[1], res))


# --- the translator -------------------------------------------------------


def test_translate_leaves_plus_free_formulas_alone() -> None:
    f = Implies(Eq(S(_a), S(_b)), Eq(_a, _b))
    assert translate(f, (PLUS,)) == f


def test_translate_lands_base_one_add_one_on_a4() -> None:
    # a + 1 = S(a)  ↦  bridge(a, 1, S(a))  -- Robinson's A4', verbatim.
    p3 = Eq(add(_a, ONE), S(_a))
    assert translate(p3, (PLUS,)) == ADD_ONE


def test_translate_lands_base_one_add_succ_on_a5() -> None:
    # a + S(b) = S(a + b)  ↦  ∀c (bridge(a,b,c) → bridge(a, S b, S c)) -- the
    # universal closure of Robinson's A5', whose free `c` is implicitly
    # universal. One ForallIntro pays the debt from the axiom itself.
    p4 = Eq(add(_a, S(_b)), S(add(_a, _b)))
    got = translate(p4, (PLUS,))
    want = forall("c", "", Implies(bridge(_a, _b, _c), bridge(_a, S(_b), S(_c))))
    assert got == want

    from cold_start.checker import check
    from cold_start.proof import ForallIntro

    payment = ForallIntro("c", "", Axiom(ADD_SUCC))
    seq = check(payment, ROBINSON_PEANO)
    assert not seq.hyps and seq.concl == got


def test_translate_unnests_nested_sums() -> None:
    # a + (b + c) = d  ↦  ∀u (bridge(b,c,u) → bridge(a,u,d))
    f = Eq(add(_a, add(_b, _c)), _d)
    u = Var("u!")
    want = forall("u!", "", Implies(bridge(_b, _c, u), bridge(_a, u, _d)))
    assert translate(f, (PLUS,)) == want


def test_translate_rejects_binders_in_the_source() -> None:
    with pytest.raises(InterpError):
        translate(exists("k", "", Eq(add(_a, Var("k")), _b)), (PLUS,))


# --- obligations ----------------------------------------------------------


def _bare(source, **kw):
    """An Interpretation with no payments -- obligations only need the shape."""
    retained = tuple(
        (name, len(args))
        for name, args, _result in source.signature.ranks
        if name != "+"
    ) if source.signature is not None else ()
    retained_relations = tuple(
        name for name, _args in source.signature.relations
    ) if source.signature is not None else ()
    supplied = {
        "retained_funs": retained,
        "retained_predicates": retained_relations,
        **kw,
    }
    return Interpretation(
        name="probe",
        source=source,
        target=ROBINSON_PEANO,
        symbols=(PLUS,),
        **supplied,
    )


def test_obligations_cover_axioms_and_definedness() -> None:
    obs = obligations(_bare(ROBINSON_PEANO))  # any theory works as a source
    labels = {o.label for o in obs}
    assert "totality:+" in labels
    assert "uniqueness:+" in labels
    assert sum(1 for o in obs if o.label.startswith("axiom:")) == len(ROBINSON_PEANO.axioms)


def test_definedness_formulas_have_the_graph_shape() -> None:
    obs = {o.label: o.formula for o in obligations(_bare(ROBINSON_PEANO))}
    x, y = Var("x!0"), Var("x!1")
    c, d = Var("c!"), Var("d!")
    assert obs["totality:+"] == exists("c!", "", bridge(x, y, Var("c!")))
    assert obs["uniqueness:+"] == Implies(
        bridge(x, y, c), Implies(bridge(x, y, d), Eq(c, d))
    )


# --- relativization -------------------------------------------------------


def _delta(t):
    return exists("k", "", Eq(t, S(Var("k"))))


def test_relativized_axiom_guards_free_vars_and_hoists() -> None:
    # a + S(b) = S(a + b) relativized: δ guards the free variables outermost
    # (sorted) and the hoisted quantifier ranges over the domain.
    p4 = Eq(add(_a, S(_b)), S(add(_a, _b)))
    from cold_start.interp import translate_axiom

    got = translate_axiom(p4, (PLUS,), _delta)
    want = Implies(
        _delta(_a),
        Implies(
            _delta(_b),
            forall(
                "c",
                "",
                Implies(_delta(_c), Implies(bridge(_a, _b, _c), bridge(_a, S(_b), S(_c)))),
            ),
        ),
    )
    assert got == want


def test_relativized_obligations_add_domain_debts() -> None:
    one = ONE
    interp = _bare(
        ROBINSON_PEANO,
        domain=_delta,
        retained_funs=(("1", 0), ("S", 1), ("*", 2)),
        retained_consts=(one,),
    )
    obs = {o.label: o.formula for o in obligations(interp)}
    assert "domain:nonempty" in obs
    assert obs["closure:S"] == Implies(_delta(Var("x!0")), _delta(S(Var("x!0"))))
    assert obs[f"closure:{one!r}"] == _delta(one)

    # Guarded totality packs domain membership with the graph via And.
    from cold_start.prop import And

    x, y, c = Var("x!0"), Var("x!1"), Var("c!")
    want_tot = Implies(
        _delta(x),
        Implies(_delta(y), exists("c!", "", And(_delta(c), bridge(x, y, c)))),
    )
    assert obs["totality:+"] == want_tot


# --- verification ---------------------------------------------------------


def _tiny_source() -> object:
    """A one-axiom source theory whose translation is a ROBINSON_PEANO axiom."""
    from cold_start.theory import Theory

    return Theory(axioms=frozenset({Eq(add(_a, ONE), S(_a))}))


def test_verify_accepts_a_correct_payment_and_reports_toll() -> None:
    source = _tiny_source()
    interp = Interpretation(
        name="tiny",
        source=source,  # type: ignore[arg-type]
        target=ROBINSON_PEANO,
        symbols=(PLUS,),
        payments=((ObligationKey.axiom(Eq(add(_a, ONE), S(_a))), Axiom(ADD_ONE)),),
    )
    report = verify(interp)
    by_label = {s.obligation.label: s for s in report.statuses}
    axiom_status = by_label["axiom:" + repr(Eq(add(_a, ONE), S(_a)))]
    assert axiom_status.paid and axiom_status.toll > 0
    assert not by_label["totality:+"].paid
    assert not report.complete
    assert report.bridge_size > 0
    assert report.total_toll == axiom_status.toll


def test_verify_rejects_a_wrong_payment() -> None:
    source = _tiny_source()
    interp = Interpretation(
        name="tiny-wrong",
        source=source,  # type: ignore[arg-type]
        target=ROBINSON_PEANO,
        symbols=(PLUS,),
        payments=((ObligationKey.axiom(Eq(add(_a, ONE), S(_a))), Refl(_a)),),
    )
    with pytest.raises(InterpError):
        verify(interp)


def test_verify_rejects_a_conditional_payment() -> None:
    # A payment whose sequent carries hypotheses is not a theorem of the target.
    from cold_start.proof import Assume

    source = _tiny_source()
    key = ObligationKey.axiom(Eq(add(_a, ONE), S(_a)))
    interp = Interpretation(
        name="tiny-conditional",
        source=source,  # type: ignore[arg-type]
        target=ROBINSON_PEANO,
        symbols=(PLUS,),
        payments=((key, Assume(ADD_ONE)),),
    )
    with pytest.raises(InterpError):
        verify(interp)


def test_verify_rejects_an_unknown_label() -> None:
    source = _tiny_source()
    interp = Interpretation(
        name="tiny-unknown",
        source=source,  # type: ignore[arg-type]
        target=ROBINSON_PEANO,
        symbols=(PLUS,),
        payments=((ObligationKey.axiom(Eq(_a, _a)), Axiom(ADD_ONE)),),
    )
    with pytest.raises(InterpError):
        verify(interp)


def test_translate_negated_atom() -> None:
    # ¬(a + 1 = 1) ↦ ¬bridge(a, 1, 1): translation commutes with the encoding
    # of negation as →⊥.
    f = Not(Eq(add(_a, ONE), ONE))
    assert translate(f, (PLUS,)) == Not(bridge(_a, ONE, ONE))
