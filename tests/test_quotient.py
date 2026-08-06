"""k-dimensional quotient interpretations: the general TMR bridge machinery.

`cold_start.interp` handles one-dimensional interpretations whose source
equality stays absolute. The general Tarski-Mostowski-Robinson notion lets a
source element be a k-TUPLE of target elements and lets source equality land
on a DEFINED equivalence, which the artifact must then prove is an equivalence
respected by every translated symbol. These tests specify that machinery on
the motivating instance: pairs of naturals (a, b) read as the integer a - b,
equivalent when a + d = c + b.
"""

from __future__ import annotations

import pytest

from cold_start.algebra import R0
from cold_start.algebra import add as z_add
from cold_start.checker import check
from cold_start.interp import InterpError
from cold_start.presburger import PRESBURGER, add
from cold_start.proof import Assume
from cold_start.quotient import (
    QuotientInterpretation,
    VecSymbol,
    obligations,
    translate,
    vec,
    verify,
)
from cold_start.syntax import Eq, Formula, Implies, Term, Var, exists, forall
from cold_start.tactics import prove_eq
from cold_start.theory import Theory

Vec = tuple[Term, ...]

_x, _y = Var("x"), Var("y")


def eps(p: Vec, q: Vec) -> Formula:
    """(p1, p2) ~ (q1, q2)  :=  p1 + q2 = q1 + p2  -- same difference."""
    return Eq(add(p[0], q[1]), add(q[0], p[1]))


def g_zero(args: tuple[Vec, ...], res: Vec) -> Formula:
    return Eq(res[0], res[1])


def g_add(args: tuple[Vec, ...], res: Vec) -> Formula:
    (a, b) = args
    return eps((add(a[0], b[0]), add(a[1], b[1])), res)


def g_neg(args: tuple[Vec, ...], res: Vec) -> Formula:
    (a,) = args
    return eps((a[1], a[0]), res)


ZED = VecSymbol("0", 0, g_zero)
PLUS = VecSymbol("+", 2, g_add)
NEG = VecSymbol("neg", 1, g_neg)
SYMBOLS = (ZED, PLUS, NEG)


def _interp(source: Theory, payments: tuple = ()) -> QuotientInterpretation:
    return QuotientInterpretation(
        name="probe",
        source=source,
        target=PRESBURGER,
        dim=2,
        equiv=eps,
        symbols=SYMBOLS,
        payments=payments,
    )


# --- vectors ---------------------------------------------------------------


def test_vec_names_components() -> None:
    assert vec("x", 2) == (Var("x.1"), Var("x.2"))
    assert vec("u!0", 3) == (Var("u!0.1"), Var("u!0.2"), Var("u!0.3"))


# --- the translator --------------------------------------------------------


def test_translate_bare_variable_equation_is_the_equivalence() -> None:
    # x = y  ↦  x.1 + y.2 = y.1 + x.2
    got = translate(Eq(_x, _y), SYMBOLS, eps, 2)
    assert got == eps(vec("x", 2), vec("y", 2))


def test_translate_hoists_nested_applications_into_pair_guards() -> None:
    # x + 0 = x: the constant hoists to the pair u!, the sum to u!0, and the
    # atom is the equivalence of u!0 with x -- every quantifier ranging over
    # both components, first hoist outermost.
    axiom = Eq(z_add(_x, R0), _x)
    u, u0 = vec("u!", 2), vec("u!0", 2)
    want = forall(
        "u!.1",
        "",
        forall(
            "u!.2",
            "",
            Implies(
                g_zero((), u),
                forall(
                    "u!0.1",
                    "",
                    forall(
                        "u!0.2",
                        "",
                        Implies(g_add((vec("x", 2), u), u0), eps(u0, vec("x", 2))),
                    ),
                ),
            ),
        ),
    )
    assert translate(axiom, SYMBOLS, eps, 2) == want


def test_translate_structure_and_rejections() -> None:
    # Implication structure survives; unknown symbols and binders are refused.
    f = Implies(Eq(_x, _y), Eq(_y, _x))
    got = translate(f, SYMBOLS, eps, 2)
    assert got == Implies(eps(vec("x", 2), vec("y", 2)), eps(vec("y", 2), vec("x", 2)))
    from cold_start.peano import mul

    with pytest.raises(InterpError):
        translate(Eq(mul(_x, _y), _x), SYMBOLS, eps, 2)
    with pytest.raises(InterpError):
        translate(exists("k", "", Eq(Var("k"), _x)), SYMBOLS, eps, 2)


# --- obligations -----------------------------------------------------------


def _tiny() -> Theory:
    return Theory(axioms=frozenset({Eq(_x, _x)}))


def test_obligations_cover_equivalence_definedness_and_axioms() -> None:
    labels = {o.label for o in obligations(_interp(_tiny()))}
    assert labels == {
        "equivalence:refl",
        "equivalence:sym",
        "equivalence:trans",
        "totality:0",
        "respect:0",
        "totality:+",
        "respect:+",
        "totality:neg",
        "respect:neg",
        f"axiom:{Eq(_x, _x)!r}",
    }


def test_equivalence_obligations_have_canonical_shapes() -> None:
    obs = {o.label: o.formula for o in obligations(_interp(_tiny()))}
    a, b, c = vec("x!", 2), vec("y!", 2), vec("z!", 2)
    assert obs["equivalence:refl"] == eps(a, a)
    assert obs["equivalence:sym"] == Implies(eps(a, b), eps(b, a))
    assert obs["equivalence:trans"] == Implies(eps(a, b), Implies(eps(b, c), eps(a, c)))


def test_definedness_obligations_quantify_component_wise() -> None:
    obs = {o.label: o.formula for o in obligations(_interp(_tiny()))}
    args = (vec("x!0", 2), vec("x!1", 2))
    c = vec("c!", 2)
    want_tot = exists("c!.1", "", exists("c!.2", "", g_add(args, c)))
    assert obs["totality:+"] == want_tot

    primed = (vec("y!0", 2), vec("y!1", 2))
    d = vec("d!", 2)
    want_resp: Formula = Implies(g_add(args, c), Implies(g_add(primed, d), eps(c, d)))
    for old, new in reversed(tuple(zip(args, primed, strict=True))):
        want_resp = Implies(eps(old, new), want_resp)
    assert obs["respect:+"] == want_resp


# --- verification ----------------------------------------------------------


def test_verify_accepts_payment_reports_toll_and_open_debts() -> None:
    from cold_start.presburger_proofs import add_kit

    label = f"axiom:{Eq(_x, _x)!r}"
    refl_goal = eps(vec("x", 2), vec("x", 2))
    interp = _interp(_tiny(), payments=((label, prove_eq(refl_goal, add_kit())),))
    report = verify(interp)
    by_label = {s.obligation.label: s for s in report.statuses}
    assert by_label[label].paid and by_label[label].toll > 0
    assert not report.complete
    assert "equivalence:trans" in report.open_labels()
    assert report.bridge_size > 0
    # The payment really is a target theorem of the owed shape.
    seq = check(dict(interp.payments)[label], PRESBURGER)
    assert not seq.hyps and seq.concl == by_label[label].obligation.formula


def test_verify_rejects_wrong_conditional_and_unknown_payments() -> None:
    label = f"axiom:{Eq(_x, _x)!r}"
    wrong = _interp(_tiny(), payments=((label, prove_eq(Eq(_x, _x), ())),))
    with pytest.raises(InterpError):
        verify(wrong)
    conditional = _interp(_tiny(), payments=((label, Assume(eps(vec("x", 2), vec("x", 2)))),))
    with pytest.raises(InterpError):
        verify(conditional)
    unknown = _interp(_tiny(), payments=(("axiom:nonsense", prove_eq(Eq(_x, _x), ())),))
    with pytest.raises(InterpError):
        verify(unknown)
