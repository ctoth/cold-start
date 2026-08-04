"""The Grothendieck bridge: the integers, interpreted into Presburger.

The naturals have no subtraction, and `x + (-x) = 0` is flatly false of them.
The classical repair (Grothendieck's difference construction) is to let a PAIR
`(a, b)` of naturals denote the integer `a - b` and to declare two pairs equal
when they name the same difference:

    (a, b) ~ (c, d)   :=   a + d = c + b

-- an equation the naturals CAN speak, since it never subtracts. Over that
defined equivalence the theory of abelian groups interprets into plain
Presburger arithmetic, two-dimensionally:

    0        becomes  the diagonal        c.1 = c.2
    x + y    becomes  componentwise sum   (x.1 + y.1, x.2 + y.2)
    neg(x)   becomes  the swap            (x.2, x.1)

This is the first artifact of the k-dimensional quotient machinery
(`cold_start.quotient`), and EVERY obligation is paid: the three equivalence
laws, totality and respect for all three symbols, and the four translated
group axioms -- including the inverse axiom, which lands as a theorem of a
theory with no negative numbers in it anywhere.

Every payment is one cancellation argument: sum the hypotheses with `Cong`,
shuffle with the ordered AC rewriting of `add_kit`, and cancel the common
suffix with `add_cancel_right`. That recipe -- `combination.by_combination`
with every coefficient `None` -- is this module's whole proof engine.

Untrusted, like every prover module: `check` remains the only judge.
"""

from __future__ import annotations

from .algebra import AB_GROUP, ADD_ASSOC, ADD_COMM, ADD_NEG, ADD_ZERO
from .combination import Hypothesis, by_combination
from .presburger import PRESBURGER, ZERO, add
from .presburger_proofs import add_kit
from .proof import (
    Assume,
    ExistsIntro,
    ForallIntro,
    ImpIntro,
    Pf,
    Refl,
    Sym,
)
from .quotient import QuotientInterpretation, Vec, VecSymbol, vec
from .syntax import Eq, Formula, Term, exists

# ---------------------------------------------------------------------------
# The translation
# ---------------------------------------------------------------------------


def int_eq(p: Vec, q: Vec) -> Eq:
    """(p1, p2) ~ (q1, q2)  :=  p1 + q2 = q1 + p2  -- the same difference."""
    return Eq(add(p[0], q[1]), add(q[0], p[1]))


def _g_zero(args: tuple[Vec, ...], res: Vec) -> Eq:
    return Eq(res[0], res[1])


def _g_add(args: tuple[Vec, ...], res: Vec) -> Eq:
    a, b = args
    return int_eq((add(a[0], b[0]), add(a[1], b[1])), res)


def _g_neg(args: tuple[Vec, ...], res: Vec) -> Eq:
    (a,) = args
    return int_eq((a[1], a[0]), res)


ZERO_AS_DIAGONAL = VecSymbol("0", 0, _g_zero)
ADD_COMPONENTWISE = VecSymbol("+", 2, _g_add)
NEG_AS_SWAP = VecSymbol("neg", 1, _g_neg)


# ---------------------------------------------------------------------------
# The proof engine: one cancellation recipe
# ---------------------------------------------------------------------------
# `by_combination` with every coefficient `None`: sum the oriented hypotheses,
# AC-shuffle with the addition kit, cancel the common suffix.

_KIT = add_kit()


def _cancel(goal: Eq, hyps: tuple[Hypothesis, ...]) -> Pf:
    return by_combination(goal, hyps, _KIT)


def _assume(eq: Eq) -> Hypothesis:
    return eq, Assume(eq), None


def _flip(eq: Eq) -> Hypothesis:
    return Eq(eq.rhs, eq.lhs), Sym(Assume(eq)), None


# ---------------------------------------------------------------------------
# Payments: the equivalence laws
# ---------------------------------------------------------------------------

_a, _b, _c = vec("x!", 2), vec("y!", 2), vec("z!", 2)


def _pay_refl() -> Pf:
    return Refl(add(_a[0], _a[1]))


def _pay_sym() -> Pf:
    hyp = int_eq(_a, _b)
    return ImpIntro(hyp, Sym(Assume(hyp)))


def _pay_trans() -> Pf:
    h1, h2 = int_eq(_a, _b), int_eq(_b, _c)
    core = _cancel(int_eq(_a, _c), (_assume(h1), _assume(h2)))
    return ImpIntro(h1, ImpIntro(h2, core))


# ---------------------------------------------------------------------------
# Payments: totality and respect
# ---------------------------------------------------------------------------


def _pay_totality(symbol: VecSymbol, image: tuple[Term, Term]) -> Pf:
    """Every totality witness is the image tuple itself, where the graph
    collapses to a reflexive equation."""
    args = symbol._args(2)
    claim = symbol.graph(args, vec("c!", 2))
    outer: Formula = exists("c!.1", "", exists("c!.2", "", claim))
    inner = exists("c!.2", "", symbol.graph(args, (image[0], vec("c!", 2)[1])))
    ground = symbol.graph(args, image)
    assert type(ground) is Eq and ground.lhs == ground.rhs
    return ExistsIntro(outer, image[0], ExistsIntro(inner, image[1], Refl(ground.lhs)))


def _pay_respect(symbol: VecSymbol, orient) -> Pf:
    """The respect chain, discharged in obligation order: one ~ per argument
    slot, then the two graph hypotheses, cancellation at the core."""
    args, primed = symbol._args(2), symbol._primed(2)
    c, d = vec("c!", 2), vec("d!", 2)
    eps_hyps = tuple(int_eq(old, new) for old, new in zip(args, primed, strict=True))
    g_c = symbol.graph(args, c)
    g_d = symbol.graph(primed, d)
    assert type(g_c) is Eq and type(g_d) is Eq
    core = _cancel(int_eq(c, d), orient(eps_hyps, g_c, g_d))
    out = ImpIntro(g_c, ImpIntro(g_d, core))
    for hyp in reversed(eps_hyps):
        out = ImpIntro(hyp, out)
    return out


def _orient_zero(eps_hyps, g_c: Eq, g_d: Eq):
    return (_assume(g_c), _flip(g_d))


def _orient_add(eps_hyps, g_c: Eq, g_d: Eq):
    return (_flip(g_c), _assume(g_d), _assume(eps_hyps[0]), _assume(eps_hyps[1]))


def _orient_neg(eps_hyps, g_c: Eq, g_d: Eq):
    return (_flip(eps_hyps[0]), _flip(g_c), _assume(g_d))


# ---------------------------------------------------------------------------
# Payments: the translated axioms
# ---------------------------------------------------------------------------
# Each translated axiom is a block of hoist guards around one equivalence
# atom; the payment mirrors the translator's wrapping exactly and pays the
# core by cancellation. The guard formulas are spelled with the same graph
# builders the translator uses, at the translator's own marker names.

_x, _y, _z = vec("x", 2), vec("y", 2), vec("z", 2)
_u, _u0, _u1, _u2 = vec("u!", 2), vec("u!0", 2), vec("u!1", 2), vec("u!2", 2)


def _pay_axiom(guards: tuple[tuple[str, Formula], ...], core: Pf) -> Pf:
    out = core
    for marker, guard in reversed(guards):
        out = ImpIntro(guard, out)
        for i in reversed(range(2)):
            out = ForallIntro(f"{marker}.{i + 1}", "", out)
    return out


def _pay_add_zero() -> Pf:
    """x + 0 = x: the diagonal guard makes the padding cancel."""
    g0 = _g_zero((), _u)
    ga = _g_add((_x, _u), _u0)
    assert type(ga) is Eq
    core = _cancel(int_eq(_u0, _x), (_flip(ga), _assume(g0)))
    return _pay_axiom((("u!", g0), ("u!0", ga)), core)


def _pay_add_comm() -> Pf:
    """x + y = y + x: componentwise sums of the same components."""
    g_r = _g_add((_y, _x), _u)
    g_l = _g_add((_x, _y), _u0)
    assert type(g_r) is Eq and type(g_l) is Eq
    core = _cancel(int_eq(_u0, _u), (_flip(g_l), _assume(g_r)))
    return _pay_axiom((("u!", g_r), ("u!0", g_l)), core)


def _pay_add_assoc() -> Pf:
    """(x + y) + z = x + (y + z): four hoists, one cancellation."""
    g1 = _g_add((_y, _z), _u)
    g2 = _g_add((_x, _u), _u0)
    g3 = _g_add((_x, _y), _u1)
    g4 = _g_add((_u1, _z), _u2)
    for g in (g1, g2, g3, g4):
        assert type(g) is Eq
    core = _cancel(
        int_eq(_u2, _u0),
        (_assume(g1), _assume(g2), _flip(g3), _flip(g4)),
    )
    return _pay_axiom((("u!", g1), ("u!0", g2), ("u!1", g3), ("u!2", g4)), core)


def _pay_add_neg() -> Pf:
    """x + (-x) = 0 -- the axiom the naturals refuse, paid as a theorem."""
    g0 = _g_zero((), _u)
    gn = _g_neg((_x,), _u0)
    ga = _g_add((_x, _u0), _u1)
    assert type(g0) is Eq and type(gn) is Eq and type(ga) is Eq
    core = _cancel(int_eq(_u1, _u), (_flip(ga), _flip(gn), _flip(g0)))
    return _pay_axiom((("u!", g0), ("u!0", gn), ("u!1", ga)), core)


# ---------------------------------------------------------------------------
# The artifact
# ---------------------------------------------------------------------------


def integers_interpretation() -> QuotientInterpretation:
    """The abelian group of integers -> PRESBURGER, dimension 2, all paid."""
    x0, x1 = vec("x!0", 2), vec("x!1", 2)
    return QuotientInterpretation(
        name="integers-into-presburger-pairs",
        source=AB_GROUP,
        target=PRESBURGER,
        dim=2,
        equiv=int_eq,
        symbols=(ZERO_AS_DIAGONAL, ADD_COMPONENTWISE, NEG_AS_SWAP),
        payments=(
            ("equivalence:refl", _pay_refl()),
            ("equivalence:sym", _pay_sym()),
            ("equivalence:trans", _pay_trans()),
            ("totality:0", _pay_totality(ZERO_AS_DIAGONAL, (ZERO, ZERO))),
            ("respect:0", _pay_respect(ZERO_AS_DIAGONAL, _orient_zero)),
            (
                "totality:+",
                _pay_totality(ADD_COMPONENTWISE, (add(x0[0], x1[0]), add(x0[1], x1[1]))),
            ),
            ("respect:+", _pay_respect(ADD_COMPONENTWISE, _orient_add)),
            ("totality:neg", _pay_totality(NEG_AS_SWAP, (x0[1], x0[0]))),
            ("respect:neg", _pay_respect(NEG_AS_SWAP, _orient_neg)),
            (f"axiom:{ADD_ZERO!r}", _pay_add_zero()),
            (f"axiom:{ADD_COMM!r}", _pay_add_comm()),
            (f"axiom:{ADD_ASSOC!r}", _pay_add_assoc()),
            (f"axiom:{ADD_NEG!r}", _pay_add_neg()),
        ),
    )


if __name__ == "__main__":
    from .quotient import verify

    report = verify(integers_interpretation())
    print(
        f"{report.name}: bridge {report.bridge_size} nodes; "
        f"toll {report.total_toll}; open {report.open_labels()}"
    )


__all__ = [
    "ADD_COMPONENTWISE",
    "NEG_AS_SWAP",
    "ZERO_AS_DIAGONAL",
    "int_eq",
    "integers_interpretation",
]
