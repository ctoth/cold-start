"""The concrete bridges: interpretation artifacts landed between this repo's
theories. First span: base-1 Presburger carried into Robinson's (1, S, ·).

Julia Robinson's 1949 §2 is, in modern terms, an interpretation: the whole of
addition crosses into the multiplication-only world over the single identity

    x + y = z   ↦   S(x·z) · S(y·z) = S((z·z) · S(x·y))

and this module packages that crossing as a checked `Interpretation` artifact.
The translator (cold_start.interp) lands the source's two addition axioms on
Robinson's own A4' and A5'; the successor axioms cross verbatim; totality --
`∃c bridge(a,b,c)`, addition is defined EVERYWHERE on the far shore -- is
`bridge_total` below, this repo's first existential theorem, proved inside
ROBINSON_PEANO by induction based at 1. Uniqueness is deliberately left as the
artifact's one OPEN obligation: deriving `bridge(a,b,c) → bridge(a,b,d) → c=d`
over (1, S, ·) needs the multiplication ladder rebuilt on the far shore, and
the report says so rather than hiding it. An interpretation with an open
obligation is a conjecture with a ledger, not a theorem.

Untrusted, like every prover module: `check` remains the only judge.
"""

from __future__ import annotations

from .checker import Theory
from .interp import GraphSymbol, Interpretation
from .presburger import S, add, induction
from .proof import (
    MP,
    Assume,
    Axiom,
    ExistsElim,
    ExistsIntro,
    ForallIntro,
    ImpIntro,
    Inst,
    Pf,
)
from .robinson import ADD_ONE, ADD_SUCC, ONE, ROBINSON_PEANO, SUCC_INJ, SUCC_NEQ_ONE, bridge
from .syntax import Eq, Formula, Term, Var, exists

_a, _b = Var("a"), Var("b")

# --- the source theory: base-1 Presburger ----------------------------------
# Addition over the positive integers, recursing from 1: the (1, S, +) twin of
# `cold_start.presburger`. Its successor axioms are literally Robinson's A1/A2,
# so they cross the bridge verbatim.

ADD_ONE_F: Formula = Eq(add(_a, ONE), S(_a))  # a + 1 = S a
ADD_SUCC_F: Formula = Eq(add(_a, S(_b)), S(add(_a, _b)))  # a + S b = S(a + b)

PRESBURGER_ONE = Theory(
    axioms=frozenset({SUCC_NEQ_ONE, SUCC_INJ, ADD_ONE_F, ADD_SUCC_F}),
    zero=ONE,
    succ="S",
)


# --- totality: the first existential theorem -------------------------------


def _exists_bridge(b: Term) -> Formula:
    """∃c bridge(a, b, c) -- the induction predicate, at a given second leg."""
    return exists("c", "", bridge(_a, b, Var("c")))


def bridge_total() -> Pf:
    """|- ∃c bridge(a, b, c), by induction on b **based at 1**, entirely inside
    ROBINSON_PEANO -- addition is total on the far shore, said without any `+`.

        base:  A4' is bridge(a, 1, S a) verbatim: S(a) is the witness.
        step:  assume ∃c bridge(a,b,c); take its witness w (ExistsElim);
               A5' at c := w steps it to bridge(a, S b, S w); S(w) is the
               witness for ∃c bridge(a, S b, c).

    The eigenvariable w escapes into neither the conclusion nor any remaining
    hypothesis, and ImpIntro discharges the induction hypothesis, so `Induct`'s
    side condition holds and the sequent comes back with an empty context."""
    pred = _exists_bridge(_b)

    base = ExistsIntro(_exists_bridge(ONE), S(_a), Axiom(ADD_ONE))

    w = Var("w")
    step_up = Inst(Axiom(ADD_SUCC), "c", w)  # bridge(a,b,w) -> bridge(a,Sb,Sw)
    stepped = MP(step_up, Assume(bridge(_a, _b, w)))
    packed = ExistsIntro(_exists_bridge(S(_b)), S(w), stepped)
    used = ExistsElim("w", Assume(pred), packed)
    step = ImpIntro(pred, used)

    return induction("b", pred, base, step)


# --- the artifact ----------------------------------------------------------

PLUS = GraphSymbol("+", 2, lambda args, res: bridge(args[0], args[1], res))


def robinson_interpretation() -> Interpretation:
    """Base-1 Presburger -> ROBINSON_PEANO over Robinson's bridge identity.

    Payments: the successor axioms and A4' cross as target axioms verbatim;
    the translated recursion axiom is A5' one ForallIntro up; totality is
    `bridge_total`. The totality obligation is stated at the artifact's
    canonical variables x!0, x!1, so the theorem (proved at a, b) is carried
    there by two hypothesis-free instantiations. Uniqueness is offered no
    payment -- the report ledgers it open."""
    totality = Inst(Inst(bridge_total(), "a", Var("x!0")), "b", Var("x!1"))
    return Interpretation(
        name="robinson-1949-s2",
        source=PRESBURGER_ONE,
        target=ROBINSON_PEANO,
        symbols=(PLUS,),
        payments=(
            (f"axiom:{SUCC_NEQ_ONE!r}", Axiom(SUCC_NEQ_ONE)),
            (f"axiom:{SUCC_INJ!r}", Axiom(SUCC_INJ)),
            (f"axiom:{ADD_ONE_F!r}", Axiom(ADD_ONE)),
            (f"axiom:{ADD_SUCC_F!r}", ForallIntro("c", "", Axiom(ADD_SUCC))),
            ("totality:+", totality),
        ),
    )


if __name__ == "__main__":
    from .checker import check
    from .interp import verify

    print("bridge_total:", check(bridge_total(), ROBINSON_PEANO))
    report = verify(robinson_interpretation())
    print(f"bridge size: {report.bridge_size} nodes; toll paid: {report.total_toll};")
    print(f"open: {report.open_labels()}")
