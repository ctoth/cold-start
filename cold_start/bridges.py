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
from .peano import PEANO
from .presburger import ADD_SUCC_F as P_ADD_SUCC
from .presburger import SUCC_INJ as P_SUCC_INJ
from .presburger import SUCC_NEQ_ZERO, ZERO, S, add, induction
from .proof import (
    MP,
    Assume,
    Axiom,
    Cong,
    ExistsElim,
    ExistsIntro,
    ForallIntro,
    ImpIntro,
    Inst,
    Pf,
    Refl,
    Sym,
    Trans,
)
from .prop import And, and_intro
from .robinson import ADD_ONE, ADD_SUCC, ONE, ROBINSON_PEANO, SUCC_INJ, SUCC_NEQ_ONE, bridge
from .robinson_proofs import (
    bridge_converse_positive,
    bridge_theorem,
    robinson_add_one,
    robinson_add_succ_positive,
)
from .syntax import Eq, Formula, Term, Var, exists
from .tactics import Rule, normalize_equality

_a, _b, _c, _d = Var("a"), Var("b"), Var("c"), Var("d")

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


# ---------------------------------------------------------------------------
# The second landing: the same bridge into PEANO, relativized to the positives
# ---------------------------------------------------------------------------
# The same 19-node translation can land at home instead -- but not on all of
# PEANO: unguarded A5' is FALSE at zero (see robinson_proofs), so the crossing
# is provably impassable without relativizing. On the domain δ(x) := ∃k x=S(k)
# every obligation is payable, and the toll is exactly last wave's theorems:
# the guarded recursion law pays the translated A5' obligation, and the
# converse -- bridge(a,b,S(c)) → a+b=S(c) -- pays uniqueness. A bridge with no
# open obligations: base-1 Presburger is interpreted in PEANO's positives.


def positive(t: Term) -> Formula:
    """δ(t): ∃k. t = S(k) -- membership in the positive domain. `t` must not
    contain a free `k`; every use here applies it to k-free terms."""
    return exists("k", "", Eq(t, S(Var("k"))))


def _succ_ne_one_positive() -> Pf:
    """δ(a) → ¬(S(a) = 1). The guard earns its keep: at a = 0 the conclusion
    is false, so no unguarded proof exists. Under a = S(k), injectivity turns
    S(a) = S(0) into S(k) = 0, which the successor axiom refutes."""
    k = Var("k")
    a_pos = Eq(_a, S(k))
    inj = Inst(Inst(Axiom(P_SUCC_INJ), "x", _a), "y", ZERO)  # S(a)=S(0) -> a=0
    a_zero = MP(inj, Assume(Eq(S(_a), ONE)))
    sk_zero = Trans(Sym(Assume(a_pos)), a_zero)  # S(k) = 0
    contra = MP(Inst(Axiom(SUCC_NEQ_ZERO), "x", k), sk_zero)
    not_one = ImpIntro(Eq(S(_a), ONE), contra)
    return ImpIntro(positive(_a), ExistsElim("k", Assume(positive(_a)), not_one))


def _rewrite_by(eq: Eq) -> Rule:
    """Rewrite by an assumed ground equation, left to right."""
    return Rule(eq, Assume(eq), frozenset())


def _add_succ_positive_relativized() -> Pf:
    """δ(a) → δ(b) → ∀c (δ(c) → bridge(a,b,c) → bridge(a, S b, S c)).

    The translated recursion axiom. Under c = S(k) the hypothesis transports to
    bridge(a,b,S(k)); the guarded A5' theorem steps it; transporting back along
    S(k) = c lands bridge(a, S b, S c). The δ(a)/δ(b) guards are not needed by
    the mathematics -- only δ(c) bites -- so they wrap vacuously."""
    k = Var("k")
    c_pos = Eq(_c, S(k))
    hyp = bridge(_a, _b, _c)
    at_sk = normalize_equality(hyp, Assume(hyp), (_rewrite_by(c_pos),))
    stepped = MP(Inst(robinson_add_succ_positive(), "c", k), at_sk)
    back = Rule(Eq(S(k), _c), Sym(Assume(c_pos)), frozenset())
    at_c = normalize_equality(bridge(_a, S(_b), S(S(k))), stepped, (back,))
    body = ImpIntro(positive(_c), ExistsElim("k", Assume(positive(_c)), ImpIntro(hyp, at_c)))
    for_all = ForallIntro("c", "", body)
    return ImpIntro(positive(_a), ImpIntro(positive(_b), for_all))


def _bridge_total_positive() -> Pf:
    """δ(x!0) → δ(x!1) → ∃c (δ(c) ∧ bridge(x!0, x!1, c)).

    Existence with the witness where it always was: a + b. The bridge theorem
    supplies the graph half; positivity of the sum follows from δ(b) alone
    (b = S(j) makes a + b = S(a + j)), and δ(a) wraps vacuously."""
    j = Var("j")
    b_pos = Eq(_b, S(j))
    ab = add(_a, _b)
    sum_succ = Trans(
        Cong("+", (Refl(_a), Assume(b_pos))),  # a+b = a+S(j)
        Inst(Inst(Axiom(P_ADD_SUCC), "x", _a), "y", j),  # a+S(j) = S(a+j)
    )
    ab_pos = ExistsIntro(positive(ab), add(_a, j), sum_succ)
    packed = and_intro(positive(ab), bridge(_a, _b, ab), ab_pos, bridge_theorem())
    claim = exists("c!", "", And(positive(Var("c!")), bridge(_a, _b, Var("c!"))))
    intro = ExistsIntro(claim, ab, packed)
    guarded = ImpIntro(
        positive(_a), ImpIntro(positive(_b), ExistsElim("j", Assume(positive(_b)), intro))
    )
    return Inst(Inst(guarded, "a", Var("x!0")), "b", Var("x!1"))


def _bridge_unique_positive() -> Pf:
    """δ(x!0) → δ(x!1) → δ(c!) → δ(d!) → bridge → bridge → c! = d!.

    Uniqueness, paid by last wave's converse: each positive result S(k) forces
    a + b = S(k), so two results both equal the sum. This is where the previous
    campaign's theorem becomes this campaign's toll payment."""
    k, j = Var("k"), Var("j")
    c_pos, d_pos = Eq(_c, S(k)), Eq(_d, S(j))
    h1, h2 = bridge(_a, _b, _c), bridge(_a, _b, _d)
    h1_at = normalize_equality(h1, Assume(h1), (_rewrite_by(c_pos),))
    sum_k = MP(Inst(bridge_converse_positive(), "c", k), h1_at)  # a+b = S(k)
    c_val = Trans(Assume(c_pos), Sym(sum_k))  # c = a+b
    h2_at = normalize_equality(h2, Assume(h2), (_rewrite_by(d_pos),))
    sum_j = MP(Inst(bridge_converse_positive(), "c", j), h2_at)
    d_val = Trans(Assume(d_pos), Sym(sum_j))  # d = a+b
    core = ImpIntro(h1, ImpIntro(h2, Trans(c_val, Sym(d_val))))
    elim = ExistsElim("k", Assume(positive(_c)), ExistsElim("j", Assume(positive(_d)), core))
    guarded = elim
    for g in (positive(_d), positive(_c), positive(_b), positive(_a)):
        guarded = ImpIntro(g, guarded)
    out = guarded
    for var, target in (("a", "x!0"), ("b", "x!1"), ("c", "c!"), ("d", "d!")):
        out = Inst(out, var, Var(target))
    return out


def robinson_into_peano() -> Interpretation:
    """Base-1 Presburger -> PEANO relativized to the positives: the same
    19-node bridge, every obligation paid. Uniqueness and the recursion axiom
    are settled by the Robinson-converse campaign's theorems; totality by the
    bridge theorem; the domain debts by one witness each."""
    x0 = Var("x!0")
    succ_inj_pay = ImpIntro(
        positive(_a),
        ImpIntro(positive(_b), Inst(Inst(Axiom(P_SUCC_INJ), "x", _a), "y", _b)),
    )
    add_one_pay = ImpIntro(positive(_a), robinson_add_one())
    closure_s = ImpIntro(positive(x0), ExistsIntro(positive(S(x0)), x0, Refl(S(x0))))
    one_pos = ExistsIntro(positive(ONE), ZERO, Refl(ONE))
    nonempty = ExistsIntro(exists("x!", "", positive(Var("x!"))), ONE, one_pos)
    return Interpretation(
        name="robinson-1949-s2-into-peano-positives",
        source=PRESBURGER_ONE,
        target=PEANO,
        symbols=(PLUS,),
        domain=positive,
        retained_funs=(("S", 1),),
        retained_consts=(ONE,),
        payments=(
            (f"axiom:{SUCC_NEQ_ONE!r}", _succ_ne_one_positive()),
            (f"axiom:{SUCC_INJ!r}", succ_inj_pay),
            (f"axiom:{ADD_ONE_F!r}", add_one_pay),
            (f"axiom:{ADD_SUCC_F!r}", _add_succ_positive_relativized()),
            ("totality:+", _bridge_total_positive()),
            ("uniqueness:+", _bridge_unique_positive()),
            ("domain:nonempty", nonempty),
            ("closure:S", closure_s),
            (f"closure:{ONE!r}", one_pos),
        ),
    )


if __name__ == "__main__":
    from .checker import check
    from .interp import verify

    print("bridge_total:", check(bridge_total(), ROBINSON_PEANO))
    for build in (robinson_interpretation, robinson_into_peano):
        report = verify(build())
        print(
            f"{report.name}: bridge {report.bridge_size} nodes; "
            f"toll {report.total_toll}; open {report.open_labels()}"
        )
