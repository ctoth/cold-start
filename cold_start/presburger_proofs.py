"""Proof builders whose complete checking contract is Presburger arithmetic."""

from __future__ import annotations

from .presburger import (
    ADD_SUCC_F,
    ADD_ZERO_F,
    SUCC_INJ,
    SUCC_NEQ_ZERO,
    induction,
)
from .proof import (
    MP,
    Assume,
    Axiom,
    Cong,
    ExFalso,
    ExistsElim,
    ExistsIntro,
    ImpIntro,
    Inst,
    Pf,
    Refl,
    Sym,
    Trans,
)
from .prop import And, Or, and_intro, or_elim, or_left, or_right
from .syntax import Eq, Formula, Implies, Var, exists
from .tactics import Rule, axiom_rule, by_induction, lemma_rule, normalize_equality
from .vocabulary import ZERO, S, add, numeral


def left_identity_proof() -> Pf:
    """Proof term for  0 + n = n  by induction on n.

    The annoying one: `0 + n` does not reduce by the recursion axioms (they
    recurse on the second argument), so induction is the only way through.
    """
    n = Var("n")
    pred = Eq(add(ZERO, n), n)  # P(n) :=  0 + n = n

    # base:  0 + 0 = 0          -- (x + 0 = x) at x := 0
    base = Inst(Axiom(ADD_ZERO_F), "x", ZERO)

    # step:  (0 + n = n) -> (0 + S(n) = S(n))
    ih = Assume(pred)
    #   0 + S(n) = S(0 + n)     -- (x + S y = S(x+y)) at x:=0, y:=n
    unfold = Inst(Inst(Axiom(ADD_SUCC_F), "x", ZERO), "y", n)
    #   S(0 + n) = S(n)         -- congruence of S on the hypothesis
    cong_ih = Cong("S", (ih,))
    #   0 + S(n) = S(n)
    step_eq = Trans(unfold, cong_ih)
    step = ImpIntro(pred, step_eq)

    return induction("n", pred, base, step)


def add_proof(a: int, b: int) -> Pf:
    """Proof term for  numeral(a) + numeral(b) = numeral(a+b).

    Built by unfolding the ADD_SUCC axiom on the concrete second argument -- no
    induction needed, since `b` is a fixed numeral. Useful as a sound generator
    for tests: the checker must agree with it for every a, b.

    Built bottom-up from `a + 0 = a`, one loop iteration per unit of `b`. The
    recursive spelling of this same term was the more obvious one, but it spent
    a Python frame per unit and so could not build past b ~ 1000 -- a proof the
    iterative `check` would have been perfectly happy to verify.
    """
    big_a = numeral(a)
    pf: Pf = Inst(Axiom(ADD_ZERO_F), "x", big_a)  # a + 0 = a
    for k in range(1, b + 1):
        #  a + S(k-1) = S(a + (k-1)),  then fold the sum already proved
        succ_step = Inst(Inst(Axiom(ADD_SUCC_F), "x", big_a), "y", numeral(k - 1))
        pf = Trans(succ_step, Cong("S", (pf,)))
    return pf


# ---------------------------------------------------------------------------
# The same mathematics, built by tactics
# ---------------------------------------------------------------------------
# Below, nothing is spelled node by node: we state the theorem and let the
# untrusted rewriting engine in `tactics.py` emit the proof term. Each lemma is
# then handed to the next one as a rewrite rule -- a `lemma_rule` wraps the
# lemma's own (hypothesis-free) proof term, so instantiating it introduces no
# assumption and every theorem here still checks with an empty context.

_x, _y, _z, _n = Var("x"), Var("y"), Var("z"), Var("n")

LEFT_IDENTITY: Formula = Eq(add(ZERO, _n), _n)  # 0 + n = n
SUCC_ADD: Formula = Eq(add(S(_x), _y), S(add(_x, _y)))  # S(x) + y = S(x + y)
ADD_COMM: Formula = Eq(add(_x, _y), add(_y, _x))  # x + y = y + x
ADD_ASSOC: Formula = Eq(add(add(_x, _y), _z), add(_x, add(_y, _z)))  # (x+y)+z = x+(y+z)
ADD_LEFT_COMM: Formula = Eq(  # x + (y + z) = y + (x + z)
    add(_x, add(_y, _z)),
    add(_y, add(_x, _z)),
)
ADD_CANCEL_RIGHT: Formula = Implies(  # x + z = y + z -> x = y
    Eq(add(_x, _z), add(_y, _z)),
    Eq(_x, _y),
)
ADD_CANCEL_LEFT: Formula = Implies(  # z + x = z + y -> x = y
    Eq(add(_z, _x), add(_z, _y)),
    Eq(_x, _y),
)

ADD_RULES = (axiom_rule(ADD_ZERO_F), axiom_rule(ADD_SUCC_F))
"""The two recursion axioms, read left to right: the whole starting kit."""


def left_identity() -> Pf:
    """0 + n = n, by induction on n -- the tactic-built twin of
    `left_identity_proof`. Both derive the very same sequent."""
    return by_induction("n", LEFT_IDENTITY, ADD_RULES)


def succ_add() -> Pf:
    """S(x) + y = S(x + y), by induction on y. The axioms recurse on the SECOND
    argument, so moving a successor out of the first one needs induction."""
    return by_induction("y", SUCC_ADD, ADD_RULES)


def add_comm() -> Pf:
    """x + y = y + x, by induction on y, over the axioms plus both lemmas: the
    base case is `x + 0 = 0 + x` (left identity) and the step turns `S(y) + x`
    into `S(y + x)` (succ-add)."""
    rules = (
        *ADD_RULES,
        lemma_rule(LEFT_IDENTITY, left_identity()),
        lemma_rule(SUCC_ADD, succ_add()),
    )
    return by_induction("y", ADD_COMM, rules)


def add_assoc() -> Pf:
    """(x + y) + z = x + (y + z), by induction on z -- the axioms alone suffice,
    since both sides recurse on the same trailing argument."""
    return by_induction("z", ADD_ASSOC, ADD_RULES)


def add_left_comm() -> Pf:
    """x + (y + z) = y + (x + z), the third leg of the AC kit, built by hand
    from associativity and commutativity:

        x + (y + z) = (x + y) + z = (y + x) + z = y + (x + z).

    Hand-built because the tactics cannot reach it: `prove_eq` would need
    commutativity as a rewrite rule, and this very lemma is what an *ordered*
    commutativity rule is missing -- ordered rewriting sorts the arguments of
    one `+`, and this is what lets a swap reach past the head of a nested sum.
    """
    assoc = lemma_rule(ADD_ASSOC, add_assoc())
    return Trans(
        Sym(add_assoc()),  # x + (y + z) = (x + y) + z
        Trans(
            Cong("+", (add_comm(), Refl(_z))),  # (x + y) + z = (y + x) + z
            assoc.instance({"x": _y, "y": _x, "z": _z}),  # (y + x) + z = y + (x + z)
        ),
    )


def add_cancel_right() -> Pf:
    """x + z = y + z -> x = y, by induction on the common suffix ``z``.

    The base simply unfolds both zero sums.  In the step both sums unfold to
    successors; successor injectivity peels those, and the induction hypothesis
    cancels the remaining common suffix.  Unlike the equational laws above,
    this proof needs implication introduction and modus ponens, so
    ``normalize_equality`` supplies the algebraic transport inside each case.
    """
    base_hyp = Eq(add(_x, ZERO), add(_y, ZERO))
    base = ImpIntro(
        base_hyp,
        normalize_equality(base_hyp, Assume(base_hyp), ADD_RULES),
    )

    step_hyp = Eq(add(_x, S(_z)), add(_y, S(_z)))
    unfolded = normalize_equality(step_hyp, Assume(step_hyp), ADD_RULES)
    injective = Inst(
        Inst(Axiom(SUCC_INJ), "x", add(_x, _z)),
        "y",
        add(_y, _z),
    )
    peeled = MP(injective, unfolded)
    step_result = MP(Assume(ADD_CANCEL_RIGHT), peeled)
    step = ImpIntro(ADD_CANCEL_RIGHT, ImpIntro(step_hyp, step_result))

    return induction("z", ADD_CANCEL_RIGHT, base, step)


def add_cancel_left() -> Pf:
    """z + x = z + y -> x = y, from commutativity and right cancellation."""
    hyp = Eq(add(_z, _x), add(_z, _y))
    comm = lemma_rule(ADD_COMM, add_comm())
    zx_to_xz = comm.instance({"x": _z, "y": _x})
    zy_to_yz = comm.instance({"x": _z, "y": _y})
    right_cancel_hyp = Trans(Sym(zx_to_xz), Trans(Assume(hyp), zy_to_yz))
    return ImpIntro(hyp, MP(add_cancel_right(), right_cancel_hyp))


def add_kit() -> tuple[Rule, ...]:
    """Everything proved about `+` so far, as one rewrite kit.

    The two recursion axioms and their two mirror images reduce a sum whose
    second OR first argument is a zero or a successor; associativity right-nests
    it; commutativity and left-commutativity, both `ordered`, sort the summands.
    The result is a canonical arrangement -- so `prove_eq` decides any goal whose
    sides differ only in how their additions are bracketed and ordered, which is
    what every rung of the multiplication ladder above needs.

    The zero laws have to travel WITH the sorting rules: the order puts `0`
    first, so `x*y + 0` sorts to `0 + x*y`, and only `0 + n = n` finishes it."""
    return (
        *ADD_RULES,
        lemma_rule(LEFT_IDENTITY, left_identity()),
        lemma_rule(SUCC_ADD, succ_add()),
        lemma_rule(ADD_ASSOC, add_assoc()),
        lemma_rule(ADD_COMM, add_comm(), ordered=True),
        lemma_rule(ADD_LEFT_COMM, add_left_comm(), ordered=True),
    )


ZERO_OR_SUCC: Formula = Or(  # n = 0  or  exists m, n = S(m)
    Eq(_n, ZERO),
    exists("m", "", Eq(_n, S(Var("m")))),
)


def zero_or_succ() -> Pf:
    """Every number is zero or a successor -- the case-split principle.

    Induction on ``n`` where neither case needs its hypothesis: at zero the
    left disjunct is reflexivity, and at ``S(n)`` the right disjunct holds
    with witness ``n``. A Presburger theorem; classical only through the
    disjunction encoding itself."""
    ex_zero = exists("m", "", Eq(ZERO, S(Var("m"))))
    base = or_left(Eq(ZERO, ZERO), ex_zero, Refl(ZERO))

    ex_succ = exists("m", "", Eq(S(_n), S(Var("m"))))
    witness = ExistsIntro(ex_succ, _n, Refl(S(_n)))
    step = ImpIntro(ZERO_OR_SUCC, or_right(Eq(S(_n), ZERO), ex_succ, witness))

    return induction("n", ZERO_OR_SUCC, base, step)


ADD_EQ_ZERO: Formula = Implies(  # x + y = 0  ->  x = 0 and y = 0
    Eq(add(_x, _y), ZERO),
    And(Eq(_x, ZERO), Eq(_y, ZERO)),
)


def add_eq_zero() -> Pf:
    """A zero sum has zero summands -- by cases on ``y`` via ``zero_or_succ``.

    When ``y = 0`` the hypothesis collapses to ``x = 0`` through the zero
    axiom; when ``y = S(m)`` the sum is a successor, and a successor is never
    zero. The corner every subtraction-free divisibility argument hits."""
    hyp = Eq(add(_x, _y), ZERO)
    goal = And(Eq(_x, ZERO), Eq(_y, ZERO))
    y_zero = Eq(_y, ZERO)
    ex_succ = exists("m", "", Eq(_y, S(Var("m"))))

    x_plus_zero = Inst(Axiom(ADD_ZERO_F), "x", _x)  # x + 0 = x
    shift = Cong("+", (Refl(_x), Assume(y_zero)))  # x + y = x + 0
    x_zero = Trans(Trans(Sym(x_plus_zero), Sym(shift)), Assume(hyp))  # x = 0
    zero_arm = ImpIntro(y_zero, and_intro(Eq(_x, ZERO), y_zero, x_zero, Assume(y_zero)))

    m = Var("m!")
    y_succ = Eq(_y, S(m))
    unfold = Inst(Inst(Axiom(ADD_SUCC_F), "x", _x), "y", m)  # x + S(m!) = S(x + m!)
    shift_succ = Cong("+", (Refl(_x), Assume(y_succ)))  # x + y = x + S(m!)
    succ_is_zero = Trans(Trans(Sym(unfold), Sym(shift_succ)), Assume(hyp))  # S(x+m!) = 0
    boom = MP(Inst(Axiom(SUCC_NEQ_ZERO), "x", add(_x, m)), succ_is_zero)
    succ_arm = ImpIntro(ex_succ, ExistsElim("m!", Assume(ex_succ), ExFalso(boom, goal)))

    cases = or_elim(y_zero, ex_succ, goal, Inst(zero_or_succ(), "n", _y), zero_arm, succ_arm)
    return ImpIntro(hyp, cases)
