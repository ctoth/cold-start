"""Worked proofs. Each function returns a proof term (proof.Pf), an inert
recipe. It asserts nothing until checker.check() re-derives its sequent.

Two styles live here. The first section builds proof terms *by hand*, node by
node -- that is the readable spelling of what a derivation actually is. The
second section builds them *by tactics* (`cold_start.tactics`), stating only the
theorem and letting an untrusted search emit the term. Both end up in front of
the same `check`, which is the point: the checker cannot tell, and does not care,
which one wrote the proof.
"""

from __future__ import annotations

from .peano import MUL_SUCC_F, MUL_ZERO_F
from .presburger import ADD_SUCC_F, ADD_ZERO_F, ZERO, S, add, induction, numeral
from .proof import MP, Assume, Axiom, Cong, ImpIntro, Inst, Pf, Refl, Trans
from .robinson import ADD_ONE, ADD_SUCC
from .syntax import Eq, Formula, Var
from .tactics import axiom_rule, by_induction, lemma_rule


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
    """
    big_a = numeral(a)
    if b == 0:
        return Inst(Axiom(ADD_ZERO_F), "x", big_a)  # a + 0 = a
    b_minus = numeral(b - 1)
    succ_step = Inst(Inst(Axiom(ADD_SUCC_F), "x", big_a), "y", b_minus)
    return Trans(succ_step, Cong("S", (add_proof(a, b - 1),)))


def mul_proof(a: int, b: int) -> Pf:
    """Proof term for  numeral(a) * numeral(b) = numeral(a*b).

    Recurses on the second argument via the multiplication axioms, reusing
    `add_proof` to collapse the trailing addition. A Peano theorem -- it cites
    the multiplication axioms, so it does not check under Presburger.
    """
    big_a = numeral(a)
    if b == 0:
        return Inst(Axiom(MUL_ZERO_F), "x", big_a)  # a * 0 = 0
    b_minus = numeral(b - 1)
    #  a * S(b-1) = (a * (b-1)) + a
    succ_step = Inst(Inst(Axiom(MUL_SUCC_F), "x", big_a), "y", b_minus)
    #  (a * (b-1)) + a = numeral(a*(b-1)) + a        -- by the inductive product
    fold_product = Cong("+", (mul_proof(a, b - 1), Refl(big_a)))
    #  numeral(a*(b-1)) + a = numeral(a*(b-1) + a) = numeral(a*b)
    collapse_sum = add_proof(a * (b - 1), a)
    return Trans(succ_step, Trans(fold_product, collapse_sum))


def robinson_add_proof(a: int, b: int) -> Pf:
    """Proof term for  bridge(numeral(a), numeral(b), numeral(a+b))  in the
    (1, S, ·) theory -- addition computed with no `+` symbol anywhere.

    Recurses on the second argument through Robinson's own §2 recursion laws:
    A4' (`a + 1 = S a`) is the base, and A5' (`a + b = c -> a + S b = S c`) is
    instantiated at the concrete numerals and discharged by modus ponens. Both
    arguments must be positive -- Robinson's domain is the positive integers,
    and the bridge is the graph of addition only for c > 0.
    """
    if a < 1 or b < 1:
        raise ValueError(f"Robinson's domain is the positive integers, got a={a}, b={b}")
    big_a = numeral(a)
    if b == 1:
        return Inst(Axiom(ADD_ONE), "a", big_a)  # a + 1 = S a
    #  a + (b-1) = a+b-1  ->  a + S(b-1) = S(a+b-1),  i.e.  a + b = a+b
    succ_step = Inst(
        Inst(Inst(Axiom(ADD_SUCC), "a", big_a), "b", numeral(b - 1)),
        "c",
        numeral(a + b - 1),
    )
    return MP(succ_step, robinson_add_proof(a, b - 1))


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


if __name__ == "__main__":
    from .checker import check
    from .presburger import PRESBURGER

    print("left identity:", check(left_identity_proof(), PRESBURGER))
    for name, build in (
        ("left identity (tactic)", left_identity),
        ("succ-add", succ_add),
        ("commutativity", add_comm),
        ("associativity", add_assoc),
    ):
        print(f"{name}:", check(build(), PRESBURGER))
