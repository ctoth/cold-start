"""Worked proofs. Each function returns a proof term (proof.Pf), an inert
recipe. It asserts nothing until checker.check() re-derives its sequent.
"""

from __future__ import annotations

from .peano import ADD_SUCC_F, ADD_ZERO_F, ZERO, add, induction, numeral
from .proof import Assume, Axiom, Cong, ImpIntro, Inst, Pf, Trans
from .syntax import Eq, Var


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


if __name__ == "__main__":
    from .checker import check
    from .peano import PEANO

    print("left identity:", check(left_identity_proof(), PEANO))
