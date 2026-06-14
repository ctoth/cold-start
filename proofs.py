"""Worked proofs. Each function returns a kernel.Theorem -- if it returns at
all, the theorem is genuinely derived.
"""

from __future__ import annotations

import kernel as k
from kernel import Eq, Var
from peano import ADD_ZERO, ADD_SUCC, add, induction, ZERO


def left_identity_of_addition() -> k.Theorem:
    """Prove  0 + n = n  by induction on n.

    The annoying one: `0 + n` does not reduce by the recursion axioms (those
    recurse on the *second* argument), so the only way through is induction.
    """
    n = Var("n")
    pred = Eq(add(ZERO, n), n)  # P(n) :=  0 + n = n

    # Base case:  0 + 0 = 0    -- instantiate (x + 0 = x) at x := 0
    base = k.instantiate(ADD_ZERO, "x", ZERO)

    # Step case:  (0 + n = n) -> (0 + S(n) = S(n))
    ih = k.assume(pred)  # {0+n=n} |- 0 + n = n

    #   0 + S(n) = S(0 + n)   -- instantiate (x + S(y) = S(x+y)) at x:=0, y:=n
    unfold = k.instantiate(k.instantiate(ADD_SUCC, "x", ZERO), "y", n)
    #   S(0 + n) = S(n)       -- congruence of S applied to the hypothesis
    cong_ih = k.cong("S", [ih])
    #   0 + S(n) = S(n)       -- chain them
    step_concl = k.trans(unfold, cong_ih)
    #   discharge the hypothesis to get the implication
    step = k.implies_intro(pred, step_concl)

    return induction("n", pred, base, step)


if __name__ == "__main__":
    print("left identity:", left_identity_of_addition())
