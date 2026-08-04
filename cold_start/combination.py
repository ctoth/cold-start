"""Linear combinations of equations, with term coefficients.

The Grothendieck bridge's whole proof engine was one cancellation recipe:
`Cong`-sum the oriented hypotheses, AC-shuffle, cancel the common suffix.
The ring of integers needs one strictly stronger move -- a hypothesis may be
MULTIPLIED THROUGH by a term before it joins the sum, because equal
differences only stay equal under `*` after each is scaled by the factors of
the other. `by_combination` is that move: a linear combination of equational
hypotheses with term coefficients, closed by the same cancellation.

The old recipe is the special case where every coefficient is `None`, so this
module replaces `integers.by_cancellation` outright.

Untrusted, like every prover module: `check` remains the only judge.
"""

from __future__ import annotations

from .peano import mul
from .presburger import add
from .presburger_proofs import add_cancel_right
from .proof import MP, Cong, Inst, Pf, Refl, Trans
from .syntax import Eq, Term, Var
from .tactics import prove_eq

Hypothesis = tuple[Eq, Pf, Term | None]
"""An oriented equation, its proof, and an optional coefficient to scale by."""


def _cancel(lhs: Term, rhs: Term, suffix: Term) -> Pf:
    """`add_cancel_right` at x := lhs, y := rhs, z := suffix.

    `Inst` substitutes sequentially, so instantiating "x" and then "y" would
    rewrite any `y` the first value contained (the ordering hazard the
    divisibility work documented). Renaming every hole to a fresh name first
    and only then substituting the values makes the substitution simultaneous.
    """
    avoid = set()
    for t in (lhs, rhs, suffix):
        avoid |= set(t.free_vars())
    fresh = {}
    for name in ("x", "y", "z"):
        candidate = f"{name}!"
        k = 0
        while candidate in avoid:
            k += 1
            candidate = f"{name}!{k}"
        fresh[name] = candidate
        avoid.add(candidate)
    pf: Pf = add_cancel_right()
    for name in ("x", "y", "z"):
        pf = Inst(pf, name, Var(fresh[name]))
    for name, value in (("x", lhs), ("y", rhs), ("z", suffix)):
        pf = Inst(pf, fresh[name], value)
    return pf


def by_combination(goal: Eq, hyps: tuple[Hypothesis, ...], kit) -> Pf:
    """Prove `goal` from equational hypotheses by a scaled sum and one
    cancellation.

    Each hypothesis arrives as (its equation, its proof, its coefficient),
    already oriented by the caller; a coefficient `c` turns `L = R` into
    `L*c = R*c` by congruence before it joins the sum. Summing everything
    with `Cong` gives one equation H_L = H_R; then

        G_L + H_L  =  G_L + H_R      (congruence on the sum)
                   =  G_R + H_L      (the kit's normal forms, `prove_eq`)

    and cancelling the suffix H_L lands the goal. The middle step is exactly
    the polynomial identity G_L + H_R == G_R + H_L, so a wrong orientation or
    a wrong coefficient fails loudly inside `prove_eq`, never silently. With
    no hypotheses at all, the goal must be a kit identity outright."""
    kit = tuple(kit)
    if not hyps:
        return prove_eq(goal, kit)
    scaled: list[tuple[Eq, Pf]] = []
    for eq, pf, coeff in hyps:
        if coeff is not None:
            eq = Eq(mul(eq.lhs, coeff), mul(eq.rhs, coeff))
            pf = Cong("*", (pf, Refl(coeff)))
        scaled.append((eq, pf))
    (first_eq, combined), rest = scaled[0], scaled[1:]
    h_l: Term = first_eq.lhs
    h_r: Term = first_eq.rhs
    for eq, pf in rest:
        combined = Cong("+", (combined, pf))
        h_l, h_r = add(h_l, eq.lhs), add(h_r, eq.rhs)
    on_sum = Cong("+", (Refl(goal.lhs), combined))  # G_L + H_L = G_L + H_R
    shuffle = prove_eq(Eq(add(goal.lhs, h_r), add(goal.rhs, h_l)), kit)
    return MP(_cancel(goal.lhs, goal.rhs, h_l), Trans(on_sum, shuffle))


__all__ = ["Hypothesis", "by_combination"]
