"""Rigidity of the positive integers: every successor-preserving self-map is the identity.

This is the first genuine *induction* proof in `ROBINSON_PEANO` -- Robinson's
(1, S, ·) theory, whose induction base is **1**, not 0.

We extend that theory with one fresh unary function symbol `f` and two axioms,

    f(1)   = 1                                                (F_ONE)
    f(S x) = S(f x)                                           (F_SUCC)

and derive, by the checker's first-class `Induct` rule,

    |- f(x) = x                                               (RIGIDITY)

with `x` implicitly universally quantified, as everything else in this repo is.

## Why this statement

F_ONE and F_SUCC are exactly the **successor half** of a *brachymorphism* in the
sense of Wehrung, "Is addition definable from multiplication and successor?"
(arXiv:2405.08364, Forum Mathematicum). A brachymorphism between unital rings is
a map with `f(1+x) = 1+f(x)` and `f(xy) = f(x)f(y)`; Wehrung's central open
question is whether every brachymorphism is additive. Over the positive
integers, the first law alone already pins `f` down completely -- that is the
theorem below, and it is the degenerate base case of the addability question:
`N` is addable for the boring reason that it has no room to move.

That rigidity is also what makes Robinson's programme work at all. Multiplication
alone is *not* rigid -- permuting the primes is an automorphism of `(N, ·)`, and
those automorphisms are precisely what hide addition. Adjoining `S` kills them
(this module is that fact, checked), which is why `+` becomes definable from
`(1, S, ·)` in `cold_start.robinson`.

## The bonus theorem

Given RIGIDITY, the *other* brachymorphism law is no longer an assumption:

    |- f(x·y) = f(x)·f(y)                                     (MULTIPLICATIVE)

is derived by plain equational rewriting with rigidity as the only rule. Over
the positive integers, preserving successor forces multiplicativity for free.

See papers/Wehrung_2024_AdditionDefinableMultiplicationSuccessor/notes.md and
papers/Robinson_1949_DefinabilityArithmetic/notes.md.
"""

from __future__ import annotations

from dataclasses import replace

from .presburger import induction
from .proof import Assume, Axiom, Cong, ImpIntro, Pf, Trans
from .robinson import ONE, ROBINSON_PEANO
from .syntax import Eq, Formula, Fun, Term, Var
from .tactics import lemma_rule, prove_eq
from .theory import Signature
from .vocabulary import S, mul

# --- the extra symbol: a self-map of the positive integers -----------------


def f(t: Term) -> Term:
    return Fun("f", (t,))


_x, _y = Var("x"), Var("y")

# --- the two new axioms ----------------------------------------------------

F_ONE: Formula = Eq(f(ONE), ONE)  # f(1) = 1
F_SUCC: Formula = Eq(f(S(_x)), S(f(_x)))  # f(S x) = S(f x)

# A `Theory` is data, so "ROBINSON_PEANO plus f" is a value built with
# `dataclasses.replace` -- never a subclass. Zero (= 1), successor, and the
# induction rule are inherited unchanged; the only change is two more axioms and
# the `f` symbol they use. Compare `cold_start.peano` extending PRESBURGER.
if ROBINSON_PEANO.signature is None:
    raise TypeError("ROBINSON_PEANO must have a closed signature")
ROBINSON_PEANO_F = replace(
    ROBINSON_PEANO,
    axioms=ROBINSON_PEANO.axioms | {F_ONE, F_SUCC},
    signature=Signature(
        sorts=ROBINSON_PEANO.signature.sorts,
        ranks=ROBINSON_PEANO.signature.ranks + (("f", ("",), ""),),
        relations=ROBINSON_PEANO.signature.relations,
    ),
)

# --- the theorems ----------------------------------------------------------

RIGIDITY: Formula = Eq(f(_x), _x)  # f(x) = x
MULTIPLICATIVE: Formula = Eq(f(mul(_x, _y)), mul(f(_x), f(_y)))  # f(x·y) = f(x)·f(y)


def rigidity() -> Pf:
    """Proof term for  f(x) = x  by induction on x, **based at 1**.

    Built by hand, node by node -- the readable spelling of what the derivation
    actually is, and short enough that no tactic is warranted:

        base:  f(1) = 1                       -- F_ONE, verbatim; the checker
                                                 asks for `pred[x := theory.zero]`
                                                 and `theory.zero` is `1`.
        step:  (f(x) = x)  ->  (f(S x) = S x)
                 f(S x) = S(f x)              -- F_SUCC
                 S(f x) = S(x)                -- Cong on the hypothesis
                 f(S x) = S x                 -- Trans

    `ImpIntro` discharges the hypothesis, so `Induct`'s side condition (the
    induction variable free in no surviving hypothesis) holds vacuously and the
    sequent comes back with an empty context.
    """
    base = Axiom(F_ONE)
    unfold = Axiom(F_SUCC)  # f(S x) = S(f x), already at the eigenvariable x
    cong_ih = Cong("S", (Assume(RIGIDITY),))  # S(f x) = S(x)
    step = ImpIntro(RIGIDITY, Trans(unfold, cong_ih))
    return induction("x", RIGIDITY, base, step)


def multiplicative() -> Pf:
    """Proof term for  f(x·y) = f(x)·f(y)  -- Wehrung's second brachymorphism law,
    obtained as a THEOREM from rigidity rather than assumed.

    No induction: rigidity is used as a single rewrite rule (`f(t) -> t`, with
    `t` a hole), and both sides of the goal normalise to `x·y`. `lemma_rule`
    wraps rigidity's own hypothesis-free proof term, so this theorem also checks
    with an empty context.
    """
    return prove_eq(MULTIPLICATIVE, (lemma_rule(RIGIDITY, rigidity()),))


if __name__ == "__main__":
    from .checker import check

    print("rigidity:      ", check(rigidity(), ROBINSON_PEANO_F))
    print("multiplicative:", check(multiplicative(), ROBINSON_PEANO_F))
