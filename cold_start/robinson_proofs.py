"""Robinson's bridge, proved -- not model-checked -- in PEANO.

`cold_start.robinson` exhibits the (1, S, ·) axiomatisation and `tests/` checks
it against the standard model. That leaves the interesting half unsaid: is
Robinson's definition of addition *correct*? Here it is, as a theorem.

    PEANO |- S(a·(a+b)) · S(b·(a+b)) = S(((a+b)·(a+b)) · S(a·b))

Read with `+` back in, that is `(1 + ac)(1 + bc) = 1 + c²(1 + ab)` at `c := a+b`,
and at that instance it is a pure semiring identity -- both sides multiply out to
`ab(a+b)² + (a+b)² + 1`. So it needs no positivity and no case split: it is true
of every natural number, 0 included.

The proof is the identity's own reason: `poly_kit()` normalises both sides to
one canonical polynomial. Distributivity expands the products, the recursion
laws float every successor to the outside, and the AC rules sort the sum of
monomials; then `prove_eq` joins the two sides at the shared normal form. Both
sides of the theorem above land on

    S(a·a + (a·b + (a·b + (b·b + (a·(a·(a·b)) + ...)))))

which is `1 + (a+b)² + ab(a+b)²` written in the canonical arrangement.

The converse is derived too, precisely on Robinson's positive domain.  A bridge
hypothesis normalizes to `(a+b)c=c²`; additive cancellation removes the common
polynomial part, and a nested-induction proof cancels a positive factor `S(c)`.
Thus `bridge(a,b,S(c)) -> a+b=S(c)`.  Robinson's A4' and A7' come out as direct
instances, while A5' comes out with exactly that positivity guard.  Its
unguarded Peano version remains false at `c=0`, as documented at the bottom.
"""

from __future__ import annotations

from .peano import MUL_SUCC_F, MUL_ZERO_F, mul
from .peano_proofs import (
    DISTRIB_LEFT,
    DISTRIB_RIGHT,
    MUL_ASSOC,
    MUL_COMM,
    MUL_LEFT_COMM,
    MUL_SUCC_LEFT,
    MUL_ZERO_LEFT,
    distrib_left,
    distrib_right,
    mul_assoc,
    mul_cancel_right_succ,
    mul_comm,
    mul_left_comm,
    mul_succ_left,
    mul_zero_left,
)
from .presburger import ADD_SUCC_F, SUCC_INJ, S, add, numeral
from .presburger_proofs import ADD_ASSOC, add_assoc, add_cancel_right, add_kit
from .proof import MP, Assume, Axiom, Cong, ImpIntro, Inst, Pf, Sym, Trans
from .robinson import ADD_ONE, ADD_SUCC, ONE, bridge
from .syntax import Eq, Formula, Implies, Var
from .tactics import (
    axiom_rule,
    hypothesis_rule,
    lemma_rule,
    normalize,
    normalize_equality,
    prove_eq,
)

_a, _b, _c = Var("a"), Var("b"), Var("c")


def robinson_add_proof(a: int, b: int) -> Pf:
    """Proof term for  bridge(numeral(a), numeral(b), numeral(a+b))  in the
    (1, S, ·) theory -- addition computed with no `+` symbol anywhere.

    Climbs the second argument through Robinson's own §2 recursion laws: A4'
    (`a + 1 = S a`) is the base, and A5' (`a + b = c -> a + S b = S c`) is
    instantiated at the concrete numerals and discharged by modus ponens, one
    rung per unit of `b`. Both arguments must be positive -- Robinson's domain
    is the positive integers, and the bridge is the graph of addition only for
    c > 0. Iterative, for the reason given on `add_proof`.
    """
    if a < 1 or b < 1:
        raise ValueError(f"Robinson's domain is the positive integers, got a={a}, b={b}")
    big_a = numeral(a)
    pf: Pf = Inst(Axiom(ADD_ONE), "a", big_a)  # a + 1 = S a
    for k in range(2, b + 1):
        #  a + (k-1) = a+k-1  ->  a + S(k-1) = S(a+k-1),  i.e.  a + k = a+k
        succ_step = Inst(
            Inst(Inst(Axiom(ADD_SUCC), "a", big_a), "b", numeral(k - 1)),
            "c",
            numeral(a + k - 1),
        )
        pf = MP(succ_step, pf)
    return pf


BRIDGE_SUM: Formula = bridge(_a, _b, add(_a, _b))
"""Robinson's bridge at `c := a + b` -- the claim that his definition of
addition is correct, stated in PEANO's own signature."""

BRIDGE_RESIDUAL: Formula = Implies(
    bridge(_a, _b, _c),
    Eq(mul(add(_a, _b), _c), mul(_c, _c)),
)
"""The exact algebraic content left by a bridge hypothesis after expansion."""

BRIDGE_FORWARD: Formula = Implies(
    Eq(add(_a, _b), _c),
    bridge(_a, _b, _c),
)
"""The forward graph direction, with the result named independently."""

BRIDGE_CONVERSE_POS: Formula = Implies(
    bridge(_a, _b, S(_c)),
    Eq(add(_a, _b), S(_c)),
)
"""The missing half of Robinson's theorem: her bridge defines addition when
the result is positive (represented as ``S(c)``)."""

ROBINSON_ADD_SUCC_POS: Formula = Implies(
    bridge(_a, _b, S(_c)),
    bridge(_a, S(_b), S(S(_c))),
)
"""Robinson's A5' recursion theorem with exactly its missing positivity guard."""

POLY_BUDGET = 400
"""Rewrite steps the bridge needs; the identity is degree four in two
variables, so its normal form is eight monomials wide."""


def poly_kit() -> tuple:
    """Every law of `+` and `·` proved in the theory-owned libraries, as one rewrite
    kit that normalises a term to a canonical polynomial.

    Three groups do three jobs. The recursion laws (both axioms and both of
    their mirror images) float every successor out to the front, so a term
    becomes `S^k` of a successor-free body. Distributivity, both ways, expands
    every product over a sum, so that body becomes a sum of monomials. The AC
    rules for `+` and for `·` -- associativity directed, commutativity and
    left-commutativity ordered -- right-nest and sort both the sum and each
    monomial. What is left is unique, so `prove_eq` over this kit decides any
    identity of the commutative semiring."""
    return (
        *add_kit(),
        axiom_rule(MUL_ZERO_F),
        axiom_rule(MUL_SUCC_F),
        lemma_rule(MUL_ZERO_LEFT, mul_zero_left()),
        lemma_rule(MUL_SUCC_LEFT, mul_succ_left()),
        lemma_rule(DISTRIB_LEFT, distrib_left()),
        lemma_rule(DISTRIB_RIGHT, distrib_right()),
        lemma_rule(MUL_ASSOC, mul_assoc()),
        lemma_rule(MUL_COMM, mul_comm(), ordered=True),
        lemma_rule(MUL_LEFT_COMM, mul_left_comm(), ordered=True),
    )


def bridge_theorem() -> Pf:
    """PEANO |- bridge(a, b, a + b): Robinson's definition of addition is
    correct. Both sides normalise to the same polynomial; nothing is assumed
    about `a` and `b`, so this is the theorem for every pair of naturals."""
    return prove_eq(BRIDGE_SUM, poly_kit(), POLY_BUDGET)


def bridge_residual() -> Pf:
    """PEANO |- bridge(a,b,c) -> (a+b)c = c^2.

    Polynomial normalization turns the assumed bridge into

        S(ac + (bc + abc^2)) = S(c^2 + abc^2).

    Successor injectivity removes the outer ``S``; associativity exposes the
    identical ``abc^2`` suffix, and the derived additive-cancellation theorem
    removes it.  Folding distributivity back up gives the displayed residual.
    This implication is valid even at ``c = 0``; only the next cancellation
    step needs positivity.
    """
    hyp = bridge(_a, _b, _c)
    rules = poly_kit()
    normalized = normalize_equality(hyp, Assume(hyp), rules, POLY_BUDGET)

    ac = mul(_a, _c)
    bc = mul(_b, _c)
    c_squared = mul(_c, _c)
    common = mul(_a, mul(_b, c_squared))
    left = add(ac, add(bc, common))
    right = add(c_squared, common)
    injective = Inst(Inst(Axiom(SUCC_INJ), "x", left), "y", right)
    peeled = MP(injective, normalized)

    reassociate = lemma_rule(ADD_ASSOC, add_assoc()).instance({"x": ac, "y": bc, "z": common})
    cancellable = Trans(reassociate, peeled)
    cancel = Inst(
        Inst(
            Inst(add_cancel_right(), "z", common),
            "x",
            add(ac, bc),
        ),
        "y",
        c_squared,
    )
    residual_normal = MP(cancel, cancellable)

    residual = Eq(mul(add(_a, _b), _c), c_squared)
    _, left_to_normal = normalize(residual.lhs, rules, POLY_BUDGET)
    _, right_to_normal = normalize(residual.rhs, rules, POLY_BUDGET)
    folded = Trans(left_to_normal, Trans(residual_normal, Sym(right_to_normal)))
    return ImpIntro(hyp, folded)


def bridge_forward() -> Pf:
    """PEANO |- a+b=c -> bridge(a,b,c), the graph's forward direction.

    The earlier ``bridge_theorem`` chooses ``c := a+b`` in its statement.  This
    implication names ``c`` independently: under the equality hypothesis,
    rewriting ``c`` back to ``a+b`` reduces the target to that same polynomial
    identity.  Discharging the equality makes the direction reusable by later
    proofs instead of relying on metalevel substitution.
    """
    hyp = Eq(add(_a, _b), _c)
    replace_c = hypothesis_rule(hyp).flipped
    body = prove_eq(bridge(_a, _b, _c), (*poly_kit(), replace_c), POLY_BUDGET)
    return ImpIntro(hyp, body)


def bridge_converse_positive() -> Pf:
    """PEANO |- bridge(a,b,S(c)) -> a+b=S(c), Robinson's positive converse.

    ``bridge_residual`` leaves ``(a+b)S(c) = S(c)^2``.  The factor ``S(c)`` is
    provably positive, so the separately derived multiplication-cancellation
    theorem removes it.  Together with ``bridge_theorem`` this proves that the
    bridge is exactly the graph of addition on Robinson's positive domain.
    """
    hyp = bridge(_a, _b, S(_c))
    product_eq = MP(Inst(bridge_residual(), "c", S(_c)), Assume(hyp))
    cancel = Inst(
        Inst(
            Inst(mul_cancel_right_succ(), "z", _c),
            "x",
            add(_a, _b),
        ),
        "y",
        S(_c),
    )
    return ImpIntro(hyp, MP(cancel, product_eq))


def robinson_add_succ_positive() -> Pf:
    """A5' with ``c`` positive, derived in PEANO instead of assumed.

    The positive converse reads a bridge hypothesis as ``a+b=S(c)``.  Peano's
    addition recursion turns that into ``a+S(b)=S(S(c))``; ``bridge_forward``
    then turns the equality back into Robinson's successor bridge.  The
    unguarded A5' remains correctly unprovable because its ``c=0`` instance is
    false.
    """
    hyp = bridge(_a, _b, S(_c))
    sum_eq_c = MP(bridge_converse_positive(), Assume(hyp))
    unfold = Inst(Inst(Axiom(ADD_SUCC_F), "x", _a), "y", _b)
    successor_eq = Cong("S", (sum_eq_c,))
    next_sum = Trans(unfold, successor_eq)

    forward = Inst(
        Inst(
            Inst(bridge_forward(), "c", S(S(_c))),
            "a",
            _a,
        ),
        "b",
        S(_b),
    )
    return ImpIntro(hyp, MP(forward, next_sum))


def _instance_at(sigma: dict, rewrite: tuple) -> Pf:
    """The bridge theorem at `sigma`, with `rewrite` applied to the sum that
    `c := a + b` leaves behind.

    Robinson states A4' and A7' with the sum already evaluated -- `a + 1` as
    `S(a)`, `a·b + a` as `a·S(b)` -- so an instance of the theorem is one
    congruence rewrite away from the axiom. `normalize` proves that rewrite on
    each side separately (`src = tgt`), and the two are pasted around the
    instance: from `L_src = R_src` and `L_src = L_tgt`, `R_src = R_tgt`, we get
    `L_tgt = R_tgt`, which is the axiom on the nose."""
    instance = lemma_rule(BRIDGE_SUM, bridge_theorem()).instance(sigma)
    source = bridge(sigma["a"], sigma["b"], add(sigma["a"], sigma["b"]))
    _, left = normalize(source.lhs, rewrite)
    _, right = normalize(source.rhs, rewrite)
    return Trans(Sym(left), Trans(instance, right))


def robinson_add_one() -> Pf:
    """A4' as a Peano theorem: PEANO |- bridge(a, 1, S(a)).

    The bridge theorem at `b := 1`, whose `a + 1` the two addition axioms turn
    into `S(a)` -- one unfold and one zero law, inside every position where the
    sum occurs."""
    return _instance_at({"a": _a, "b": ONE}, add_kit())


def robinson_mul_succ() -> Pf:
    """A7' as a Peano theorem: PEANO |- bridge(a·b, a, a·S(b)).

    The bridge theorem at `a := a·b, b := a` -- a SIMULTANEOUS substitution, so
    it goes through `Rule.instance` rather than a chain of `Inst`, which would
    substitute the second into what the first introduced. The sum it leaves,
    `a·b + a`, is folded back up by the multiplication axiom read right to
    left: exactly the step Robinson's A7' states."""
    return _instance_at({"a": mul(_a, _b), "b": _a}, (axiom_rule(MUL_SUCC_F).flipped,))


# --- why unguarded A5' is still impossible --------------------------------
# Robinson's A5' -- `bridge(a,b,c) -> bridge(a, S b, S c)`, the recursion law for
# addition -- has no unguarded proof here, and can have none. It is not that the tactics
# are too weak: the implication is FALSE in the standard model of PEANO, which by
# soundness settles it.
#
# The bridge says `(a + b)·c = c·c`, which pins `a + b = c` down only when `c` can
# be cancelled -- and 0 cannot. At `a = b = 1, c = 0` the hypothesis holds
# vacuously (`(1 + 0)·(1 + 0) = 1 = 1 + 0·(1 + 1)`) while the conclusion
# `bridge(1, 2, 1)` demands `2·3 = 1 + 1·3`, i.e. `6 = 4`. Robinson's §2 domain is
# the POSITIVE integers, where `c > 0` makes the cancellation available; PEANO's
# is the naturals, where it does not. That is precisely the work positivity does
# in her definition. A4' and A7' transfer without it; `robinson_add_succ_positive`
# proves A5' under `c = S(k)`, and `tests/test_robinson.py` pins the lone boundary
# obstruction at zero.
