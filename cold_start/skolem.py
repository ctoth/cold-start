"""The Skolem shore: Presburger arithmetic interpreted into multiplication.

Skolem arithmetic is the theory of the naturals with multiplication ONLY.
Mostowski's classical observation is that the additive world embeds into it:
on the powers of two, multiplication IS addition of exponents. This module
lands that crossing as a checked `Interpretation` artifact:

    0       becomes  1
    S(x)    becomes  x*2          (the doubling graph)
    x + y   becomes  x*y          (the multiplication graph)

relativized to the domain

    pow2(t) :=  forall d (d | t -> d != 1 -> 2 | d)

-- "every divisor except 1 is even", a definition of *power of two* spoken
entirely in divisibility, with no exponentiation anywhere. The target is
PEANO; `a | b` is the paid predicate `exists k, a*k = b`.

Every source axiom is paid, and so are both definedness obligations of the
doubling graph: closure of the powers of two under doubling is EXACTLY
Euclid's lemma at 2 (`cold_start.parity`), which also settles the translated
successor injectivity. The single open obligation is `totality:+` -- that a
product of powers of two is a power of two -- whose honest proof needs
descent on divisors (strong induction / an order kit) that the repository
does not yet own. An interpretation with an open obligation is a conjecture
with a ledger, not a theorem; the ledger says exactly this.

Untrusted, like every prover module: `check` remains the only judge.
"""

from __future__ import annotations

from .divisibility import divides_one, peano_divides
from .interp import GraphSymbol, Interpretation
from .parity import TWO, cancel_two, euclid_two
from .peano import PEANO, mul
from .peano_proofs import MUL_ASSOC, MUL_COMM, mul_assoc, mul_comm
from .peano_proofs import MUL_RULES as _MUL_RULES
from .presburger import (
    ADD_SUCC_F,
    ADD_ZERO_F,
    PRESBURGER,
    SUCC_INJ,
    SUCC_NEQ_ZERO,
    ZERO,
    S,
)
from .presburger_proofs import ADD_RULES, LEFT_IDENTITY, left_identity
from .proof import (
    MP,
    RAA,
    Assume,
    Axiom,
    Cong,
    ExFalso,
    ExistsIntro,
    ForallElim,
    ForallIntro,
    ImpIntro,
    Inst,
    Pf,
    Refl,
    Sym,
    Trans,
)
from .prop import And, and_intro
from .syntax import Eq, Formula, Implies, Not, Term, Var, exists, forall
from .tactics import lemma_rule, prove_eq

ONE = S(ZERO)
_x, _y = Var("x"), Var("y")


# ---------------------------------------------------------------------------
# The domain: powers of two, by divisibility alone
# ---------------------------------------------------------------------------


def pow2(t: Term) -> Formula:
    """``t`` is a power of two: every divisor other than 1 is even.

    Zero fails it (3 divides 0 and is odd), 1 passes vacuously, and any other
    number passes exactly when its divisor lattice is the 2-adic chain."""
    d = Var("d")
    return forall(
        "d",
        "",
        Implies(
            peano_divides(d, t),
            Implies(Not(Eq(d, ONE)), peano_divides(TWO, d)),
        ),
    )


def pow2_one() -> Pf:
    """PEANO proves ``pow2(1)``: a divisor of 1 IS 1, so the guard explodes."""
    d = Var("d")
    dvd, ne_one = peano_divides(d, ONE), Not(Eq(d, ONE))
    d_is_one = MP(Inst(divides_one(), "a", d), Assume(dvd))
    boom = MP(Assume(ne_one), d_is_one)
    body = ImpIntro(dvd, ImpIntro(ne_one, ExFalso(boom, peano_divides(TWO, d))))
    return ForallIntro("d", "", body)


POW2_DOUBLE: Formula = Implies(pow2(_x), pow2(mul(_x, TWO)))


def pow2_double() -> Pf:
    """PEANO proves the powers of two are closed under doubling.

    A divisor ``d != 1`` of ``x*2`` must be shown even. Reductio: were it odd,
    Euclid's lemma at 2 drops it to a divisor of ``x`` itself, where
    ``pow2(x)`` pronounces it even after all. The whole toll of this bridge
    is that one lemma."""
    hyp = pow2(_x)
    d = Var("d")
    dvd, ne_one = peano_divides(d, mul(_x, TWO)), Not(Eq(d, ONE))
    even = peano_divides(TWO, d)
    odd = Not(even)
    down = MP(MP(euclid_two(), Assume(odd)), Assume(dvd))  # d | x
    from_domain = MP(MP(ForallElim(Assume(hyp), d), down), Assume(ne_one))  # 2 | d
    body = RAA(even, MP(Assume(odd), from_domain))
    return ImpIntro(hyp, ForallIntro("d", "", ImpIntro(dvd, ImpIntro(ne_one, body))))


# ---------------------------------------------------------------------------
# The translation
# ---------------------------------------------------------------------------

ZERO_AS_ONE = GraphSymbol("0", 0, lambda args, result: Eq(result, ONE))
SUCC_AS_DOUBLE = GraphSymbol("S", 1, lambda args, result: Eq(mul(args[0], TWO), result))
ADD_AS_MUL = GraphSymbol("+", 2, lambda args, result: Eq(mul(args[0], args[1]), result))

_u0, _u1, _u2 = Var("u!"), Var("u!0"), Var("u!1")


def _mul_one(t: Term) -> Pf:
    return prove_eq(
        Eq(mul(t, ONE), t),
        (*ADD_RULES, *_MUL_RULES, lemma_rule(LEFT_IDENTITY, left_identity())),
    )


def _pay_add_zero() -> Pf:
    """delta(x) -> forall u! (delta(u!) -> u! = 1 -> x*u! = x)."""
    guard = Eq(_u0, ONE)
    core = Trans(Cong("*", (Refl(_x), Assume(guard))), _mul_one(_x))
    body = ImpIntro(pow2(_u0), ImpIntro(guard, core))
    return ImpIntro(pow2(_x), ForallIntro("u!", "", body))


def _pay_add_succ() -> Pf:
    """The translated recursion axiom: under the three hoisted graph guards
    ``x*y = u!``, ``u!*2 = u!0``, ``y*2 = u!1``, associativity carries
    ``x*u!1 = u!0``. Every domain guard wraps vacuously."""
    g_sum, g_up, g_arg = Eq(mul(_x, _y), _u0), Eq(mul(_u0, TWO), _u1), Eq(mul(_y, TWO), _u2)
    assoc = lemma_rule(MUL_ASSOC, mul_assoc())
    core = Trans(
        Cong("*", (Refl(_x), Sym(Assume(g_arg)))),  # x*u!1 = x*(y*2)
        Trans(
            Sym(assoc.instance({"x": _x, "y": _y, "z": TWO})),  # x*(y*2) = (x*y)*2
            Trans(Cong("*", (Assume(g_sum), Refl(TWO))), Assume(g_up)),  # = u!*2 = u!0
        ),
    )
    inner = ForallIntro("u!1", "", ImpIntro(pow2(_u2), ImpIntro(g_arg, core)))
    middle = ForallIntro("u!0", "", ImpIntro(pow2(_u1), ImpIntro(g_up, inner)))
    outer = ForallIntro("u!", "", ImpIntro(pow2(_u0), ImpIntro(g_sum, middle)))
    return ImpIntro(pow2(_x), ImpIntro(pow2(_y), outer))


def _pay_succ_neq_zero() -> Pf:
    """No doubling lands on 1: from the hoisted hypothesis at u! := 1,
    ``x*2 = 1`` makes 2 a unit, so 2 = 1, and injectivity marches that down
    to the successor axiom."""
    hyp = forall(
        "u!",
        "",
        Implies(pow2(_u0), Implies(Eq(_u0, ONE), Eq(mul(_x, TWO), _u0))),
    )
    at_one = ForallElim(Assume(hyp), ONE)
    x2_is_one = MP(MP(at_one, pow2_one()), Refl(ONE))  # x*2 = 1
    comm = lemma_rule(MUL_COMM, mul_comm())
    two_x = Trans(comm.instance({"x": TWO, "y": _x}), x2_is_one)  # 2*x = 1
    two_unit = ExistsIntro(peano_divides(TWO, ONE), _x, two_x)
    two_is_one = MP(Inst(divides_one(), "a", TWO), two_unit)  # S(1) = S(0)
    one_is_zero = MP(Inst(Inst(Axiom(SUCC_INJ), "x", ONE), "y", ZERO), two_is_one)
    boom = MP(Inst(Axiom(SUCC_NEQ_ZERO), "x", ZERO), one_is_zero)
    return ImpIntro(pow2(_x), ImpIntro(hyp, boom))


def _pay_succ_inj() -> Pf:
    """Doubling is injective on the domain: instantiate the hoisted guard at
    ``y*2`` -- which the CLOSURE theorem `pow2_double` proves admissible --
    and cancel the 2. This is where the relativization earns its keep: the
    payment exists only because doubling stays inside the domain."""
    hyp = forall(
        "u!",
        "",
        Implies(pow2(_u0), Implies(Eq(mul(_y, TWO), _u0), Eq(mul(_x, TWO), _u0))),
    )
    doubled = MP(Inst(pow2_double(), "x", _y), Assume(pow2(_y)))  # pow2(y*2)
    at_double = ForallElim(Assume(hyp), mul(_y, TWO))
    x2_eq_y2 = MP(MP(at_double, doubled), Refl(mul(_y, TWO)))  # x*2 = y*2
    halved = MP(Inst(Inst(cancel_two(), "a", _x), "b", _y), x2_eq_y2)
    return ImpIntro(pow2(_x), ImpIntro(pow2(_y), ImpIntro(hyp, halved)))


def _pay_totality_zero() -> Pf:
    """1 is in the domain and is the image of 0."""
    c = Var("c!")
    claim = exists("c!", "", And(pow2(c), Eq(c, ONE)))
    packed = and_intro(pow2(ONE), Eq(ONE, ONE), pow2_one(), Refl(ONE))
    return ExistsIntro(claim, ONE, packed)


def _pay_totality_succ() -> Pf:
    """Doubling is total on the domain -- the closure theorem, packaged."""
    x0, c = Var("x!0"), Var("c!")
    claim = exists("c!", "", And(pow2(c), Eq(mul(x0, TWO), c)))
    image = mul(x0, TWO)
    in_domain = MP(Inst(pow2_double(), "x", x0), Assume(pow2(x0)))
    packed = and_intro(pow2(image), Eq(image, image), in_domain, Refl(image))
    return ImpIntro(pow2(x0), ExistsIntro(claim, image, packed))


def _uniqueness(graph: Formula, graph_at_d: Formula, guards: tuple, core: Pf) -> Pf:
    """The common shape: two graph hypotheses, transitivity, delta wrappers."""
    out = ImpIntro(graph, ImpIntro(graph_at_d, core))
    for g in reversed(guards):
        out = ImpIntro(pow2(g), out)
    return out


def _pay_uniqueness_zero() -> Pf:
    c, d = Var("c!"), Var("d!")
    core = Trans(Assume(Eq(c, ONE)), Sym(Assume(Eq(d, ONE))))
    return _uniqueness(Eq(c, ONE), Eq(d, ONE), (c, d), core)


def _pay_uniqueness_succ() -> Pf:
    x0, c, d = Var("x!0"), Var("c!"), Var("d!")
    at_c, at_d = Eq(mul(x0, TWO), c), Eq(mul(x0, TWO), d)
    core = Trans(Sym(Assume(at_c)), Assume(at_d))
    return _uniqueness(at_c, at_d, (x0, c, d), core)


def _pay_uniqueness_add() -> Pf:
    x0, x1, c, d = Var("x!0"), Var("x!1"), Var("c!"), Var("d!")
    at_c, at_d = Eq(mul(x0, x1), c), Eq(mul(x0, x1), d)
    core = Trans(Sym(Assume(at_c)), Assume(at_d))
    return _uniqueness(at_c, at_d, (x0, x1, c, d), core)


def _pay_nonempty() -> Pf:
    claim = exists("x!", "", pow2(Var("x!")))
    return ExistsIntro(claim, ONE, pow2_one())


def skolem_interpretation() -> Interpretation:
    """Presburger -> PEANO's powers of two, over multiplication alone.

    Ten obligations paid; `totality:+` -- the product of two powers of two is
    a power of two -- is offered no payment and stays on the ledger: proving
    it needs descent (an odd divisor of x*y must fall through x's dyadic
    layers), which awaits an order kit."""
    return Interpretation(
        name="presburger-into-skolem-powers-of-two",
        source=PRESBURGER,
        target=PEANO,
        symbols=(ZERO_AS_ONE, SUCC_AS_DOUBLE, ADD_AS_MUL),
        domain=pow2,
        payments=(
            (f"axiom:{ADD_ZERO_F!r}", _pay_add_zero()),
            (f"axiom:{ADD_SUCC_F!r}", _pay_add_succ()),
            (f"axiom:{SUCC_NEQ_ZERO!r}", _pay_succ_neq_zero()),
            (f"axiom:{SUCC_INJ!r}", _pay_succ_inj()),
            ("totality:0", _pay_totality_zero()),
            ("uniqueness:0", _pay_uniqueness_zero()),
            ("totality:S", _pay_totality_succ()),
            ("uniqueness:S", _pay_uniqueness_succ()),
            ("uniqueness:+", _pay_uniqueness_add()),
            ("domain:nonempty", _pay_nonempty()),
        ),
    )


if __name__ == "__main__":
    from .interp import verify

    report = verify(skolem_interpretation())
    print(
        f"{report.name}: bridge {report.bridge_size} nodes; "
        f"toll {report.total_toll}; open {report.open_labels()}"
    )


__all__ = [
    "ADD_AS_MUL",
    "POW2_DOUBLE",
    "SUCC_AS_DOUBLE",
    "ZERO_AS_ONE",
    "pow2",
    "pow2_double",
    "pow2_one",
    "skolem_interpretation",
]
