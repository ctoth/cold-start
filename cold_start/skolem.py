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

EVERY obligation is paid; the bridge is a theorem, not a conjecture. The
doubling graph's definedness and the translated successor injectivity ride
Euclid's lemma at 2 (`cold_start.parity`); the last debt -- `totality:+`,
that a product of powers of two is a power of two -- fell to course-of-values
descent through the dyadic layers (`cold_start.order`): the order kit the
ledger asked for is exactly what paid it.

Untrusted, like every prover module: `check` remains the only judge.
"""

from __future__ import annotations

from .divisibility import divides_one, divides_product, divides_refl, peano_divides
from .interp import GraphSymbol, Interpretation, ObligationKey
from .order import course_of_values, pos_half_le, reach
from .parity import TWO, cancel_two, euclid_two, even_ne_odd
from .peano import MUL_ZERO_F, PEANO
from .peano_proofs import MUL_ASSOC, MUL_COMM, mul_assoc, mul_comm
from .peano_proofs import MUL_RULES as _MUL_RULES
from .presburger import (
    ADD_SUCC_F,
    ADD_ZERO_F,
    PRESBURGER,
    SUCC_INJ,
    SUCC_NEQ_ZERO,
)
from .presburger_proofs import ADD_RULES, LEFT_IDENTITY, left_identity, zero_or_succ
from .proof import (
    MP,
    RAA,
    Assume,
    Axiom,
    Cong,
    ExFalso,
    ExistsElim,
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
from .prop import And, and_intro, or_elim
from .syntax import Bottom, Eq, Formula, Implies, Not, Term, Var, exists, forall
from .tactics import lemma_rule, prove_eq, simultaneous_inst, transport
from .vocabulary import ZERO, S, mul

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


THREE = S(TWO)

NOT_POW2_ZERO: Formula = Not(pow2(ZERO))


def not_pow2_zero() -> Pf:
    """Zero is no power of two: 3 divides 0, is not 1, and is odd.

    The odd witness 3 turns the domain guard into `2 | 3`, whose divisibility
    witness makes an even number equal S(1*2) -- even equals odd, absurd."""
    hyp = pow2(ZERO)
    at_three = ForallElim(Assume(hyp), THREE)
    divides_zero = ExistsIntro(
        peano_divides(THREE, ZERO), ZERO, Inst(Axiom(MUL_ZERO_F), "x", THREE)
    )
    three_is_one = Eq(THREE, ONE)
    two_is_zero = MP(Inst(Inst(Axiom(SUCC_INJ), "x", TWO), "y", ZERO), Assume(three_is_one))
    ne_three_one = ImpIntro(three_is_one, MP(Inst(Axiom(SUCC_NEQ_ZERO), "x", ONE), two_is_zero))
    even_three = MP(MP(at_three, divides_zero), ne_three_one)  # 2 | 3

    k = Var("k!")
    witness = Eq(mul(TWO, k), THREE)
    comm = lemma_rule(MUL_COMM, mul_comm())
    as_odd = Trans(
        comm.instance({"x": k, "y": TWO}),  # k!*2 = 2*k!
        Trans(
            Assume(witness),
            Sym(prove_eq(Eq(S(mul(ONE, TWO)), THREE), (*ADD_RULES, *_MUL_RULES))),
        ),
    )  # k!*2 = S(1*2)
    refute = Inst(Inst(even_ne_odd(), "b", ONE), "a", k)
    return ImpIntro(hyp, ExistsElim("k!", even_three, MP(refute, as_odd)))


POW2_HALF: Formula = Implies(pow2(mul(_x, TWO)), pow2(_x))


def pow2_half() -> Pf:
    """The powers of two are closed DOWNWARD through halving: a divisor of the
    half divides the double, where the domain already pronounces it even."""
    hyp = pow2(mul(_x, TWO))
    d = Var("d")
    dvd, ne_one = peano_divides(d, _x), Not(Eq(d, ONE))
    lift = MP(
        Inst(Inst(Inst(divides_product(), "a", d), "b", _x), "c", TWO),
        Assume(dvd),
    )  # d | x*2
    even = MP(MP(ForallElim(Assume(hyp), d), lift), Assume(ne_one))
    return ImpIntro(hyp, ForallIntro("d", "", ImpIntro(dvd, ImpIntro(ne_one, even))))


POW2_MUL: Formula = Implies(pow2(_x), Implies(pow2(_y), pow2(mul(_x, _y))))


def _one_times(t: Term) -> Pf:
    """1*t = t, through commutativity and the evaluated t*1."""
    return Trans(lemma_rule(MUL_COMM, mul_comm()).instance({"x": ONE, "y": t}), _mul_one(t))


def pow2_mul() -> Pf:
    """Product closure of the powers of two -- the strong-induction descent.

    By course-of-values induction on ``x``. An odd divisor ``d != 1`` of
    ``x*y`` must be refuted: at ``x = S(n)`` either ``n = 0`` (so ``x*y = y``
    and ``pow2(y)`` refutes it directly) or ``x`` is even by its own domain
    membership, ``x = h*2`` with ``h <= n`` (`pos_half_le`) and ``pow2(h)``
    (`transport` + `pow2_half`); Euclid's lemma at 2 drops ``d`` through the
    doubling to a divisor of ``h*y``, where the reach hypothesis -- closure
    one dyadic layer down -- pronounces it even after all. This is the
    descent the ledger said was missing; the order kit is what pays it."""
    comm = lemma_rule(MUL_COMM, mul_comm())
    assoc = lemma_rule(MUL_ASSOC, mul_assoc())
    bound = Var("n!")

    # base: pow2(0) is absurd.
    rest = Implies(pow2(_y), pow2(mul(ZERO, _y)))
    base = ImpIntro(pow2(ZERO), ExFalso(MP(not_pow2_zero(), Assume(pow2(ZERO))), rest))

    # step: everything at or below n! is closed; close S(n!).
    below = reach("x", POW2_MUL, bound)
    x_pow, y_pow = pow2(S(bound)), pow2(_y)
    d = Var("d")
    dvd = peano_divides(d, mul(S(bound), _y))
    ne_one = Not(Eq(d, ONE))
    even_d = peano_divides(TWO, d)
    odd_d = Not(even_d)
    k, h, m, p = Var("k!"), Var("h!"), Var("m!"), Var("p!")
    witness = Eq(mul(d, k), mul(S(bound), _y))

    # n! = 0: S(n!)*y is y itself; the divisor drops straight into pow2(y).
    n_zero = Eq(bound, ZERO)
    product_is_y = Trans(
        Cong("*", (Cong("S", (Assume(n_zero),)), Refl(_y))),  # S(n!)*y = S(0)*y
        _one_times(_y),
    )
    dvd_y = ExistsIntro(peano_divides(d, _y), k, Trans(Assume(witness), product_is_y))
    even_from_y = MP(MP(ForallElim(Assume(y_pow), d), dvd_y), Assume(ne_one))
    arm_zero = ImpIntro(n_zero, ExistsElim("k!", Assume(dvd), MP(Assume(odd_d), even_from_y)))

    # n! = S(m!): S(n!) is even by its own domain membership; halve and descend.
    ex_n_succ = exists("m", "", Eq(bound, S(Var("m"))))
    n_succ = Eq(bound, S(m))
    self_dvd = Inst(divides_refl(), "a", S(bound))
    top_is_one = Eq(S(bound), ONE)
    n_is_zero = MP(Inst(Inst(Axiom(SUCC_INJ), "x", bound), "y", ZERO), Assume(top_is_one))
    succ_is_zero = Trans(Sym(Assume(n_succ)), n_is_zero)  # S(m!) = 0
    ne_top_one = ImpIntro(top_is_one, MP(Inst(Axiom(SUCC_NEQ_ZERO), "x", m), succ_is_zero))
    even_top = MP(MP(ForallElim(Assume(x_pow), S(bound)), self_dvd), ne_top_one)  # 2 | S(n!)

    h_witness = Eq(mul(TWO, h), S(bound))
    half_eq = Trans(Sym(Assume(h_witness)), comm.instance({"x": TWO, "y": h}))  # S(n!) = h!*2

    #   h! = 0 collapses S(n!) to zero.
    h_zero = Eq(h, ZERO)
    collapse = Trans(
        half_eq,
        Trans(
            Cong("*", (Assume(h_zero), Refl(TWO))),
            prove_eq(Eq(mul(ZERO, TWO), ZERO), (*ADD_RULES, *_MUL_RULES)),
        ),
    )  # S(n!) = 0
    arm_h_zero = ImpIntro(h_zero, MP(Inst(Axiom(SUCC_NEQ_ZERO), "x", bound), collapse))

    #   h! = S(p!): the half is positive -- descend one dyadic layer.
    ex_h_succ = exists("m", "", Eq(h, S(Var("m"))))
    h_succ = Eq(h, S(p))
    descend = simultaneous_inst(pos_half_le(), {"a": h, "m": p, "n": bound})
    h_below = MP(MP(descend, Assume(h_succ)), Sym(half_eq))  # h! <= n!
    hole = Var("t!")
    dom_double = transport(
        pow2(hole), "t!", Eq(S(bound), mul(h, TWO)), half_eq, Assume(x_pow)
    )  # pow2(h!*2)
    dom_half = MP(Inst(pow2_half(), "x", h), dom_double)  # pow2(h!)
    closed_below = MP(
        MP(MP(ForallElim(Assume(below), h), h_below), dom_half), Assume(y_pow)
    )  # pow2(h!*y)
    to_double = Trans(
        Assume(witness),  # d*k! = S(n!)*y
        Trans(
            Cong("*", (half_eq, Refl(_y))),  # S(n!)*y = (h!*2)*y
            Trans(
                assoc.instance({"x": h, "y": TWO, "z": _y}),  # (h!*2)*y = h!*(2*y)
                Trans(
                    Cong("*", (Refl(h), comm.instance({"x": TWO, "y": _y}))),
                    Sym(assoc.instance({"x": h, "y": _y, "z": TWO})),  # h!*(y*2) = (h!*y)*2
                ),
            ),
        ),
    )  # d*k! = (h!*y)*2
    dvd_double = ExistsIntro(peano_divides(d, mul(mul(h, _y), TWO)), k, to_double)
    dvd_layer = MP(MP(Inst(euclid_two(), "x", mul(h, _y)), Assume(odd_d)), dvd_double)  # d | h!*y
    even_from_layer = MP(MP(ForallElim(closed_below, d), dvd_layer), Assume(ne_one))
    arm_h_succ = ImpIntro(
        ex_h_succ,
        ExistsElim("p!", Assume(ex_h_succ), MP(Assume(odd_d), even_from_layer)),
    )

    h_cases = or_elim(
        h_zero, ex_h_succ, Bottom(), Inst(zero_or_succ(), "n", h), arm_h_zero, arm_h_succ
    )
    after_half = ExistsElim("h!", even_top, h_cases)
    after_witness = ExistsElim("k!", Assume(dvd), after_half)
    arm_succ = ImpIntro(ex_n_succ, ExistsElim("m!", Assume(ex_n_succ), after_witness))

    refuted = or_elim(
        n_zero, ex_n_succ, Bottom(), Inst(zero_or_succ(), "n", bound), arm_zero, arm_succ
    )
    body = RAA(even_d, refuted)
    closed = ForallIntro("d", "", ImpIntro(dvd, ImpIntro(ne_one, body)))
    step = ImpIntro(x_pow, ImpIntro(y_pow, closed))
    return course_of_values("x", POW2_MUL, "n!", base, step)


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


def _uniqueness(
    graph: Formula,
    graph_at_d: Formula,
    guards: tuple[Term, ...],
    core: Pf,
) -> Pf:
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


def _pay_totality_add() -> Pf:
    """Multiplication is total on the domain -- product closure, packaged."""
    x0, x1, c = Var("x!0"), Var("x!1"), Var("c!")
    claim = exists("c!", "", And(pow2(c), Eq(mul(x0, x1), c)))
    product = mul(x0, x1)
    in_domain = MP(
        MP(Inst(Inst(pow2_mul(), "x", x0), "y", x1), Assume(pow2(x0))),
        Assume(pow2(x1)),
    )
    packed = and_intro(pow2(product), Eq(product, product), in_domain, Refl(product))
    return ImpIntro(pow2(x0), ImpIntro(pow2(x1), ExistsIntro(claim, product, packed)))


def _pay_nonempty() -> Pf:
    claim = exists("x!", "", pow2(Var("x!")))
    return ExistsIntro(claim, ONE, pow2_one())


def skolem_interpretation() -> Interpretation:
    """Presburger -> PEANO's powers of two, over multiplication alone.

    All eleven obligations paid: the four translated axioms, definedness of
    all three graphs, and the domain's nonemptiness. `totality:+` -- product
    closure -- was the last to fall, by strong-induction descent through the
    order kit."""
    return Interpretation(
        name="presburger-into-skolem-powers-of-two",
        source=PRESBURGER,
        target=PEANO,
        symbols=(ZERO_AS_ONE, SUCC_AS_DOUBLE, ADD_AS_MUL),
        domain=pow2,
        payments=(
            (ObligationKey.axiom(ADD_ZERO_F), _pay_add_zero()),
            (ObligationKey.axiom(ADD_SUCC_F), _pay_add_succ()),
            (ObligationKey.axiom(SUCC_NEQ_ZERO), _pay_succ_neq_zero()),
            (ObligationKey.axiom(SUCC_INJ), _pay_succ_inj()),
            (ObligationKey.totality("0"), _pay_totality_zero()),
            (ObligationKey.uniqueness("0"), _pay_uniqueness_zero()),
            (ObligationKey.totality("S"), _pay_totality_succ()),
            (ObligationKey.uniqueness("S"), _pay_uniqueness_succ()),
            (ObligationKey.totality("+"), _pay_totality_add()),
            (ObligationKey.uniqueness("+"), _pay_uniqueness_add()),
            (ObligationKey.domain("nonempty"), _pay_nonempty()),
        ),
    )


__all__ = [
    "ADD_AS_MUL",
    "NOT_POW2_ZERO",
    "POW2_DOUBLE",
    "POW2_HALF",
    "POW2_MUL",
    "SUCC_AS_DOUBLE",
    "ZERO_AS_ONE",
    "not_pow2_zero",
    "pow2",
    "pow2_double",
    "pow2_half",
    "pow2_mul",
    "pow2_one",
    "skolem_interpretation",
]
