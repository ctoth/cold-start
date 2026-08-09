"""The commutative ring Z[theta | theta^3 = 2] on rogue-coordinate constants.

The theory of the HRT Lemma 7.1 factorization certificate. The four
generators are CONSTANTS (`Fun`, not `Var`): `th` is the abstract cube root
of two, and `k`, `m`, `n` are the integer coordinates of a candidate small
divisor d = k + m*th + n*th^2 in Oussa's four-point counterexample. The
single non-ring axiom is CUBE: th * (th * th) = 1 + 1. Everything else is
the stock commutative-ring axiom set, negation included — the coefficients
of the conjugate cofactor genuinely need subtraction.

The payload theorem (`cubicring_proofs`) is the norm factorization
d * e = k^3 + 2m^3 + 4n^3 - 6kmn with e the conjugate product d'd'' — the
identity that turns "the norm form has no nontrivial zeros" into the
quantitative small-divisor bound. The descent and the inequalities live in
the Lean/Mathlib companion (`jc/hrt/formal`); this module owns the layer
that is purely equational.
"""

from __future__ import annotations

from .algebra import COMM_RING, RING_SIG
from .syntax import Eq, Fun, Term
from .theory import Signature, Theory
from .vocabulary import ONE, add, mul, neg

# --- generators ------------------------------------------------------------

GEN_TH: Term = Fun("th", ())
GEN_K: Term = Fun("k", ())
GEN_M: Term = Fun("m", ())
GEN_N: Term = Fun("n", ())
GENERATORS: tuple[Term, ...] = (GEN_TH, GEN_K, GEN_M, GEN_N)

TWO: Term = add(ONE, ONE)

CUBE: Eq = Eq(mul(GEN_TH, mul(GEN_TH, GEN_TH)), TWO)

# --- the paper's three polynomials -----------------------------------------


def _sub(x: Term, y: Term) -> Term:
    return add(x, neg(y))


def _sq(x: Term) -> Term:
    return mul(x, x)


def _cube(x: Term) -> Term:
    return mul(x, mul(x, x))


def element_term() -> Term:
    """d = k + m*th + n*th^2, the candidate small divisor."""
    return add(GEN_K, add(mul(GEN_M, GEN_TH), mul(GEN_N, _sq(GEN_TH))))


def cofactor_term() -> Term:
    """e = (k^2 - 2mn) + (2n^2 - km)*th + (m^2 - kn)*th^2, the conjugate
    product d'd'' written on the basis (1, th, th^2)."""
    c0 = _sub(_sq(GEN_K), mul(TWO, mul(GEN_M, GEN_N)))
    c1 = _sub(mul(TWO, _sq(GEN_N)), mul(GEN_K, GEN_M))
    c2 = _sub(_sq(GEN_M), mul(GEN_K, GEN_N))
    return add(c0, add(mul(c1, GEN_TH), mul(c2, _sq(GEN_TH))))


def norm_term() -> Term:
    """N = k^3 + 2m^3 + 4n^3 - 6kmn, the norm form of Q(cbrt 2)."""
    four = add(TWO, TWO)
    six = add(TWO, four)
    return add(
        _cube(GEN_K),
        add(
            mul(TWO, _cube(GEN_M)),
            _sub(mul(four, _cube(GEN_N)), mul(six, mul(GEN_K, mul(GEN_M, GEN_N)))),
        ),
    )


def residue_term() -> Term:
    """g with d*e = N + (th^3 - 2)*g as a plain ring identity:
    g = (m^3 + 2n^3 - 2kmn) + (n m^2 - k n^2)*th."""
    g0 = _sub(
        add(_cube(GEN_M), mul(TWO, _cube(GEN_N))),
        mul(TWO, mul(GEN_K, mul(GEN_M, GEN_N))),
    )
    g1 = _sub(mul(GEN_N, _sq(GEN_M)), mul(GEN_K, _sq(GEN_N)))
    return add(g0, mul(g1, GEN_TH))


# --- subtraction-free split forms ------------------------------------------
# The statement is arranged with every subtraction moved across the equals
# sign, so each side has only natural coefficients: the sparse normalizer
# then never has to justify a coefficient cancellation mid-merge, and the
# one genuine cancellation happens in the trusted right-cancellation step
# of `elaborate_combination`. Over any ring the arrangement is equivalent
# to d * e = N; the model tests pin that equivalence.


def cofactor_plus_term() -> Term:
    """e+ = k^2 + 2n^2*th + m^2*th^2."""
    return add(
        _sq(GEN_K),
        add(mul(mul(TWO, _sq(GEN_N)), GEN_TH), mul(_sq(GEN_M), _sq(GEN_TH))),
    )


def cofactor_minus_term() -> Term:
    """e- = 2mn + km*th + kn*th^2, so e = e+ - e-."""
    return add(
        mul(TWO, mul(GEN_M, GEN_N)),
        add(
            mul(mul(GEN_K, GEN_M), GEN_TH),
            mul(mul(GEN_K, GEN_N), _sq(GEN_TH)),
        ),
    )


def norm_plus_term() -> Term:
    """N+ = k^3 + 2m^3 + 4n^3."""
    four = add(TWO, TWO)
    return add(_cube(GEN_K), add(mul(TWO, _cube(GEN_M)), mul(four, _cube(GEN_N))))


def norm_minus_term() -> Term:
    """N- = 6kmn, so N = N+ - N-."""
    six = add(TWO, add(TWO, TWO))
    return mul(six, mul(GEN_K, mul(GEN_M, GEN_N)))


def residue_plus_term() -> Term:
    """g+ = m^3 + 2n^3 + n m^2 * th."""
    return add(
        _cube(GEN_M),
        add(mul(TWO, _cube(GEN_N)), mul(mul(GEN_N, _sq(GEN_M)), GEN_TH)),
    )


def residue_minus_term() -> Term:
    """g- = 2kmn + k n^2 * th, so g = g+ - g-."""
    return add(
        mul(TWO, mul(GEN_K, mul(GEN_M, GEN_N))),
        mul(mul(GEN_K, _sq(GEN_N)), GEN_TH),
    )


# --- the theory -------------------------------------------------------------

CUBIC_RING_SIG = Signature(
    sorts=frozenset({""}),
    ranks=(
        *RING_SIG.ranks,
        ("th", (), ""),
        ("k", (), ""),
        ("m", (), ""),
        ("n", (), ""),
    ),
)

CUBIC_RING = Theory(
    axioms=COMM_RING.axioms | {CUBE},
    signature=CUBIC_RING_SIG,
)

__all__ = [
    "CUBE",
    "CUBIC_RING",
    "CUBIC_RING_SIG",
    "GENERATORS",
    "GEN_K",
    "GEN_M",
    "GEN_N",
    "GEN_TH",
    "TWO",
    "cofactor_minus_term",
    "cofactor_plus_term",
    "cofactor_term",
    "element_term",
    "norm_minus_term",
    "norm_plus_term",
    "norm_term",
    "residue_minus_term",
    "residue_plus_term",
    "residue_term",
]
