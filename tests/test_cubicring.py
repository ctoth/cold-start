"""The cubic-ring factorization certificate behind the HRT Lemma 7.1.

The identity d * e = N in Z[theta | theta^3 = 2], where

    d = k + m*theta + n*theta^2
    e = (k^2 - 2mn) + (2n^2 - km)*theta + (m^2 - kn)*theta^2
    N = k^3 + 2m^3 + 4n^3 - 6kmn

is the algebraic heart of the small-divisor bound in Oussa's four-point HRT
counterexample (Lemma 7.1): e is the conjugate product d'd'', so |N| = |d| e,
and N is the norm form whose nonvanishing drives the Diophantine estimate.
The kernel proves the identity; the coordinate model here guards that the
statement is about the right polynomials (mirroring test_jacobian2's
frozenset model and test_groupring2's coordinate model)."""

import subprocess
import sys

from cold_start.checker import check
from cold_start.codec import encode_certificate, make_certificate
from cold_start.cubicring import (
    CUBIC_RING,
    GEN_K,
    GEN_M,
    GEN_N,
    GEN_TH,
    cofactor_minus_term,
    cofactor_plus_term,
    cofactor_term,
    element_term,
    norm_minus_term,
    norm_plus_term,
    norm_term,
)
from cold_start.cubicring_proofs import (
    factorization_proof,
    factorization_statement,
)
from cold_start.sequent import Sequent
from cold_start.syntax import Eq, Fun, Term

# --- an independent coordinate model of Z[theta]/(theta^3 - 2) ------------

Triple = tuple[int, int, int]


def _tadd(a: Triple, b: Triple) -> Triple:
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])


def _tmul(a: Triple, b: Triple) -> Triple:
    return (
        a[0] * b[0] + 2 * (a[1] * b[2] + a[2] * b[1]),
        a[0] * b[1] + a[1] * b[0] + 2 * a[2] * b[2],
        a[0] * b[2] + a[1] * b[1] + a[2] * b[0],
    )


def _tneg(a: Triple) -> Triple:
    return (-a[0], -a[1], -a[2])


def evaluate(term: Term, k: int, m: int, n: int) -> Triple:
    if type(term) is not Fun:
        raise TypeError(f"model evaluates ground Fun terms, got {term!r}")
    consts: dict[str, Triple] = {
        "0": (0, 0, 0),
        "1": (1, 0, 0),
        "th": (0, 1, 0),
        "k": (k, 0, 0),
        "m": (m, 0, 0),
        "n": (n, 0, 0),
    }
    if term.name in consts:
        return consts[term.name]
    args = [evaluate(a, k, m, n) for a in term.args]
    if term.name == "+":
        return _tadd(args[0], args[1])
    if term.name == "*":
        return _tmul(args[0], args[1])
    if term.name == "neg":
        return _tneg(args[0])
    raise ValueError(f"unknown symbol {term.name!r}")


_SAMPLES = [(0, 1, 0), (1, 0, 1), (2, -3, 5), (-7, 4, -1), (11, 13, -17)]


def test_the_statement_is_the_norm_factorization() -> None:
    """Model guard: the subtraction-free statement holds in the model, and it
    is exactly d * e = N rearranged — d*e+ + N- and N+ + d*e- differ from
    those by the same moved terms, so d * e = N follows in the model."""
    statement = factorization_statement()
    assert type(statement) is Eq
    for k, m, n in _SAMPLES:
        lhs = evaluate(statement.lhs, k, m, n)
        rhs = evaluate(statement.rhs, k, m, n)
        assert lhs == rhs
        d = evaluate(element_term(), k, m, n)
        e = evaluate(cofactor_term(), k, m, n)
        norm = k**3 + 2 * m**3 + 4 * n**3 - 6 * k * m * n
        assert _tmul(d, e) == (norm, 0, 0)
        # the split parts recombine to the paper's e and N
        assert _tadd(
            evaluate(cofactor_plus_term(), k, m, n),
            _tneg(evaluate(cofactor_minus_term(), k, m, n)),
        ) == e
        assert _tadd(
            evaluate(norm_plus_term(), k, m, n),
            _tneg(evaluate(norm_minus_term(), k, m, n)),
        ) == (norm, 0, 0)


def test_the_ingredients_denote_what_the_paper_says() -> None:
    for k, m, n in _SAMPLES:
        assert evaluate(element_term(), k, m, n) == (k, m, n)
        assert evaluate(cofactor_term(), k, m, n) == (
            k * k - 2 * m * n,
            2 * n * n - k * m,
            m * m - k * n,
        )
        assert evaluate(norm_term(), k, m, n) == (
            k**3 + 2 * m**3 + 4 * n**3 - 6 * k * m * n,
            0,
            0,
        )


def test_the_generators_are_distinct_constants() -> None:
    assert len({GEN_TH, GEN_K, GEN_M, GEN_N}) == 4


def test_factorization_checks() -> None:
    """The kernel re-derives d * e = N from the ring axioms plus theta^3 = 2,
    hypothesis-free."""
    seq = check(factorization_proof(), CUBIC_RING)
    assert seq == Sequent(frozenset(), factorization_statement())


def test_factorization_verifies_in_a_fresh_process() -> None:
    proof_bytes = encode_certificate(
        make_certificate("cubicring", CUBIC_RING, factorization_proof())
    )
    result = subprocess.run(
        [sys.executable, "-m", "cold_start.verify"],
        input=proof_bytes,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr.decode()
    assert repr(factorization_statement()) in result.stdout.decode()
