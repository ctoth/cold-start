"""Padoa's method, executably: `+` is NOT definable from `·` alone.

Julia Robinson (1949, p. 100) cites Padoa's method for why `(N, ·)` — Skolem
arithmetic — cannot define addition. The argument is model-theoretic and has two
halves:

  1. Any relation first-order definable from a structure's primitives is invariant
     under every automorphism of that structure. (Standard: automorphisms preserve
     satisfaction of every formula over the signature they act on.)
  2. The multiplicative monoid of the positive integers has automorphisms that
     permute the primes — unique factorization makes any prime permutation extend
     to a multiplicative bijection. One of them, `sigma` below, does not preserve
     the graph of `+`. Hence that graph is not definable over `{·}` alone.

Successor is exactly what such an automorphism cannot survive: `S` pins down
1, 2 = S1, 3 = SS1, ..., so the only automorphism of `(N, S, ·)` is the identity.
That rigidity is what lets Robinson's `bridge` define `+` — see
`cold_start/robinson.py`.

HONESTY NOTE. Everything below is a *witness*, not a proof of the general theorem.
Step 1 (definable => automorphism-invariant) is a metatheorem we do not mechanise;
these tests mechanise step 2 — they exhibit a concrete automorphism of `(N+, ·)`
and check, on a finite grid, that it preserves `·` and demolishes `+` and `S`. A
single counterexample to invariance is genuinely enough to refute definability
*given* step 1, but the finite grid means we verify the automorphism property only
on samples, not universally.
"""

from __future__ import annotations

import pytest
from semantics import Model, evaluate

from cold_start.robinson import bridge
from cold_start.syntax import Fun, Var, children

# --- sigma: the prime-permuting automorphism ------------------------------


def sigma(n: int) -> int:
    """The multiplicative automorphism of the positive integers that swaps the
    primes 2 and 3, i.e. swaps their exponents in the prime factorization:

        n = 2^i · 3^j · m   (m coprime to 6)   |->   2^j · 3^i · m

    So sigma(1)=1, sigma(2)=3, sigma(3)=2, sigma(4)=9, sigma(6)=6, and sigma(p)=p
    for every prime p >= 5. It is multiplicative and an involution."""
    if n < 1:
        raise ValueError(f"sigma is defined on the positive integers, not {n}")
    twos = threes = 0
    while n % 2 == 0:
        n //= 2
        twos += 1
    while n % 3 == 0:
        n //= 3
        threes += 1
    return n * 2**threes * 3**twos  # the exponents, swapped


GRID = tuple(range(1, 41))  # 1..40: enough factorizations to bite
PAIRS = tuple((a, b) for a in range(1, 16) for b in range(1, 16))


@pytest.mark.parametrize("n,want", [(1, 1), (2, 3), (3, 2), (4, 9), (6, 6), (5, 5), (7, 7)])
def test_sigma_table(n, want):
    # The defining values: 2 <-> 3, and every other prime fixed.
    assert sigma(n) == want


@pytest.mark.parametrize("a,b", PAIRS)
def test_sigma_is_multiplicative(a, b):
    # sigma(a·b) = sigma(a)·sigma(b): sigma IS an automorphism of the
    # multiplicative monoid (on this grid).
    assert sigma(a * b) == sigma(a) * sigma(b)


@pytest.mark.parametrize("n", GRID)
def test_sigma_is_an_involution(n):
    # sigma . sigma = id, so sigma is a bijection -- an automorphism, not merely
    # a multiplicative endomorphism.
    assert sigma(sigma(n)) == n


@pytest.mark.parametrize("n", GRID)
def test_sigma_is_injective_on_the_grid(n):
    # Injectivity follows from the involution, but state it: distinct inputs get
    # distinct images, so no collapsing.
    assert sum(1 for m in GRID if sigma(m) == sigma(n)) == 1


# --- the Padoa punchline --------------------------------------------------


def test_sigma_does_not_preserve_addition():
    """The counterexample. In the positive integers 2 + 2 = 4, so if the graph of
    `+` were definable over `{·}` alone it would be invariant under sigma, giving
    sigma(2) + sigma(2) = sigma(4). It does not: 3 + 3 = 6, but sigma(4) = 9.

    Conclusion (given the metatheorem that definable relations are
    automorphism-invariant): NO first-order formula over the signature `{·}` alone
    defines the graph of addition on the positive integers."""
    assert 2 + 2 == 4
    assert sigma(2) + sigma(2) == 6
    assert sigma(4) == 9
    assert sigma(2) + sigma(2) != sigma(4)


def test_addition_graph_is_moved_by_sigma_broadly():
    # Not a one-off accident: sigma moves the MAJORITY of the graph of + on the
    # grid. Since a definable relation would be moved by NO automorphism, one
    # witness suffices -- but the scale shows how badly `·` alone loses addition.
    moved = [(a, b) for a, b in PAIRS if sigma(a) + sigma(b) != sigma(a + b)]
    assert (2, 2) in moved
    assert len(moved) > len(PAIRS) // 2


@pytest.mark.parametrize("a,b", [(2, 2), (1, 1), (2, 4), (3, 3), (4, 5)])
def test_named_triples_leave_the_graph_of_addition(a, b):
    # Named witnesses: each (a, b, a+b) is in the graph of +, and its sigma-image
    # is not.
    assert sigma(a) + sigma(b) != sigma(a + b)


def test_sigma_does_not_preserve_successor():
    """Successor is exactly what sigma cannot survive: S(1) = 2, so invariance
    would demand sigma(S(1)) = S(sigma(1)), i.e. sigma(2) = S(1) = 2. But
    sigma(2) = 3. Adding `S` to the signature therefore kills this automorphism --
    the rigidification Robinson's bridge relies on."""
    assert sigma(1) == 1
    assert sigma(1 + 1) == 3
    assert sigma(1) + 1 == 2
    assert sigma(1 + 1) != sigma(1) + 1


@pytest.mark.parametrize("n", GRID)
def test_successor_invariance_at_n_forces_sigma_to_fix_n_and_n_plus_one(n):
    # If sigma preserved S at n while fixing n, it would have to fix n+1 too --
    # the induction that rigidifies the integers. Contrapositive on the grid:
    # wherever sigma moves n+1 but fixes n, S-invariance fails outright.
    if sigma(n) == n and sigma(n + 1) != n + 1:
        assert sigma(n + 1) != sigma(n) + 1


def test_only_the_identity_survives_S_on_the_grid():
    # Any sigma-like map that preserved S and fixed 1 would fix 1,2,3,... pointwise.
    # sigma does not fix 2, so sigma does not preserve S -- witnessed concretely.
    fixed_by_sigma = [n for n in GRID if sigma(n) == n]
    assert 2 not in fixed_by_sigma
    assert 1 in fixed_by_sigma


# --- tying it to the codebase's formulas via the model evaluator ----------

# The standard model over `(S, ·)` used by tests/test_robinson.py -- no `+` in the
# interpretation, because the point is that `+` is not part of this structure.
N = Model("N", interp={"0": lambda: 0, "S": lambda x: x + 1, "*": lambda a, b: a * b})

BRIDGE = bridge(Var("a"), Var("b"), Var("c"))


@pytest.mark.parametrize("a,b", [(2, 2), (2, 3), (4, 6), (3, 5), (1, 7), (8, 9), (12, 10)])
def test_sigma_preserves_the_interpreted_product_term(a, b):
    """The same preservation, stated on the codebase's own syntax through the
    shared evaluator: the term `a·b` evaluated at the sigma-images of its
    variables equals sigma of its value at the originals. That equivariance is
    what "automorphism of the `·`-reduct" means."""
    prod = Fun("*", (Var("a"), Var("b")))
    env = {"a": a, "b": b}
    senv = {k: sigma(v) for k, v in env.items()}
    assert evaluate(prod, N, senv) == sigma(evaluate(prod, N, env))


def _mul_only(node: object) -> bool:
    """True for terms built from variables and `·` alone -- no `S` anywhere."""
    if type(node) is Var:
        return True
    if type(node) is Fun:
        return node.name == "*" and all(_mul_only(arg) for arg in node.args)
    return False


def maximal_mul_subterms(node: object) -> list:
    """The largest subterms of `node` that live in the `·`-only signature."""
    if type(node) is Fun and _mul_only(node):
        return [node]
    return [t for kid in children(node) for t in maximal_mul_subterms(kid)]


def test_bridge_has_mul_only_subterms():
    # The bridge S(a·c)·S(b·c) = S((c·c)·S(a·b)) contains exactly four maximal
    # `·`-only subterms: a·c, b·c, c·c, a·b. Everything else is wrapped in S.
    subs = maximal_mul_subterms(BRIDGE)
    assert len(subs) == 4
    env = {"a": 2, "b": 5, "c": 7}
    assert sorted(evaluate(t, N, env) for t in subs) == sorted([2 * 7, 5 * 7, 7 * 7, 2 * 5])


@pytest.mark.parametrize("c", [1, 2, 3, 4, 5, 6, 8, 9])
@pytest.mark.parametrize("b", [1, 2, 3, 4, 5])
@pytest.mark.parametrize("a", [1, 2, 3, 4, 5])
def test_mul_only_subterms_of_bridge_are_sigma_equivariant(a, b, c):
    """The `·`-only part of Robinson's bridge IS sigma-equivariant: evaluating a
    `·`-only subterm at (sigma a, sigma b, sigma c) gives sigma of its value at
    (a, b, c). So no `{·}`-fragment of the bridge can be where sigma-variance
    enters -- it must enter through `S`."""
    env = {"a": a, "b": b, "c": c}
    senv = {k: sigma(v) for k, v in env.items()}
    for t in maximal_mul_subterms(BRIDGE):
        assert evaluate(t, N, senv) == sigma(evaluate(t, N, env))


def test_a_successor_subterm_of_bridge_is_not_sigma_equivariant():
    """...and it does. `S(a·c)` at (a,c) = (2,4) is S(8) = 9, whose sigma-image is
    4; but at (sigma a, sigma c) = (3, 9) it is S(27) = 28. The whole difference
    between a definable-from-`·` relation and Robinson's bridge sits in `S`."""
    a_c = Fun("*", (Var("a"), Var("c")))
    s_a_c = Fun("S", (a_c,))
    env = {"a": 2, "b": 2, "c": 4}
    senv = {k: sigma(v) for k, v in env.items()}
    assert evaluate(s_a_c, N, env) == 9
    assert sigma(evaluate(s_a_c, N, env)) == 4
    assert evaluate(s_a_c, N, senv) == 28
    assert evaluate(s_a_c, N, senv) != sigma(evaluate(s_a_c, N, env))


def test_bridge_truth_is_not_sigma_invariant():
    """The payoff on the codebase's own formula. `bridge(a,b,c)` is true in N
    exactly when a + b = c (c > 0) -- so it defines the graph of `+`. It is true
    at (2,2,4) and FALSE at the sigma-image (3,3,9). No contradiction with the
    automorphism argument: the bridge uses `S`, so it is not a `{·}`-formula, and
    sigma is not an automorphism of the structure it is interpreted in. That is
    precisely Robinson's point -- `S` is what makes `+` definable."""
    assert evaluate(BRIDGE, N, {"a": 2, "b": 2, "c": 4}) is True
    assert evaluate(BRIDGE, N, {"a": sigma(2), "b": sigma(2), "c": sigma(4)}) is False


@pytest.mark.parametrize("a,b", [(1, 1), (2, 2), (2, 3), (3, 5), (4, 4), (6, 6), (5, 7)])
def test_bridge_tracks_addition_under_sigma_exactly(a, b):
    """Sharper: the bridge holds at the sigma-image triple iff sigma(a) + sigma(b)
    = sigma(a+b). So the bridge's failure to be sigma-invariant is EXACTLY the
    failure of the graph of `+` to be sigma-invariant -- the bridge really is
    defining addition, and addition really is what sigma breaks."""
    senv = {"a": sigma(a), "b": sigma(b), "c": sigma(a + b)}
    assert evaluate(BRIDGE, N, senv) is (sigma(a) + sigma(b) == sigma(a + b))
    assert evaluate(BRIDGE, N, {"a": a, "b": b, "c": a + b}) is True
