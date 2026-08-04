"""Komatsu's line, witnessed by exhaustive search over the (1, S, ·) terms.

## The punchline

`cold_start/robinson.py` defines addition from multiplication and successor with
a **formula** -- the `bridge`, `S(a·c)·S(b·c) = S((c·c)·S(a·b))`, which says
"`a + b = c`" relationally. A natural question is whether that detour is
necessary: why not just write `a + b` as a **term** in `1`, `S` and `·`?

Komatsu's theorem says it is necessary. As Wehrung reports it (arXiv:2405.08364,
p. 3, ref. [23]): *rings in which the addition is a composition of multiplication
and the successor function are characterized by their satisfying a polynomial
identity of the form* `xⁿ = x^(n+1)·p(x)`, *and then the latter can be taken as*
`xⁿ = x^(2n)` *for a suitable* `n`. Wehrung calls such a term a **brachynomial**
(Definition 3.2, p. 5).

So the line falls exactly where this repo needs it:

* `ℤ/2` satisfies `x = x²` (`n = 1`) and `ℤ/3` satisfies `x² = x⁴` (`n = 2`), so
  in those rings addition *is* a brachynomial -- and the searches below exhibit
  the actual terms.
* `ℤ` (and `ℕ`) satisfies **no** identity `xⁿ = x^(2n)`, so addition is *not* a
  brachynomial there. The search below confirms this boundedly.

Hence Robinson's bridge must be a relational formula rather than a defined term.
The definability is real, but it is first-order definability, not term
definability -- and that gap is not an artefact of Robinson's ingenuity, it is a
theorem.

## Honesty about what is asserted

The `ℤ/2` and `ℤ/3` tests are **witnesses**: they exhibit a term and verify it
everywhere on the ring, which is a complete proof for those finite rings.

The naturals test is **not** a proof. It exhaustively rules out every term up to
a size bound, evaluated on a finite grid. That is a bounded witness of what
Komatsu's theorem gives in general -- a test as evidence, not as proof. Two ways
it is weaker than the theorem: the size bound, and the grid (a term could agree
with `x + y` on the grid and diverge outside it -- which would only make the test
*more* permissive, so a pass is still meaningful).

## The search

Terms are enumerated by size (`1`, `x`, `y` have size 1; `S t` has size
`1 + |t|`; `a·b` has size `1 + |a| + |b|`) and deduplicated by their **value
vector** on the grid. Keeping only the first (smallest) representative of each
value vector is complete for "is this value vector reachable at size ≤ N?":
`S` and `·` act pointwise on value vectors, so replacing any subterm by a
same-valued smaller one yields a term of no greater size with the same vector.
"""

from __future__ import annotations

from semantics import Model, evaluate

from cold_start.notation import format_term
from cold_start.peano import mul
from cold_start.presburger import S
from cold_start.robinson import ONE
from cold_start.syntax import Term, Var

# A term is built as a plain nested tuple during the search -- cheap to create by
# the hundred thousand -- and converted to a real syntax node only for a witness.
ONE_R = ("1",)
X_R = ("x",)
Y_R = ("y",)


def to_term(repr_: tuple) -> Term:
    """Turn a search result into a genuine `cold_start.syntax` term over (1, S, ·)."""
    head = repr_[0]
    if head == "1":
        return ONE
    if head in ("x", "y"):
        return Var(head)
    if head == "S":
        return S(to_term(repr_[1]))
    return mul(to_term(repr_[1]), to_term(repr_[2]))


def search(grid, succ, times, max_size, target) -> tuple[int, tuple] | None:
    """Smallest term over {1, S, ·} in x, y whose value vector on `grid` is
    `target`, or None if there is none of size ≤ `max_size`.

    `grid` is a sequence of `(x, y)` pairs; `succ` and `times` interpret the two
    function symbols. Returns `(size, term_repr)`.
    """
    levels = {
        1: {
            tuple(1 for _ in grid): ONE_R,
            tuple(x for x, _ in grid): X_R,
            tuple(y for _, y in grid): Y_R,
        }
    }
    seen = dict(levels[1])
    if target in seen:
        return 1, seen[target]
    for n in range(2, max_size + 1):
        fresh: dict = {}
        for sig, term in levels[n - 1].items():
            new = tuple(succ(v) for v in sig)
            if new not in seen and new not in fresh:
                fresh[new] = ("S", term)
        for i in range(1, n - 1):
            j = n - 1 - i
            if j < 1:
                continue
            for sa, ta in levels[i].items():
                for sb, tb in levels[j].items():
                    new = tuple(times(a, b) for a, b in zip(sa, sb, strict=True))
                    if new not in seen and new not in fresh:
                        fresh[new] = ("*", ta, tb)
        levels[n] = fresh
        seen.update(fresh)
        if target in seen:
            return n, seen[target]
    return None


def modular_ring(m: int) -> tuple:
    """The grid, the two operations, and a `Model` for ℤ/mℤ."""
    grid = [(x, y) for x in range(m) for y in range(m)]
    model = Model(
        f"Z/{m}",
        interp={"0": lambda: 0, "S": lambda v: (v + 1) % m, "*": lambda a, b: (a * b) % m},
    )
    return grid, (lambda v: (v + 1) % m), (lambda a, b: (a * b) % m), model


# The positive integers: Robinson's domain, so the grid starts at 1.
NAT_GRID = [(x, y) for x in range(1, 7) for y in range(1, 7)]
NAT_MODEL = Model("N", interp={"0": lambda: 0, "S": lambda v: v + 1, "*": lambda a, b: a * b})
NAT_BOUND = 15
"""Every term of at most this many nodes is enumerated for the naturals."""


def check_witness(repr_: tuple, grid, model, expected) -> str:
    """Re-verify a found term the hard way: build the real syntax node and run it
    through the repo's own model evaluator, independently of the search's
    internal arithmetic. Returns the rendered term."""
    term = to_term(repr_)
    for (x, y), want in zip(grid, expected, strict=True):
        got = evaluate(term, model, {"x": x, "y": y})
        assert got == want, f"{format_term(term)} gave {got} at x={x}, y={y}, wanted {want}"
    return format_term(term)


# --- the enumerator itself must be trustworthy -----------------------------


def test_search_finds_a_term_that_does_exist():
    # A positive control, and the guard that keeps the negative test below from
    # passing vacuously: (x + 2)·y IS a term over (1, S, ·), so the search must
    # find it. If the enumerator ever breaks, this goes red first.
    found = search(NAT_GRID, lambda v: v + 1, lambda a, b: a * b, 8,
                   tuple((x + 2) * y for x, y in NAT_GRID))
    assert found is not None
    size, repr_ = found
    assert size == 5
    assert check_witness(repr_, NAT_GRID, NAT_MODEL,
                         [(x + 2) * y for x, y in NAT_GRID]) == "y * S(S(x))"


def test_search_respects_its_size_bound_exactly():
    # The bound is a real cutoff in both directions: the Z/2 witness below has
    # size 11, so the same search returns None at 10 and finds it at 11. Without
    # this, "no term of size <= N" could be an off-by-one about what N means.
    grid, succ, times, _ = modular_ring(2)
    target = tuple((x + y) % 2 for x, y in grid)
    assert search(grid, succ, times, 10, target) is None
    at_eleven = search(grid, succ, times, 11, target)
    assert at_eleven is not None and at_eleven[0] == 11


# --- Komatsu, positive side: addition IS a brachynomial in Z/n -------------


def test_addition_is_a_brachynomial_on_Z2():
    # Z/2 satisfies x = x² (Komatsu's xⁿ = x^(2n) at n = 1), so addition must be a
    # term in 1, S and ·. It is, and the smallest one is
    #
    #     x + y = S(x·y) · S(S(x)·S(y))
    #
    # which is Robinson's own bridge shape read at c = 1: a product of two
    # successors of products. Check: (xy+1)((x+1)(y+1)+1) = (xy+1)(xy+x+y) and
    # with x² = x, y² = y that is 4xy + x + y = x + y over Z/2.
    grid, succ, times, model = modular_ring(2)
    expected = [(x + y) % 2 for x, y in grid]
    found = search(grid, succ, times, 12, tuple(expected))
    assert found is not None, "Komatsu says addition is a brachynomial over Z/2"
    size, repr_ = found
    rendered = check_witness(repr_, grid, model, expected)
    assert rendered == "S(x * y) * S(S(x) * S(y))", rendered
    assert size == 11, f"smallest brachynomial for + over Z/2 is {rendered} (size {size})"


def test_addition_is_a_brachynomial_on_Z3():
    # Z/3 satisfies x² = x⁴ (Komatsu's xⁿ = x^(2n) at n = 2), so addition is again
    # a term -- a bigger one, as the identity is weaker:
    #
    #     x + y = S(x·y) · S(S(S(x)·(S(y)·S(x·y))))
    grid, succ, times, model = modular_ring(3)
    expected = [(x + y) % 3 for x, y in grid]
    found = search(grid, succ, times, 18, tuple(expected))
    assert found is not None, "Komatsu says addition is a brachynomial over Z/3"
    size, repr_ = found
    rendered = check_witness(repr_, grid, model, expected)
    assert rendered == "S(x * y) * S(S(S(x) * (S(y) * S(x * y))))", rendered
    assert size == 17, f"smallest brachynomial for + over Z/3 is {rendered} (size {size})"


# --- Komatsu, negative side: addition is NOT a brachynomial on N ----------


def test_no_brachynomial_computes_addition_on_the_positive_integers():
    # The reason robinson.py's bridge is a FORMULA. N satisfies no identity
    # xⁿ = x^(2n) (x = 2 already refutes every one of them), so by Komatsu no term
    # over {1, S, ·} equals x + y. Exhaustive search confirms it up to size 15,
    # evaluated on x, y in 1..6 -- a bounded witness, not a proof of the theorem.
    found = search(NAT_GRID, lambda v: v + 1, lambda a, b: a * b, NAT_BOUND,
                   tuple(x + y for x, y in NAT_GRID))
    assert found is None, (
        f"a term over (1, S, ·) of size <= {NAT_BOUND} computed x + y on the naturals: "
        f"{format_term(to_term(found[1])) if found else ''} -- which would contradict "
        "Komatsu's theorem, so suspect the search before the mathematics"
    )


def test_N_satisfies_no_komatsu_identity():
    # The hypothesis of Komatsu's theorem fails for N, spelled out: for every n,
    # 2ⁿ != 2^(2n). This is *why* the search above must come back empty, and it is
    # the same fact Wehrung notes on p. 3 about Z.
    for n in range(1, 12):
        assert 2**n != 2 ** (2 * n)
