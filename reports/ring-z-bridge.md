# The ring bridge: the full ring of integers inside Peano arithmetic

Scope: the tooling `cold_start/combination.py` + `peano_proofs.ring_kit` and
the artifact `ring_z_interpretation()` in `cold_start/ring_z.py`. Everything
labeled **checked** re-derived through `checker.check` with empty hypotheses
and the exact stated conclusion; the artifact has **no open labels**.

## 1. The reach

The Grothendieck bridge (`reports/integers-bridge.md`) carried ℤ's abelian
group into PRESBURGER on pairs `(a, b)` meaning `a − b`. This wave carries
the whole COMMUTATIVE RING (`algebra.COMM_RING`: ten axioms) into PEANO on
the same pairs and the same defined equivalence `(a,b) ~ (c,d) := a+d = c+b`.
The two new symbols are the whole difficulty:

| source (COMM_RING) | target (PEANO, on pairs) |
|---|---|
| `1` | one above the diagonal, `c.1 = S(c.2)` |
| `x * y` | the difference product `(x₁y₁ + x₂y₂, x₁y₂ + x₂y₁)` |

— the product being exactly how `(a−b)(c−d)` expands when subtraction is
forbidden. 23 obligations: three equivalence laws, totality + respect for
five symbols, ten translated axioms. **All paid.**

## 2. The tooling leap

Two pieces, each a strict generalization of the group bridge's engine:

* **`peano_proofs.ring_kit`** — the addition kit plus the multiplication
  recursion axioms and their first-argument mirrors, both distribution laws
  read expansively, directed associativity, and *ordered* multiplicative
  commutativity/left-commutativity. Under it every term reaches a sorted
  right-nested sum of sorted monomials — a polynomial normal form — so
  `prove_eq` decides commutative-semiring identities in PEANO outright.
* **`combination.by_combination`** — linear combinations of equational
  hypotheses with TERM COEFFICIENTS: a hypothesis `L = R` may join the
  `Cong`-sum as `L·c = R·c`. With every coefficient `None` it is exactly the
  old cancellation recipe, so `integers.by_cancellation` was deleted and the
  group bridge migrated onto the general engine. The final cancellation
  instantiates `add_cancel_right` through a fresh-rename so the sequential
  `Inst` primitive acts simultaneously (goals whose sides are literally
  named `x`, `y`, `z` would otherwise be rewritten mid-substitution).

## 3. Why coefficients are the crossing

Respect for `·` is the statement that equal differences multiply. From
`a ~ a'` (that is, `a₁ + a'₂ = a'₁ + a₂`) nothing additive reaches
`ab ~ a'b'` — the hypothesis must be *multiplied through*:

    a ~ a'  scaled by  b₁ and b₂     (once plain, once flipped)
    b ~ b'  scaled by  a'₁ and a'₂   (once plain, once flipped)
    + the two graph hypotheses, one flipped

Six hypotheses, one combination, one cancellation: the goal's two sides
balance as multisets of twelve monomials, which `ring_kit`'s normal form
verifies. The same shape pays multiplicative associativity at degree 3
(`g₃` scaled by `z`'s components, `g₁` by `x`'s), both units (`g_one`
scaled by `x₁`, `x₂`), and both distributive laws. Multiplicative
commutativity needs no coefficients at all — the difference product is
literally symmetric, and the kit's ordered rules equate `x₁y₁` with `y₁x₁`.

## 4. The measurement

    bridge:  51 nodes      (the equivalence + five graph instances)
    toll:    876,035 proof nodes across all 23 obligations
    open:    ()            -- the bridge is COMPLETE

The largest toll in the ledger — multiplication is where arithmetic stops
being decidable, and the polynomial shuffles pay for it honestly. The
headline: **the commutative ring of the integers, negatives and all, is a
theorem-by-theorem paid interpretation into the arithmetic of the
naturals** — ℤ lives inside ℕ, checked.

## 5. Reproduce

    uv run pytest tests/test_ring_z.py tests/test_combination.py -q
    uv run python -m cold_start.ring_z     # the single-bridge report
    uv run python -m cold_start.ledger     # every bridge, one table
