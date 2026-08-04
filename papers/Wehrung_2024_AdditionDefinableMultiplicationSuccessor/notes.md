---
title: "Is addition definable from multiplication and successor?"
authors: "Friedrich Wehrung"
year: 2024
venue: "arXiv:2405.08364v3 [math.RA]; Forum Mathematicum"
doi_url: "https://doi.org/10.1515/forum-2024-0245"
---

# Is addition definable from multiplication and successor? (Friedrich Wehrung, 2024)

Read from the page images of pp. 1–5 (the PDF is owner-password protected; `qpdf
--decrypt` + `magick` rendered it). These notes record what the ring-theoretic
version of Robinson's question looks like, and what it says about the bridge in
`cold_start/robinson.py`.

## The one-sentence question
**Is the addition of an associative unital ring determined by its multiplication
together with the successor function `x ↦ 1 + x`?** Wehrung's opening line (§1,
p. 2): "the general question remains open."

## The definitions (verbatim, pp. 2–5)

**§1.1 "The problem" (p. 2).** A map `f: R → S` between (associative, unital, but
not necessarily commutative) rings is a ***brachymorphism*** if
$$f(1+x) = 1 + f(x) \qquad\text{and}\qquad f(xy) = f(x)f(y)\quad\text{for all } x,y \in R.$$
(Footnote 1: "The prefix *brachy*, from the ancient Greek *brakhýs*, means
'short'.") From `f(x)f(0) = f(x0) = f(0)` he derives `f(0) = 0` and `f(1) = 1`.
**The open question: is every brachymorphism additive** (hence a ring
homomorphism)? It "remains a mystery to the author. A positive solution to that
problem would probably destroy the present paper."

`R` is called ***addable*** (Definition 3.1, p. 4) if every brachymorphism with
domain `R` is additive. Known-positive classes (Abstract, p. 1): `R` finite or
left/right Artinian; any ring of `2×2` matrices over a commutative ring; `R`
Engelian; every element a sum of `π`-regular and central elements (so `π`-regular
rings, Banach algebras, power series rings); full matrix rings of order `> 1`
over any ring; monoid rings `K[M]` with `M` `π`-regular; the Weyl algebra
`A₁(K)` in positive characteristic; plus two results about specific maps — the
power function `x ↦ xⁿ` and the determinant on `n×n` matrices, `n ≥ 3`.

**Proposition 2.1 (p. 4) — "addition on a slide rule."** *Let `R` be a division
ring and let `S` be a unital ring. Then every brachymorphism `f: R → S` is
additive.* Proof in three lines: for `x ≠ 0`, `zx⁻¹ = 1 + yx⁻¹` where `z = x+y`,
so `f(z)f(x)⁻¹ = 1 + f(y)f(x)⁻¹`, whence `f(z) = f(x) + f(y)`. The section is
literally titled **"The case of division rings: addition on a slide rule"** —
Wehrung notes it "showcases the method, familiar to math students from the
pre-calculator era, for adding numbers on a slide rule: namely, apply the formula
$$x + y = (1 + yx^{-1})x.$$
A number of our 'brachymorphism ⇒ additive' results will be established by
refinements of that argument."

**Definition 3.2 (p. 5) — *brachynomials*.** Every `S`-term (signature
`S = (′, ·, 0)`, with `′` interpreted as `x ↦ 1 + x`) has an associated
`R`-polynomial `t̃`; polynomials of that form are the **brachynomials**. Example
given: `x + xy = x(1+y)` *is* a brachynomial (it is `t̃` for `t = xy′`), but
`x + y` is not.

**Lemma 3.4 (p. 5).** A tuple is *summable* iff there is a **positive
existential** (indeed positive primitive) `S`-formula `E` with `Ẽ(x⃗) ⇒ x_{n+1} =
x₁+⋯+x_n` valid in every ring and `Ẽ(a₁,…,a_n, a₁+⋯+a_n)` true in `R`. This is
the sense in which the paper's question "amounts to studying the *positive
primitive definability* of addition from multiplication and successor" (§1, p. 2).

## Komatsu's characterization (p. 3) — the equational answer is bounded
Wehrung's survey of the equational tradition (Foster; Yaqub on `ℤ/nℤ`; Moore and
Yaqub; Abu-Khuzam, Tominaga and Yaqub; Putcha and Yaqub) ends at:

> "Finally, Komatsu [23] proves that *rings in which the addition is a
> composition of multiplication and the successor function are characterized by
> their satisfying a polynomial identity of the form `xⁿ = x^{n+1}p(x)`, and then
> the latter can be taken as `xⁿ = x^{2n}` for a suitable `n`.*"

The consequence Wehrung draws immediately (p. 3) is the one that matters here:
`ℤ` **satisfies no identity of the form `xⁿ = x^{2n}`**, so addition on `ℤ` is
*not* a brachynomial — yet every brachymorphism from `ℤ` is (trivially) additive.
"The distinction in play boils down to the meaning of *definable*": the
Komatsu-style works mean it "in the strongest possible sense (i.e.,
brachynomials), which leads to the description of addition *via quantifier-free
formulas*," whereas addability is a statement about *positive existential*
formulas — "a much wider class of rings ... in fact, so wide that we do not know
so far whether there is anything outside."

## Relation to this repo
- **Our `bridge` is relational, and that is not a weakness — it is forced.**
  `bridge(a,b,c)` in `cold_start/robinson.py` is a *formula* `S(a·c)·S(b·c) =
  S((c·c)·S(a·b))` whose solutions are the graph of `+`; it is not a *term*
  computing `a+b`. Komatsu's characterization (p. 3) says a term is impossible
  over `ℤ` (and over `ℕ`, which embeds in it): addition is a brachynomial only
  for rings satisfying `xⁿ = x^{2n}`, an identity failing in `ℤ` for every `n`.
  So Robinson's relational bridge is **best possible** — the quantifier-free
  version of her theorem does not exist, and the existential/relational one does.
  Wehrung's own framing agrees: definability of `+` here is *positive primitive*
  definability (Lemma 3.4), the same shape as `bridge`.
- **The degenerate base case is rigidity.** Wehrung's `f(1) = 1` and `f(1+x) =
  1 + f(x)` are exactly the successor-preserving, unit-fixing conditions; over
  the positive integers those two alone pin `f` down — every successor-preserving
  self-map of `ℤ⁺` fixing `1` is the identity, by induction. That is the
  one-line, zero-multiplication end of the same spectrum, and it is mechanised in
  this repo as `cold_start/rigidity.py`: `ROBINSON_PEANO` extended with `f(1) = 1`
  and `f(S x) = S(f x)` proves `|- f(x) = x` through the checker's `Induct` rule
  (base 1) — the first genuine induction proof in that theory. And once rigidity
  is available, the *second* brachymorphism law is a theorem rather than a
  hypothesis: `|- f(x·y) = f(x)·f(y)` follows by rewriting alone. Over `ℤ⁺`,
  successor-preservation forces multiplicativity, so `ℕ` is addable trivially —
  exactly the degenerate corner Wehrung sets aside. Wehrung's paper is what the question
  becomes once the model is a ring rich enough that induction no longer settles
  it.
- **Komatsu's line, witnessed by search.** `tests/test_brachynomial.py` brute-forces
  every term over `{1, S, ·}` in two variables and confirms both sides of the
  characterization on the nose. Where `xⁿ = x^{2n}` holds, the brachynomial exists
  and the search exhibits it:

      Z/2   (x = x², n = 1):   x + y = S(x·y) · S(S(x)·S(y))
      Z/3   (x² = x⁴, n = 2):  x + y = S(x·y) · S(S(S(x)·(S(y)·S(x·y))))

  and over `ℕ`, where no such identity holds, nothing computes `x + y` up to the
  size bound. The `Z/2` witness is Robinson's own bridge shape read at `c = 1` — a
  product of two successors of products — which is a pleasant accident. The finite
  cases are proofs; the `ℕ` case is an honest bounded witness of the theorem.
- **Where the difficulty lives.** In `papers/Robinson_1949_DefinabilityArithmetic/notes.md`
  we recorded that `(ℕ, ·)` alone is decidable because permuting the primes is a
  multiplicative automorphism, and that `S` *rigidifies*. Wehrung's
  brachymorphisms are precisely the maps that respect `·` and `S` but are not
  assumed to respect `+` — the ring-theoretic measure of exactly how much of that
  rigidity survives outside `ℕ`.

## Cross-references
- `papers/Robinson_1949_DefinabilityArithmetic/notes.md` — Theorem 1.1 there is the
  bridge `bridge(a,b,c)`; this paper is the same question ("is `+` definable from
  `·` and `S`?") asked for arbitrary unital rings instead of `ℕ`, and answered
  only partially.
- Robinson eliminates `+` from Peano's axioms using the bridge; Wehrung's §11
  ("Expanding the context", pp. 20–23) pushes the other way, into semirings,
  near-rings, and cancellative semirings — closer to `ℕ` again.

## Open follow-ups
- [ ] Record the exact Komatsu reference ([23] in the bibliography, p. 23) and
      check whether the `xⁿ = x^{2n}` characterization is stated for unital rings
      only — our "no term over `ℕ`" argument leans on it.
- [ ] Pages 6–23 not read: Corollary 3.6 (the positive-primitive-definability
      restatement), Corollary 7.9 (brachynomial addition ⇒ addable), and §11.3 on
      cancellative semirings are the parts most likely to bear on `ℕ`.
