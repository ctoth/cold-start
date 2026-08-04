---
title: "Definability and decision problems in arithmetic"
authors: "Julia Robinson"
year: 1949
venue: "Journal of Symbolic Logic, vol. 14, pp. 98–114"
doi_url: "https://doi.org/10.2307/2266510"
---

# Definability and decision problems in arithmetic (Julia Robinson, 1949)

Read in full from the page images (the PDF is owner-password protected; `qpdf
--decrypt` + `magick` rendered it). These notes record what `cold_start/robinson.py`
and `tests/test_robinson.py` are built from.

## The one-sentence result we use
**Addition is first-order definable from multiplication and successor.** Hence the
elementary theory of `(1, S, ·)` is as expressive as full arithmetic `(+, ·)` — and
just as undecidable.

## The constructions (verbatim, p. 99–103)

**Theorem 1.1 (p. 100).** For positive integers, `a + b = c` iff
$$S(a\cdot c)\cdot S(b\cdot c) = S\big((c\cdot c)\cdot S(a\cdot b)\big).$$
In ordinary notation `(1+ac)(1+bc) = 1 + c²(1+ab)`; multiplying out and cancelling
gives `(a+b)c = c²`, true (for `c > 0`) iff `a + b = c`. This is `bridge(a,b,c)` in
`robinson.py`, and `test_bridge_is_the_graph_of_addition` verifies it in the model N.

**Theorem 1.2 (p. 101–102).** `+` and `·` are both definable from `S` and
divisibility `|`, using coprimality `a ⊥ b` and lcm `a ○ b` (a Chinese-remainder
argument: `ax ≡ −1`, `by ≡ −1 (mod m)` ⟹ `abxy ≡ +1`). So `(ℕ, S, |)` alone
reconstructs all of arithmetic. (Not mechanised here — heavier and uses `|`.)

**§2, p. 103 — Peano with `+` eliminated.** Robinson takes Peano's axioms (`1, S, ·, +`)
and removes `+` via Theorem 1.1, leaving the signature `(1, S, ·)`:
```
A1   ¬(Sa = 1)          A2   Sa = Sb → a = b        A3   induction (a rule)
A4'  S(a·Sa)·S(1·Sa) = S([Sa·Sa]·Sa)                          # a + 1 = Sa
A5'  [S(a·c)·S(b·c) = S((c·c)·S(a·b))] →                      # a+b=c → a+Sb=Sc
       [S(a·Sc)·S(Sb·Sc) = S([Sc·Sc]·S(a·Sb))]
A6   a·1 = a            A7'  S[(a·b)·(a·Sb)]·S[a·(a·Sb)] = S([(a·Sb)·(a·Sb)]·S[(a·b)·a])
```
In `robinson.py` these are A4' = `bridge(a, 1, Sa)`, A5' = `bridge(a,b,c) → bridge(a, Sb, Sc)`,
A7' = `bridge(a·b, a, a·Sb)` — the recursion laws for `+`/`·` with their `+`s replaced
by bridges. `test_robinson_peano_axioms_true_in_N` confirms all are true in N.

## Why this matters (the honest design takeaway)
- The `+`/`×` **entanglement is unavoidable** — it is the content of arithmetic. The
  usual axiom `x·Sy = x·y + x` *hides* it inside one axiom (note the `+` on its RHS);
  the Robinson basis *exposes* it as the bridge, a derivable theorem.
- **Undecidability has a precise location:** `(ℕ, ·)` alone (Skolem arithmetic) is
  decidable, because any permutation of the primes is a multiplicative automorphism
  and that much symmetry hides addition (Robinson cites Padoa, p. 100). Successor
  **rigidifies** the integers — it fixes 1, 2 = S1, 3 = SS1, … — killing those
  automorphisms, and only then is `+` definable. So undecidability enters exactly
  when `S` meets `·`. **Mechanised** in `tests/test_padoa.py`: σ swaps the exponents
  of 2 and 3 (σ2=3, σ3=2, σ4=9, σ6=6, σp=p for p≥5), preserves `·` on a grid, and
  breaks `+` at 2+2=4 (σ2+σ2=6 ≠ 9=σ4) and `S` at σ(S1)=3 ≠ 2=S(σ1).
- **For a proof checker:** Robinson herself (§2) calls the eliminated-`+` axioms
  "complicated and artificial." We therefore keep `+`-primitive with recursive `×`
  (`cold_start.peano`) as the small, readable trusted base, and *exhibit* the
  Robinson `(1, S, ·)` basis (`cold_start.robinson`) with the bridge as a checked
  theorem — beauty on display, paid for in a derivation rather than ugly axioms.

## Testable properties (mechanised in tests/test_robinson.py)
- `bridge(a,b,c)` is true in N exactly when `a + b = c` (for `c > 0`).
- Every `(1, S, ·)` Peano axiom is true in N over the positive integers.
- `check(Inst(Axiom(A4'), "a", 2), ROBINSON_PEANO)` derives `bridge(2, 1, 3)` — a
  closed theorem with no `+` symbol, verified by the trusted checker.

## Testable properties (mechanised in tests/test_padoa.py — Padoa's method)
- σ is multiplicative and an involution: an automorphism of `(N⁺, ·)`.
- σ moves the graph of `+` (most of the sampled grid), and moves `S` at 1.
- The maximal `·`-only subterms of `bridge` (`a·c`, `b·c`, `c·c`, `a·b`) ARE
  σ-equivariant; the `S`-wrapped ones are not, and `bridge(2,2,4)` is true while
  `bridge(σ2,σ2,σ4) = bridge(3,3,9)` is false. The σ-variance enters through `S`.
- Honesty: these are *witnesses*. "Definable ⇒ automorphism-invariant" is a
  metatheorem we do not mechanise; the tests supply the automorphism half.

## The bridge as a PEANO theorem (`cold_start.robinson_proofs`)
The model checks above say the bridge *works*; this says it is *correct*, for every
pair of naturals at once:

    PEANO ⊢ S(a·(a+b)) · S(b·(a+b)) = S(((a+b)·(a+b)) · S(a·b))

At `c := a+b` the bridge is a pure semiring identity — both sides multiply out to
`ab(a+b)² + (a+b)² + 1` — so it needs no positivity and no case split, and `a = b = 0`
is covered like everything else. The proof is that identity's own reason: `poly_kit()`
floats every successor out, expands the products by distributivity, and AC-sorts the
resulting sum of monomials, so both sides reach one canonical polynomial and `prove_eq`
joins them there. It rests on the multiplication ladder in `cold_start.proofs`
(`0·n = 0`, `S(x)·y = x·y + y`, commutativity, distributivity both ways, associativity),
each rung proved by induction over the rungs below it.

**A4' and A7' are Peano theorems**, one rewrite each from an instance of the bridge
theorem: `PEANO ⊢ bridge(a, 1, S a)` and `PEANO ⊢ bridge(a·b, a, a·S b)`. The derived
sequent is the axiom formula on the nose, with no hypotheses.

**Unguarded A5' is not, and cannot be, a PEANO theorem.**
`bridge(a,b,c) → bridge(a, S b, S c)` is FALSE in the
standard model of PEANO: the bridge says `(a+b)·c = c²`, which pins `a + b = c` down
only where `c` can be cancelled, and 0 cannot. At `a = b = 1, c = 0` the hypothesis
holds vacuously while the conclusion demands `6 = 4`. By soundness there is no proof.
This is exactly the work Robinson's positive-integer domain does in §2 — and it locates
it precisely: two of her three recursion axioms are positivity-free, one is not.

**The missing positive case is now proved.** `cold_start.robinson_proofs` derives
`PEANO ⊢ bridge(a,b,S(c)) → a+b=S(c)`. Expansion and successor injectivity reduce
the bridge to `(a+b)S(c)=S(c)²`; a separately checked nested-induction theorem
derives `xS(c)=yS(c) → x=y`. Consequently A5' itself is a theorem under the exact
guard `c=S(k)`. Both the cancellation and converse proof terms are also rendered
into `lean_export/ColdStart.lean` and accepted by Lean 4's kernel.

## Open follow-ups
- [x] Both bridge directions as PEANO theorems on the positive domain, plus
      A4'/A7' outright and A5' with its exact positivity guard (unguarded A5'
      remains refuted at zero).
- [ ] Mechanise Theorem 1.2 (`+`, `·` from `S` and `|`) — needs a divisibility-based
  defined `·` and the coprimality/lcm definitions (p. 102).
- [x] A genuine *induction* proof in `ROBINSON_PEANO` (base 1): `cold_start/rigidity.py`
  derives `|- f(x) = x` from `f(1)=1`, `f(Sx)=S(fx)` via the induction rule
  (and `|- f(x·y) = f(x)·f(y)` from it) — Wehrung's brachymorphism laws over ℕ⁺.
- [x] The CONVERSE of the bridge theorem — `bridge(a,b,c) → a + b = c` for `c > 0` —
      derived through positive multiplication cancellation.
