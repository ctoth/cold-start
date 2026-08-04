# Formula (2) bridge debts: decomposition, payments, and the honest ledger

Scope: the two open obligations of `robinson_product_interpretation()` in
`cold_start/divisibility_bridges.py` — `totality:*` and `uniqueness:*` of the
331-node graph transcribing Robinson (1949), Theorem 1.2, formula (2)
(pp. 101–102). Everything below labeled **checked** went through
`checker.check` (empty hypotheses, exact conclusion) and is committed;
everything labeled **conjectured** or **open** did not, and no such claim is a
theorem of this repo.

## 1. The ledger itself is the first finding

**As currently ledgered, neither debt is payable — by soundness, not by lack
of effort.** The artifact's target theory is
`PURE_SUCCESSOR_DIVISIBILITY = Theory(axioms=frozenset())`. A payment would be
a proof of `∃c Φ(x!0,x!1,c)` (resp. uniqueness) from **no axioms**, i.e. a
validity of first-order logic over the signature `(S, |)`. It is not one:

* *Uniqueness countermodel*: any two-element structure where `|` is the total
  relation. Every `coprime`/`lcm`/`unit_case` component of Φ becomes trivially
  true, so Φ(a,b,c) holds for **every** c, and two distinct elements exist.
* Totality also fails in easy finite models once `|` is tuned (e.g. empty `|`
  kills the modulus hypothesis but a two-point order breaks the unit case).

This is the intended honesty of `interp.py` — "an unpaid obligation is
REPORTED, never hidden" — but it means the path to payment necessarily changes
the artifact, in one of two ways:

* **(a) enrich the target theory** with a true theory of `(ℕ⁺, S, |)` strong
  enough to carry Robinson's argument. She reasons in the *standard model*;
  the axioms needed (essentially: divisibility lattice laws, primes, CRT,
  unboundedness) would be a research task of their own to state minimally.
* **(b) compose into PEANO**: read `a|b` as `∃k. a·k = b`
  (`divisibility.peano_divides`, already the paid predicate of
  `divisibility_into_peano()`), and prove the composed obligations as PEANO
  theorems. This is the recommended path — PEANO has induction, and the whole
  existing kit (poly_kit, cancellation, the seven divisibility laws) lives
  there.

**Second finding: on path (b) the composed obligations MUST be relativized to
the positive domain.** Verified in the standard model (not mechanised):
`coprime(0,x)` forces `x = 1`; `lcm(0,1) = 0` forces `m | S(0)`, i.e. `m = 1`;
the general disjunct of Φ(0,0,c) then reduces to `∃u. S(u) = c`. Hence
**Φ(0,0,c) holds for every c ≥ 1**: Φ(0,0,1) and Φ(0,0,2) are both true, so
unrelativized uniqueness is FALSE in N-with-zero and (by soundness) unprovable
in PEANO. This is the same phenomenon as A5''s positivity guard
(`robinson_proofs.py`), one storey higher. `interp.py` already supports
`domain=`; the right artifact is a relativized interpretation with
`δ(t) := ∃k. t = S(k)`, target PEANO, `|` ↦ `peano_divides`. Robinson's own
domain is ℕ⁺ — the transcription only becomes her theorem under that guard.

To make the composed shore first-class, the `robinson_divisibility`
constructors now take a `via=` divisibility builder (commit 7c8e22b);
`robinson_product(a, b, c, via=peano_divides)` is the exact formula the
composed obligations quantify.

## 2. The lemma DAG

Notation: `pd(a,b)` = `∃k. a·k = b`; Φ⁺ = formula (2) with `via=peano_divides`
relativized to positives. All formulas below are at that shore.

### Totality⁺: `∀a,b>0 ∃c>0 Φ⁺(a,b,c)` — witness `c := a·b`

```
TOTALITY (open)
├─ T1  Φ(a,b,ab) via the general disjunct (covers a=b=1 too)
│   ├─ T2  coprime-lcm-product: a⊥x → lcm-graph(a, x, a·x)        [HARD: H1]
│   │   ├─ ← direction: ax|u → a|u ∧ x|u
│   │   │     = PRODUCT_DIVIDES_BOTH                               [PAID]
│   │   └─ → direction: a|u ∧ x|u ∧ a⊥x → ax|u  (Euclid's lemma)   [OPEN: H1]
│   ├─ T3  congruence step: m|S(ax) ∧ m|S(by) → ∃u m|u ∧ S(u)=abxy
│   │   ├─ T3a CRT_KEY_IDENTITY:
│   │   │     mk=S(ax) → ml=S(by) → abxy+(mk+ml) = S(mk·ml)        [PAID]
│   │   ├─ T3b divides_add / divides_add_cancel / divides_step
│   │   │     (| is a congruence for +, both directions)           [PAID]
│   │   └─ T3c assembly: extract u with m·u' + 1 = abxy from T3a
│   │         via T3b (remaining bookkeeping: m=1 vs m≥2 is NOT
│   │         needed under the additive spelling)                  [OPEN, payable]
│   ├─ T4  instantiation plumbing: unfold Φ's ∀x,y,m, ExistsIntro u [OPEN, payable]
│   └─ leaves already paid: COPRIME_ONE_*, LCM_ONE_*, LCM_SELF,
│       UNIT_CASE_UNIT, totality point at (1,1)                    [PAID]
```

### Uniqueness⁺: `Φ⁺(a,b,c) ∧ Φ⁺(a,b,d) → c = d` — via `Φ⁺(a,b,c) → c = ab`

```
UNIQUENESS (open)
├─ U0  unit branch: unit_case(a,b,c) → a=b=c=1
│   ├─ UNIT_CASE_FORCES_UNIT_DIVISORS: → a|1 ∧ b|1 ∧ c|1           [PAID]
│   └─ divides_one: a|1 → a=1                                      [OPEN, payable next]
├─ U1  choose admissible x,y (coprime to a,b,c and each other)     [OPEN: H1/H3]
├─ U2  arbitrarily large admissible m: solve by ≡ −1 (mod S(ax))
│      — linear congruence solvability, i.e. Bézout                [OPEN: H3]
├─ U3  bounding: m | n ∧ 0 < n < m → ⊥ — needs an order kit
│      (≤ as ∃w. x+w=y, monotonicity, discreteness)                [OPEN: H2]
└─ U4  antisymmetry / lcm-graph functionality: lcm(a,b,c₁) ∧
       lcm(a,b,c₂) → c₁=c₂, via c₁|c₂ ∧ c₂|c₁ → c₁=c₂
       — needs divides_antisym → mul_eq_one → divides_one chain    [OPEN, payable]
```

### The three load-bearing hard parts

* **H1 — Euclid's lemma / coprime ⇒ lcm = product.** Consumed by totality (T2)
  and uniqueness (U1). Needs gcd reasoning: either Bézout by Euclidean descent
  (strong induction on remainders — expressible with the existing `Induct`
  plus an order kit) or prime factorization (worse).
* **H2 — an order kit.** `≤` as `∃w. x+w=y` with monotonicity, totality of the
  order, and `m|n ∧ 0<n<m → n=0`-style discreteness. Independent of H1 and
  reusable; a natural next wave on its own.
* **H3 — linear congruence solvability** (uniqueness only): given `gcd(b,m)=1`
  produce y with `by ≡ −1 (mod m)`. Follows from H1+H2 (Bézout), not separate
  mathematics.

**None of this is β-function/sequence-coding grade.** Every open node is
bounded elementary number theory: quantifier plumbing, Bézout, and order. The
open obligations never need to encode sequences — Robinson's formula does that
job itself. Full payment of totality⁺ is a realistic (multi-wave) target;
uniqueness⁺ is substantially heavier because H2 and H3 sit on its critical
path, but it is not blocked on anything foundationally missing.

## 3. What was landed this wave (all checker-verified, hypothesis-free)

Infrastructure:

| Commit | What |
|---|---|
| 7a56430 | `prop.or_left` / `or_right` / `or_elim` — disjunction kit (case analysis via one reductio) |
| 7c8e22b | `via=` divisibility builder on every `robinson_divisibility` constructor; `robinson_product(a,b,c, via=peano_divides)` is now a first-class formula (tested: no `Rel` left, only `S`/`*`) |

Checked theorems (sequent ⊢ shown with implicit-universal free variables;
`pd(a,b) = ∃k. a·k = b`; sizes are proof-term node counts):

| Theorem | Sequent | Theory | Nodes | Commit |
|---|---|---|---|---|
| `zero_or_succ` | ⊢ n=0 ∨ ∃m. n=S(m) | PRESBURGER | 63 | 66d014b |
| `add_eq_zero` | ⊢ x+y=0 → x=0 ∧ y=0 | PRESBURGER | 248 | 693ba3e |
| `divides_add` | ⊢ pd(a,b) → pd(a,c) → pd(a,b+c) | PEANO | 1,845 | c1dd166 |
| `divides_mul_left` | ⊢ pd(a,b) → pd(c·a, c·b) | PEANO | 2,590 | c1dd166 |
| `divides_step` | ⊢ a·k = b+a → pd(a,b) | PEANO | 681 | 693ba3e |
| `divides_add_cancel` | ⊢ pd(a, b+a·c) → pd(a,b) | PEANO | 1,073 | 693ba3e |
| `coprime_one_left` | ⊢ coprime⁽ᵖᵈ⁾(1, a) | PEANO | 5,027 | 45531e2 |
| `coprime_one_right` | ⊢ coprime⁽ᵖᵈ⁾(a, 1) | PEANO | 5,008 | 45531e2 |
| `lcm_one_left` | ⊢ lcm-graph⁽ᵖᵈ⁾(1, a, a) | PEANO | 2,546 | 45531e2 |
| `lcm_one_right` | ⊢ lcm-graph⁽ᵖᵈ⁾(a, 1, a) | PEANO | 2,563 | 45531e2 |
| `lcm_self` | ⊢ lcm-graph⁽ᵖᵈ⁾(a, a, a) | PEANO | 239 | 45531e2 |
| `unit_case_unit` | ⊢ unit-case⁽ᵖᵈ⁾(1, 1, 1) | PEANO | 7,067 | 45531e2 |
| `unit_case_forces_unit_divisors` | ⊢ unit-case⁽ᵖᵈ⁾(a,b,c) → pd(a,1) ∧ pd(b,1) ∧ pd(c,1) | PEANO | 63 | 45531e2 |
| `product_divides_both` | ⊢ pd(a·b, c) → pd(a,c) ∧ pd(b,c) | PEANO | 7,520 | 45531e2 |
| `crt_key_identity` | ⊢ m·k=S(a·x) → m·l=S(b·y) → (a·b)·(x·y) + (m·k + m·l) = S((m·k)·(m·l)) | PEANO | 16,400 | 45531e2 |
| `totality_witness_at_unit` | ⊢ ∃c. Φ⁽ᵖᵈ⁾(1, 1, c) | PEANO | 8,061 | 45531e2 |

`crt_key_identity` is the subtraction-free spelling of Robinson's central
congruence (`ax ≡ −1 ∧ by ≡ −1 ⇒ abxy ≡ 1 (mod m)`); `divides_add_cancel` is
the extraction step that turns it into `m | abxy − 1`. Together they close
T3 up to assembly. `totality_witness_at_unit` is one checked *point* of the
totality graph — a point, not the debt.

Gate at the tip: `1237 passed`, ruff clean, pyright `0 errors` on all touched
files. Every theorem above re-derives from inert proof terms through the
trusted `check` in the tests
(`tests/test_prop.py`, `tests/test_presburger.py`,
`tests/test_divisibility_proofs.py`, `tests/test_robinson_divisibility.py`,
`tests/test_robinson_divisibility_proofs.py`).

## 4. What remains, in dependency order

1. **`divides_one`** (`a|1 → a=1`): case split on the witness plus
   `mul_eq_one`; payable with the now-landed `zero_or_succ`/`or_elim`/
   `add_eq_zero` plumbing. Unlocks U0 and antisymmetry.
2. **`divides_antisym`** (`a|b ∧ b|a → a=b`) and lcm-graph functionality (U4).
3. **T3c/T4 assembly** of the general disjunct at `c := ab` — pure plumbing
   over paid leaves, but large (the formula's ∀x,y,m block must be opened and
   each of seven conjuncts consumed).
4. **The order kit (H2)** — self-contained, reusable, no new ideas needed.
5. **Bézout / Euclid (H1)** — the one genuinely hard proof. Euclidean descent
   under `Induct` with the order kit. Everything else in totality⁺ waits on it
   only at T2's forward direction.
6. **Relativized artifact**: once (1)–(5) exist, restate
   `robinson_product_interpretation` with `domain=δ`, target PEANO, and pay
   `totality:*` there. `uniqueness:*` additionally needs H3 and the U1–U3
   choice argument.

## 5. Path recommendation

Pursue **path (b), relativized**: compose into PEANO via `peano_divides`,
δ = positivity. Do not attempt path (a) (axiomatizing `(ℕ⁺,S,|)`) — it
duplicates the number theory anyway and adds an axiom-honesty problem the
PEANO shore doesn't have. Keep the current empty-target ledger entry exactly
as is: it is the truthful record that the *uninterpreted* bridge proves
nothing, which is the De Bruijn-criterion posture of this repo.

Realistic assessment: **totality⁺ is reachable without any sequence-coding
machinery** — the remaining mathematics is Euclid's lemma plus plumbing, and
this wave verified that the checker and tactics handle every proof shape
involved (nested case splits, existential witnesses under congruence
reasoning, 16k-node polynomial identities). **Uniqueness⁺ is also
coding-free but is at least two waves out** (order kit, then Bézout, then the
arbitrarily-large-modulus argument). Nothing found this wave suggests the
debts are unpayable on the composed shore; what is unpayable is the ledger's
literal empty-theory reading, and that is now documented rather than
discovered later.
