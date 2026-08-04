# The Skolem bridge: Presburger inside multiplication alone

Scope: the artifact `skolem_interpretation()` in `cold_start/skolem.py` and
the parity kit in `cold_start/parity.py` that pays for it. Everything labeled
**checked** re-derived through `checker.check` with empty hypotheses and the
exact stated conclusion; everything labeled **open** did not, and is a ledger
entry, not a claim.

## 1. The reach

Skolem arithmetic is the first-order theory of the naturals with
multiplication only — no successor axioms doing additive work, no `+`.
Mostowski's classical observation: the additive world embeds in it, because
on the powers of two multiplication *is* addition of exponents. This wave
mechanizes that crossing as a checked interpretation:

| source (PRESBURGER) | target (PEANO, on the domain pow2) |
|---|---|
| `0` | `1` |
| `S(x)` | the graph `x·2 = c` |
| `x + y` | the graph `x·y = c` |

with the domain spoken entirely in divisibility (the paid predicate
`a|b := ∃k. a·k = b`):

    pow2(t)  :=  ∀d ( d|t → d ≠ 1 → 2|d )

"every divisor except 1 is even." No exponentiation exists anywhere in the
system, yet this carves out exactly {1, 2, 4, 8, …} — zero fails it because
3 divides 0. A bounded-model test pins the semantics below 16.

## 2. The measurement

    bridge:  16 nodes    (three graph instances)
    toll:    116,358 proof nodes across all eleven obligations
    open:    ()          -- the bridge is COMPLETE

First landing (same wave, before the order kit): ten of eleven paid at toll
64,281 with `totality:+` open. The completion below is the second landing.

Paid, all checked in PEANO through the graph translator's exact output
(hoisted ∀-guards, δ-relativization of free variables and hoisted
quantifiers):

* `axiom: x+0 = x` — lands on `x·1 = x`.
* `axiom: x+S(y) = S(x+y)` — lands on associativity: `x·(y·2) = (x·y)·2`.
* `axiom: S(x) ≠ 0` — lands on "no doubling reaches 1": `x·2 = 1` makes 2 a
  unit, so `2 = 1`, refuted by successor axioms via `divides_one`.
* `axiom: S(x)=S(y) → x=y` — doubling is injective *on the domain*: the
  hoisted guard is instantiated at `y·2`, admissible exactly because the
  closure theorem `pow2_double` holds; then cancellation by 2 finishes.
* `totality:0`, `uniqueness:0/S/+` — the graphs are equations, so uniqueness
  is transitivity; `1` is in the domain vacuously.
* `totality:S` — **closure of the powers of two under doubling**, the
  mathematical heart (below).
* `totality:+` — **closure under products**, by strong-induction descent
  (section 4).
* `domain:nonempty` — witness 1.

## 3. The toll's engine: Euclid's lemma at the prime 2

`cold_start/parity.py`, all checked in PEANO:

| Theorem | Statement | Method |
|---|---|---|
| `PARITY` | `n = m·2 ∨ n = S(m·2)` | induction on `n` |
| `EVEN_NE_ODD` | `¬(a·2 = S(b·2))` | induction on `b` with a ∀-strengthened predicate; `zero_or_succ` splits `a` |
| `CANCEL_TWO` | `a·2 = b·2 → a = b` | `mul_cancel_right_succ` at `z := 1` |
| `EUCLID_TWO` | `¬(2|d) → d|x·2 → d|x` | double parity split, no order, no Bézout |

`EUCLID_TWO` is the repository's first instance of Euclid's lemma, and the
proof is notable for what it does *not* need: from the witness `d·k = x·2`,
an even `k` cancels the 2 directly, and an odd `k` with an odd `d` makes
`d·k` odd — an odd number equal to the even `x·2`, killed by `EVEN_NE_ODD`.
Parity alone carries the prime 2. This is the first paid rung of **H1** in
`reports/formula2-bridge-debts.md` (Euclid's lemma is the load-bearing hard
part of Robinson's totality⁺ debt); the general lemma still needs Bézout,
but the p = 2 case needed only this.

Closure under doubling is then a reductio: an odd divisor `d ≠ 1` of `x·2`
drops through `EUCLID_TWO` to a divisor of `x`, where `pow2(x)` pronounces
it even. That single theorem (`pow2_double`) pays `totality:S` *and*
unlocks the translated successor injectivity — the payment exists only
because doubling stays inside the domain, which is the relativization
earning its keep.

## 4. The last debt, paid: the order kit and dyadic descent

`totality:+` — a product of powers of two is a power of two — needed what
`Induct` alone cannot do: descend. The order kit (`cold_start/order.py`)
supplies it, trusting nothing new:

* `le(a,b) := ∃w. a+w = b` — order defined by addition;
* `le_zero`, `le_succ_split` (discreteness), `le_double`, and `pos_half_le`
  (`a = S(m) → a·2 = S(n) → a ≤ n` — the descent step);
* `tactics.transport` — Leibniz's law as a combinator, rewriting a whole
  formula along a proved equality (Cong/Trans at equations, antecedent
  re-introduction at implications, open–move–close at binders);
* `course_of_values` — **strong induction compiled to structural `Induct`**
  through `reach(n) := ∀z (z ≤ n → P(z))`.

`pow2_mul` (checked, the payment's engine) then descends: an odd divisor
`d ≠ 1` of `S(n)·y` is refuted because `S(n)` is even by its own domain
membership (`S(n) = h·2`), the half sits at `h ≤ n` (`pos_half_le`) and is
itself a power of two (`transport` + `pow2_half`), and Euclid's lemma at 2
drops `d` one dyadic layer to a divisor of `h·y` — where the reach
hypothesis pronounces it even. `not_pow2_zero` (odd witness 3) anchors the
base. The formula (2) ledger's H2 item is made of exactly these order-kit
pieces; that frontier is now stocked, not just named.

## 5. Reproduce

    uv run pytest tests/test_parity.py tests/test_order.py tests/test_skolem.py -q
    uv run python -m cold_start.skolem     # the single-bridge report
    uv run python -m cold_start.ledger     # every bridge, one table
