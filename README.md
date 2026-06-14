# cold-start

Number theory from nothing. We build the proof checker *and* the mathematics —
nothing gets to call itself a theorem unless the kernel minted it.

This is an LCF-style proof kernel for first-order logic with equality, plus a
Peano-arithmetic layer on top, written in plain Python with no dependencies.
The point is that the trusted base is small enough to read in one sitting.

## The pieces

- **`kernel.py`** — the trusted core (~250 lines). Terms, formulas (`Eq`,
  `Implies`), and an opaque `Theorem` type. A `Theorem` is a sequent
  `hyps |- conclusion`. You cannot construct one directly — every inference
  rule is the only door, and `axiom` is the explicit trusted door for
  asserting new axioms. The kernel knows nothing about numbers.
- **`peano.py`** — the signature (zero, successor, `+`) and the Peano axioms,
  asserted through `kernel.axiom`. Induction is *derived* here as two
  modus-ponens steps against an induction-schema axiom, so the kernel stays
  theory-agnostic.
- **`proofs.py`** — worked proofs. Currently: `0 + n = n` by induction.
- **`test_kernel.py`** — the evidence. Covers each inference rule, the
  trust boundary (you can't forge a `Theorem`), computation (`2 + 1 = 3`),
  and the headline theorem.

## Design commitments (v0)

- **Free variables are implicitly universally quantified** (the Boyer–Moore
  instinct). This is what makes `instantiate` sound and lets us skip an
  explicit `forall` connective for the arithmetic we do here.
- **Sound by construction.** The only soundness-critical code is `kernel.py`
  plus whichever axioms `peano.py` feeds through `axiom`. Everything else is
  checked.
- **Minimal logic.** Just `Eq` and `Implies` for now — exactly enough to
  bootstrap addition and prove its left identity.

## Run it

```sh
python test_kernel.py     # standalone, no pytest needed
python proofs.py          # prints:  |- +(0, n) = n
```

## Roadmap / next holes to dig

- [ ] `Not` (and `0 != S(x)`, successor injectivity as usable axioms)
- [ ] Prove `n + 0 = 0 + n` → full commutativity of `+`, then associativity
- [ ] Define `*` and prove its laws; distributivity
- [ ] Ordering (`<=`), then divisibility and primality
- [ ] A pretty-printer for proofs (proof trees / step listings)
- [ ] Tactics layer (a *non-trusted* convenience layer that emits kernel calls)
- [ ] Explicit quantifiers, if/when we outgrow implicit-universal free vars
