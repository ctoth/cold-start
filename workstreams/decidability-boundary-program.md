# The Decidability Boundary Program - 2026-08-05

## Status and Authorization Boundary

Q has authorized this program in full ("I want to do all of this, everything we
said here. all of it!"). Milestones should still land one at a time, each
through the normal gate (pytest, Ruff, Pyright, Lean compile), each with its
ledger entry where applicable. Nothing here suspends the repo's standing
disciplines: the De Bruijn split, exact-type validation, no trusted-core
imports of untrusted code, and `notes-breakthrough*` staying uncommitted.

## Execution Ledger

### 2026-08-05 — A1/B1 campaign opened

- Branch: `feat/decidability-a1-b1` from `cf09e99`.
- Baseline gate: 1,327 tests passed; Ruff clean; Pyright 0 errors/0 warnings;
  the generated Lean corpus compiled in the test suite.
- Baseline artifact ledger: seven artifacts reverified; Robinson formula (2)
  remains honestly open at `totality:*` and `uniqueness:*` on its literal
  empty-theory shore.
- A1 status: **complete** in `e6f4403`. `lean/models.py` now owns
  complete exact-identity registrations for PRESBURGER-at-`Nat` and
  PEANO-at-`Nat`. Registrations cover every operation, axiom, and induction;
  structurally equal or unregistered theories remain conditional. The corpus
  no longer carries per-entry `at_nat` permission bits. Red proof: the focused
  test initially failed because the model owner did not exist. Green proof:
  46 focused Lean/model tests and the full 1,330-test gate passed; Ruff and
  Pyright are clean; the generated corpus compiled, including the negative
  corrupted-proof control.
- B1 status: **complete**.
  `SQUARE_ARITHMETIC` extends PRESBURGER with the two addition-only square
  recursions. The 14-node subtraction-free multiplication graph has both debts
  paid: totality toll 15,186; uniqueness toll 5,044; total 20,230; open `()`.
  A proof-tree audit admits only `0`, `S`, `+`, and `sq`, while bounded standard
  semantics checks the graph exactly against `z=x*y`. The exact Lean model maps
  `sq(n)` to `Nat.mul n n`; focused foreign-kernel replay is green. Canonical
  bridge names also exposed and regressed a double-quoting defect in the Lean
  exporter before promotion. Final gate: 1,337 tests passed; Ruff clean;
  Pyright 0 errors/0 warnings; generated Lean compile and corrupted-proof
  negative control both passed. The eight-artifact ledger reverified the same
  14/20,230 measurement with both B1 obligations paid.

## The Program in One Paragraph

The cliff — (ℕ, +) decidable, (ℕ, ×) decidable, (ℕ, +, ×) undecidable — is
actually a finely mapped coastline of intermediate structures. Every landmark
on it is either a decision procedure or a definability result. This repo's
unique instruments (interpretations as checked artifacts, tolls as measured
proof cost, the ledger of paid and open obligations) can turn *both* kinds of
landmark into computational objects. The goal: be the first to put a price
sheet on the +/× entanglement, and get the Lean/Mathlib boundary working in
both directions so every measurement cashes out as an unconditional theorem
about actual ℕ.

## Track A — Mathlib, both directions

1. **Cash-out (A1).** Generalize the existing Lean-core `Nat` epilogue into a
   fail-closed registry of semantic model instantiations. PRESBURGER and PEANO
   cash out at `Nat`; positive, quotient, group, ring, and deliberately empty
   theories require their own carriers/domains or remain conditional. Every
   exported theorem with a registered model then discharges into an
   unconditional theorem about that actual carrier. Mathlib integration may
   add lemmas, but model registration — not an import — is the semantic event.
2. **Oracle (A2).** A hammer: shell out to Lean+Mathlib as an *untrusted*
   prover backend, reconstruct answers as cold-start proof terms the checker
   verifies. Start dumb: use `omega` on linear goals and rebuild from its
   certificate. Mathlib becomes a lemma mine, never a trusted dependency —
   fully consonant with the De Bruijn split.

## Track B — Seeds of undecidability, as bridges

Each classical "× becomes definable" result is an interpretation, i.e. this
repo's native artifact, with a measurable toll.

1. **The squaring seed (B1).** Use the subtraction-free multiplication graph
   `2z + x² + y² = (x+y)²`, so `(ℕ, +, x²)` defines `z=xy` without smuggling
   subtraction into the language. Register an honest addition-plus-square
   target theory, pay the graph's totality and uniqueness, and measure the
   resulting bridge. `ring_kit` + `by_combination` should make this a short
   campaign. First flag to plant.
2. **Divisibility (B2).** Julia Robinson's + and × from S and | — already in
   flight (`divisibility_bridges.py`, formula (2), two open debts: totality
   and uniqueness). Pay them or characterize them precisely.
3. **Coprimality (B3).** Woods's recovery of × from + and ⊥, sitting next to
   the open Erdős–Woods conjecture. Research-grade; expect partial bridges
   with honestly ledgered debts.
4. **The Villemaire jewel (B4).** (ℕ, +, V₂) decidable, (ℕ, +, V₃) decidable,
   (ℕ, +, V₂, V₃) undecidable. Two digit-worlds, each tame beside addition,
   entangled with *each other*. Cobham–Semënov territory: the purest specimen
   of the phenomenon. Long-range target; requires Track C instruments first.

## Track C — Decision procedures that emit proof terms

1. **Certifying Cooper (C1).** Presburger quantifier elimination emitting
   cold-start proof terms. Prior art exists (Coq/Isabelle) — table stakes,
   and it makes the decidable side of every future measurement free.
2. **Certifying Skolem arithmetic (C2).** The automata-over-prime-exponent
   argument, emitting proof terms. To our knowledge this exists nowhere.
   A publishable instrument on its own.
3. **Büchi arithmetic (C3).** Formalize V₂ as a theory; land its decidability
   as a procedure. Prerequisite for pricing B4.

## Track D — Toll spectroscopy

Define a mixing measure on statements (alternation depth between additive and
multiplicative vocabulary). Plot proof toll against it. Existing data points:
Skolem bridge 116,358; ring-ℤ 876,035; integers 155,545; divisibility's two
unpaid debts. Question the curve answers: is the cost blowup smooth, or is
there a phase transition — and where do the classical seeds (B1–B4) sit on it?
Nobody has ever plotted this, because nobody has had interpretations as
measured artifacts before.

## Track E — Hardening (carried over from the "serious" discussion)

1. Written spec of the Hamblin wire format and checker semantics, precise
   enough for an independent implementation.
2. Second, independent checker (Rust) built from the spec alone — two
   independent checkers agreeing on the same bytes, plus the throughput the
   million-node tolls will demand.
3. Soundness of the proof-term language stated and proved in Lean (leaning on
   A1's model instantiation).

## Order of Battle

A1 → B1 → C1 → (B2 debts ∥ E1) → C2 → A2 → E2 → C3 → B4 → D synthesis → paper
(CPP/ITP/CICM), with B3 opportunistic throughout. Each milestone is a normal
campaign: branch, measure, ledger, gate.

## The Pony

Delivered, as contracted:

```text
                        ,~~.
       (\   _          (  6 )-_,
        \\  \\____      \_ (\_/)\
         \\ /     `-. _  ` \   / |
          \\|         `\ \   | | |
            \  0  0     \ )  / / |
            |    ==      |/ / /  |
             \   --     /  / /   `
              `-.____.-'  ( (
                 | | |     \ \
                 | | |      ) )
                (__|__)    (__)
```

Her name is Presburgirl. She is decidable, provided you never ask her to
multiply.
