# Formula (2) bridge debts — working notes (agent: divisibility-bridge wave)

Worktree: `.claude/worktrees/agent-a38bd5b3ad1cb886b`, branch tip 4a49306. Baseline gate: `1220 passed in 126.21s`.

## Key findings so far (decomposition, deliverable 1)

1. **The ledgered debts are unpayable as stated.** `robinson_product_interpretation()`
   targets `PURE_SUCCESSOR_DIVISIBILITY = Theory(axioms=frozenset())` — the EMPTY
   theory. `totality:*` / `uniqueness:*` would have to be validities of pure FOL over
   (S, |). Countermodel for uniqueness: a 2-element structure where `|` is the total
   relation — `unit_case` holds of everything, so Φ(a,b,c) holds for every c, and
   c ≠ d exists. So by soundness no payment can exist. The debts are honest ledger
   entries, but payment requires *changing the artifact* (richer target theory, or
   composition into PEANO), not just proof labor.

2. **Even composed into PEANO (| ↦ peano_divides), the UNRELATIVIZED obligations
   break at zero.** Computed in the standard model: coprime(0,x) ⇔ x=1; lcm(0,1)=0
   forces m=1 in the modulus hypothesis; the general disjunct of Φ(0,0,c) then
   reduces to ∃u S(u) = c. Hence Φ(0,0,c) holds iff c ≥ 1: **Φ(0,0,1) and Φ(0,0,2)
   both true** — uniqueness is FALSE in N-with-0. Robinson's domain is ℕ⁺; the right
   artifact is a *relativized* interpretation (interp.py already supports `domain`)
   with δ(t) := ∃k t = S(k), target PEANO, predicate | ↦ peano_divides.

3. **Load-bearing hard parts** (neither payable this wave):
   - H1 (both debts): coprime a x → lcm(a,x) = a·x, i.e. a|u ∧ x|u ∧ a⊥x → ax|u.
     Euclid/Bézout-grade. No sequence coding needed, but needs gcd machinery or
     Bézout by descent.
   - H2 (uniqueness): order kit (≤ via ∃w x+w=y; m|n ∧ 0<n<m → ⊥) + arbitrarily
     large admissible moduli (solve by ≡ −1 mod S(ax): linear congruence
     solvability = Bézout again) — Robinson pp. 101–102 argument.
   - NOT β-function grade: all of it is bounded number theory.

4. **Payable leaves identified** (current machinery: poly_kit, cancellation,
   divisibility laws, prop kit, quantifier rules):
   - or_left / or_right / or_elim prop combinators (in progress now)
   - divides_add: a|b → a|c → a|(b+c)  (witness k+l, distrib)
   - divides_mul_left: a|b → c·a|c·b  (witness k, assoc)
   - zero_or_succ: n=0 ∨ ∃m n=S m (induction; base or_left+Refl, step or_right+ExistsIntro)
   - PEANO-side Φ components via a `via=peano_divides` parameter added to
     robinson_divisibility constructors (de Bruijn abstraction makes this hygienic):
     coprime(1,a), coprime(a,1) (divides_trans through 1), lcm(a,1,a), lcm(1,a,a),
     lcm(a,a,a) (prop kit + one_divides), unit_case(1,1,1), unit_case → instance-at-1
     forcing (ForallElim at ONE), product-divides-both: ab|u → a|u ∧ b|u,
     CRT key identity: mk=S(ax) → ml=S(by) → abxy + (mk+ml) = S((mk)(ml))
     (poly_kit + hypothesis rules, budget ~400),
     totality INSTANCE at (1,1): ∃c Φ_PEANO(1,1,c) via unit disjunct, witness 1.
   - Stretch: divides_add_cancel (a | b+a·c → a|b, induction on c + case split via
     zero_or_succ/or_elim); divides_one (a|1 → a=1); divides_antisym. These are the
     next rungs for T3/T4 but each needs the classical case-split plumbing.

## Progress log
- 9e57a12 divides_one landed (a|1 → a=1, 811 nodes, PEANO-checked:
  `|- ((exists. *(a, #0) = S(0)) -> a = S(0))`), `15 passed`
  test_divisibility_proofs.py, ruff+pyright clean. U0 unit branch now
  fully paid (with unit_case_forces_unit_divisors).
- Report updated: U0 marked PAID, divides_one row added to the landed table.
- Remaining wrap-up: fix report's remaining-items list (item 1 references
  divides_one as next — update), amend the "sixteen leaves" phrasing if
  needed (now seventeen), commit report tweak, run final full gate, write
  final summary. No blockers.
- 693ba3e stretch chain landed: add_eq_zero (248 nodes, PRESBURGER),
  divides_step (681), divides_add_cancel (1073) — all checked. Full suite
  `1237 passed in 99.59s`, ruff+pyright clean.
- 51777f1 reports/formula2-bridge-debts.md committed: ledger honesty
  (empty-target debts unpayable by soundness), positivity requirement
  (Φ(0,0,c) true for all c≥1 in N ⇒ uniqueness false unrelativized), full
  lemma DAG (T1–T4, U0–U4, hard parts H1 Euclid / H2 order kit / H3 congruence
  solvability, none β-function grade), landed table with node counts + commits,
  path recommendation (compose into PEANO, relativize δ = positivity).
- Proof sizes measured: coprime_one_* ~5k, unit_case_unit 7067,
  product_divides_both 7520, crt_key_identity 16400, totality point 8061.
- NOW: extra leaf divides_one (a|1 → a=1) — red test edits to
  test_divisibility_proofs.py in progress (imports added, test body next).
  Plan: eigen k!, case k! zero/succ; succ arm cases a zero/succ; a=S(m!) arm:
  ADD_SUCC exposes S(a·j!+m!)=S(0), SUCC_INJ + add_eq_zero force m!=0.
  If smooth, consider divides_antisym (uses divides_one at witness product).
- No blockers.
- 45531e2 proofs: robinson_divisibility_proofs.py landed (9 leaf theorems +
  totality point), full suite `1234 passed in 109.87s`.
- Stretch chain in flight (T3 quotient extraction): red tests added for
  ADD_EQ_ZERO (test_presburger), DIVIDES_STEP + DIVIDES_ADD_CANCEL
  (test_divisibility_proofs); red confirmed (2 collection errors).
- add_eq_zero() implemented in proofs.py (case split on y via zero_or_succ +
  or_elim; succ arm contradicts SUCC_NEQ_ZERO) — `13 passed` test_presburger.py.
- Next: divides_step (a·k = b+a → a|b, case split on k; zero arm uses
  add_eq_zero, succ arm uses add_cancel_right) and divides_add_cancel
  (induction on c; step rearranges b+a·S(c) = (b+a·c)+a by prove_eq then
  applies divides_step instance, then IH) in divisibility.py. Then commit,
  then the report reports/formula2-bridge-debts.md.
- No blockers.
- 66d014b proofs: zero_or_succ landed (PRESBURGER-checked), `12 passed` test_presburger.py.
- 7c8e22b formula2: `via=` divisibility builder on all robinson_divisibility
  constructors; robinson_product(a,b,c, via=peano_divides) is now first-class;
  regression suite for bridges still green (`11 passed`).
- NEW MODULE cold_start/robinson_divisibility_proofs.py, all checked in PEANO,
  `6 passed` test_robinson_divisibility_proofs.py, ruff clean, pyright 0 errors
  (after `type(phi_one) is Implies` narrowing in test). Contents:
  COPRIME_ONE_LEFT/RIGHT (via divides_trans through 1), LCM_ONE_LEFT/RIGHT,
  LCM_SELF, UNIT_CASE_UNIT, UNIT_CASE_FORCES_UNIT_DIVISORS (ForallElim at 1),
  PRODUCT_DIVIDES_BOTH (staged Inst through "t!" to avoid variable clash),
  CRT_KEY_IDENTITY (mk=S(ax) -> ml=S(by) -> abxy+(mk+ml)=S(mk*ml); proved by
  Cong-folding both hyps around a poly_kit prove_eq of the pure semiring
  identity — deliberately NOT hypothesis_rule rewriting, since MUL_ASSOC would
  destroy the literal m*k redex), totality_witness_at_unit (∃c Φ(1,1,c),
  witness 1, unit disjunct via or_left).
- Not yet committed: new module + its test. Next: full suite run, commit,
  then stretch (divides_add_cancel / divides_one) or go straight to report.
- No blockers.
- c1dd166 proofs: divides_add + divides_mul_left landed in divisibility.py,
  `12 passed` test_divisibility_proofs.py, ruff+pyright clean.
- In flight: ZERO_OR_SUCC + zero_or_succ() added to proofs.py (induction on n;
  base = or_left + Refl(0), step = or_right + ExistsIntro witness n); red seen
  (collection ImportError in test_presburger.py); about to run green.
- proofs.py now imports prop (Or, or_left, or_right) — no cycle (prop imports
  only proof+syntax; robinson.py doesn't import proofs).
- 7a56430 prop: or_left/or_right/or_elim landed, `9 passed` in test_prop.py, ruff+pyright clean.
- In flight: divisibility.py divides_add (witness k+l via distrib_left) and
  divides_mul_left (witness k via mul_assoc); red confirmed (ImportError at collection);
  implementation written, about to run test_divisibility_proofs.py green, then gate+commit.
- Note: ExistsIntro checks `instantiate(claim, witness) == subproof.concl`; witness
  names "k!"/"l!" chosen to avoid capture; peano_divides internal binder name is "k"
  (never collides — alpha-equivalence makes names moot anyway).

## State
- test_prop.py extended with or_left/or_right/or_elim tests (red confirmed:
  collection ImportError), prop.py implementation just written; about to run green +
  ruff/pyright, then commit.
- Plan of commits: (1) prop or-kit; (2) divisibility divides_add + divides_mul_left;
  (3) zero_or_succ in proofs.py (check under PRESBURGER); (4) robinson_divisibility
  `via` param; (5) new cold_start/robinson_divisibility_proofs.py + tests (the leaf
  theorems above); (6) stretch lemmas if time; (7) reports/formula2-bridge-debts.md.
- No blockers yet. Do NOT touch notes-breakthrough*.md (other agents').
