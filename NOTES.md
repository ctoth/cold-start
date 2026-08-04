# Working notes — cold-start

## What this is
Number theory from scratch in dependency-free Python, built on the **De Bruijn
criterion**: untrusted prover emits a serializable *proof term*; one small
trusted `check(proof, theory)` re-derives the sequent from inert data. Trust =
the verifier, not the object.

## Current state: DONE & GREEN
- pytest: **453 passed**
- Regression coverage includes exact-type subclass attacks, mutable-args
  aliasing, deep non-recursive traversal, hamblin byte round-trips, cross-process
  verification, quantifier rules, classical rules, many-sorted checking, model
  soundness probes, rings/monoids, Presburger/Peano, and the Robinson bridge.
- ruff check .: clean
- pyright (repo-rooted CLI, uses pyrightconfig.json): **0 errors, 0 warnings**
  (NOTE: the editor's inline Pyright is rooted at parent `code\` and ignores our
   pyrightconfig.json, so it shows bogus import-resolution errors. The CLI run
   is authoritative.)

## Layout
- `syntax.py`  — terms/formulas: Var/Fun/BVar, Eq/Implies/Bottom, locally
                 nameless Forall/Exists, `Not` sugar, structural operations,
                 exact-type validation, hamblin byte ser/deser. Not trusted.
- `proof.py`   — proof terms and rule methods: equality, implication,
                 induction, classical logic, quantifiers, to_bytes/from_bytes.
                 Not trusted as data; trusted only after the exact-type gate.
- `sequent.py` — plain Sequent data plus sort checking.
- `checker.py` — TRUSTED CORE: Signature, Theory, sort_check_formula, and
                 check() running validate_proof before proof derivation.
- `presburger.py` — 0/S/+ arithmetic with successor axioms and induction data.
- `peano.py`   — Presburger plus recursive multiplication axioms.
- `robinson.py` — `(1, S, ·)` Robinson arithmetic experiment eliminating `+`
                 into a definable bridge.
- `algebra.py` — monoids, rings, sorted monoid actions, and finite models.
- `notation.py` — untrusted human parser/formatter for terms and formulas.
- `tactics.py` — UNTRUSTED prover: matching, rewrite rules, normalization,
                 prove_eq, by_induction. Emits proof terms; has no authority.
- `proofs.py`  — worked proof constructors, by hand (left_identity_proof) and by
                 tactics (add_comm, add_assoc, ...).
- `verify.py`  — CLI: checks a binary proof in a SEPARATE process.
- `lean.py`    — untrusted Lean 4 compat layer: conditional-theorem export
                 (axioms as hypotheses, never `axiom`), statement-fragment
                 parser, lean_export/ColdStart.lean corpus — compiled by the
                 Lean 4 kernel as an independent check.
- `tests/`     — example/regression tests, property tests, model probes,
                 notation tests, quantifier/classical/sort/algebra coverage.
- `pyproject.toml` (ruff/pytest), `pyrightconfig.json`.

## History / decisions
1. Started LCF-style (opaque guarded Theorem). Q noted: non-frozen/no-slots
   bases -> fixed (commit fada2a2: __slots__=() on bases, slots=True dataclasses).
2. Q: `object.__new__(Theorem)` forges a theorem. Confirmed. Conclusion: opaque
   Theorem is unenforceable in Python (token/ctypes/monkeypatch all forge).
   Decided to build the principled De Bruijn version instead.
3. Q: rules duck-type premises + trust `==`; a lying Term/str **subclass**
   __eq__ derives 1 = 0 from reflexivity. CONFIRMED against new checker
   (`Trans(Refl(S0), Trans(Refl(Evil), Refl(0)))` -> `|- S(0)=0`).
   FIX: exact-type validate_* + single up-front validate_proof pass (answering
   Q's "decorator?" — lifted validation out of bodies entirely). Now REJECTED
   ("non-canonical term: Evil"); real proof still checks.
4. Q: stop ad-hoc one-liners, use TDD. Captured every claim as a regression
   test, incl. both attacks as permanent sentinels + cross-process subprocess.
5. Q (reading old kernel.py): implies_intro's `hyps - {hyp}` frozenset
   subtraction trusts __hash__/__eq__; a malicious formula can hash+compare
   equal to a real hypothesis and strip it -> discharge an unproved assumption.
   Real in the OLD version. In the NEW version it's ALREADY closed: every
   formula reaching a set op came via Assume (validated) or is ImpIntro.hyp
   (validated), so all are exact-type canonical with honest hash/eq.
   Proved with 2 new tests (test_lying_formula_*), incl. a sanity assertion
   that the malicious formula really strips h (so the sentinel isn't vacuous).

## Soundness model (current)
Trusted base = the exact-type gates and rule/sort-checking methods in
`syntax.py`, `proof.py`, `sequent.py`, and `checker.py`, plus each Theory's
concrete axioms and induction data. Serialized path decodes hamblin bytes into
canonical nodes. In-process path is protected by exact-type validation before
equality, hashing, or rule methods are trusted.

## Next step (not started)
- `n + 0 = 0 + n` -> commutativity of `+`, then associativity. First proof that
  exercises nested induction.
- Possible: proof-term pretty-printer; non-trusted tactics layer emitting Pf.

## Blockers
None.
