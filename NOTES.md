# Working notes — cold-start

## What this is
Number theory from scratch in dependency-free Python, built on the **De Bruijn
criterion**: untrusted prover emits a serializable *proof term*; one small
trusted `check(proof, theory)` re-derives the sequent from inert data. Trust =
the verifier, not the object.

## Current state: DONE & GREEN
- pytest: **23 passed** (+2 for the term-args aliasing attack)
- Attack #6 (Q): `Fun("f", list)` aliases a mutable list into a term; mutating
  it later retroactively rewrites a proved term. Fixed two ways: Fun.__post_init__
  snapshots args to a tuple (immutable by construction), AND validate_term's
  exact `type(args) is tuple` is the backstop against object.__new__ bypass.
  Tests: test_term_args_snapshotted_*, test_forged_fun_with_mutable_args_rejected.
- ruff check .: clean
- pyright (repo-rooted CLI, uses pyrightconfig.json): **0 errors, 0 warnings**
  (NOTE: the editor's inline Pyright is rooted at parent `code\` and ignores our
   pyrightconfig.json, so it shows bogus import-resolution errors. The CLI run
   is authoritative.)

## Layout
- `syntax.py`  — language: Var/Fun, Eq/Implies, free_vars/subst, EXACT-type
                 `validate_term`/`validate_formula`, JSON ser/deser. Not trusted.
- `proof.py`   — proof terms (Axiom/Assume/Refl/Sym/Trans/Cong/MP/ImpIntro/
                 Inst) + to_json/from_json. Not trusted.
- `checker.py` — TRUSTED CORE (~190 lines): Sequent, Theory, validate_proof
                 (one up-front structural pass), check(), pure `_derive`.
- `peano.py`   — theory: 0/S/+, ADD_ZERO_F, ADD_SUCC_F, is_induction_instance
                 recognizer, PEANO, induction() builder.
- `proofs.py`  — left_identity_proof(): 0 + n = n by induction.
- `verify.py`  — CLI: checks a JSON proof in a SEPARATE process.
- `test_checker.py` — 19 tests.
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
   STATUS: not yet committed -- commit next.

## Soundness model (current)
Trusted base = checker.py (validate_proof + _derive) + each Theory's axioms and
schema recognizers. Serialized path immune by construction (from_dict only mints
Var/Fun). In-process path now immune via exact-type validation.

## Next step (not started)
- `n + 0 = 0 + n` -> commutativity of `+`, then associativity. First proof that
  exercises nested induction. (Alternatively: add `Not` to state 0 != S(x) and
  successor injectivity.)
- Possible: proof-term pretty-printer; non-trusted tactics layer emitting Pf.

## Blockers
None.
