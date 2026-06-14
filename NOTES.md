# Working notes — De Bruijn refactor

## Goal
Rebuild the prover around the **De Bruijn criterion**: untrusted prover emits an
inert, serializable *proof term*; one small trusted `check(proof, theory)`
re-derives the conclusion. Trust moves from "Theorem object was kernel-minted"
(unenforceable in Python: `object.__new__`, token reach, monkeypatch all forge
it) to "check() re-ran the recipe." Also: real `isinstance` validation on the
inert proof data (it can be malformed/hostile post-deserialization).

## Target layout
- `syntax.py`   — language: Term/Var/Fun, Formula/Eq/Implies, free_vars/subst,
                  to_dict/from_dict. NOT trusted. **DONE.**
- `proof.py`    — proof-term nodes (Axiom/Assume/Refl/Sym/Trans/Cong/MP/
                  ImpIntro/Inst), frozen+slots, JSON ser/deser. **TODO.**
- `checker.py`  — TRUSTED. `Sequent`, `Theory(axioms, schemas)`,
                  `check(proof, theory) -> Sequent`. isinstance-heavy. **TODO.**
- `peano.py`    — signature (ZERO/S/add/numeral), axiom formulas ADD_ZERO_F /
                  ADD_SUCC_F, `is_induction_instance` recognizer, `PEANO`
                  theory, `induction(...)` proof builder. **TODO (rewrite).**
- `proofs.py`   — `left_identity_proof()` returns a Pf. **TODO (rewrite).**
- `verify.py`   — CLI: load JSON proof, check vs PEANO, print sequent / exit. **TODO.**
- tests         — replace test_kernel.py with test_checker.py. **TODO.**
- delete old `kernel.py`. **TODO.**

## Key design decisions
- Checker is generic FOL+equality; theory-agnostic. Axioms passed in.
- Induction is an **axiom schema**: `Theory` carries `schemas` (recognizer
  predicates). `is_induction_instance(f)` structurally matches
  `P[0] -> ((P -> P[S x]) -> P)`, finds x by scanning free vars of P.
  The recognizer is part of the trusted theory definition (small, auditable).
- `induction()` builds `MP(MP(Axiom(schema), base), step)`; checker validates
  via MP antecedent matching + schema acceptance.
- Sequent is plain data with NO construction guard — that's the point: holding
  one proves nothing; only `check()` returning it is authority.

## Checker rule semantics (mirror of old kernel)
Axiom(f): theory.accepts(f); ∅⊢f. Assume(f): {f}⊢f. Refl(t): ∅⊢t=t.
Sym/Trans/Cong on equalities. MP: antecedent must match. ImpIntro: remove hyp.
Inst: var not free in any hyp (guard).

## Status
syntax.py, proof.py, checker.py, peano.py, proofs.py, verify.py all written.

### MAJOR soundness finding (Q caught it)
`refl` + any rule using Python `==` trusts `__eq__`. A hostile Term/str
**subclass** can override `__eq__` to return True and derive `1 = 0` from
reflexivity. CONFIRMED against the new checker:
  `Trans(Refl(S0), Trans(Refl(Evil()), Refl(0)))` -> accepted `|- S(0) = 0`.
The serialized path was already immune (from_dict only mints Var/Fun); the
in-process hand-built path was not.

### Fix applied
Added `validate_term`/`validate_formula` in syntax.py using EXACT type checks
(`type(x) is Var`, not isinstance — subclasses ARE the attack), recursing into
args and str fields. Then (answering Q's "decorator?" nudge) lifted validation
out of the rule bodies into ONE up-front `validate_proof(pf)` pass in
checker.py. New shape:
  - `validate_proof(pf)`  — structural well-formedness, once.
  - `check(pf, theory)`   — validate_proof then `_derive`.
  - `_derive(pf, theory)` — pure logic, recurses on itself, trusts `==`.
Separates "well-formed proof term?" from "valid derivation?".

## TODO before commit
- [ ] Re-run the Evil-term attack: must now be REJECTED.
- [ ] Write test_checker.py (rules, attack rejection, serialization roundtrip,
      cross-process verify.py subprocess, unknown-axiom rejection).
- [ ] Delete old kernel.py + test_kernel.py.
- [ ] Add pyproject.toml / pyrightconfig.json (fix import-resolution noise;
      all current Pyright errors are that cascade, not real bugs).
- [ ] Update README (check off proof terms; document trust model + this attack).
- [ ] Run full suite, commit.

## Blocker
None.
