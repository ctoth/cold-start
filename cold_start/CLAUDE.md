# cold_start — working rules

A number-theory proof checker built from scratch on the **De Bruijn criterion**:
proof terms are inert, serializable data that claim nothing; one small *trusted*
`check(proof, theory)` re-derives the sequent. Trust is the checking code -- the
exact-type gates plus the syntax/sequent validation methods they guard and the
exhaustive proof validation and rule semantics in `checker.py` -- plus each
theory's axioms. `codec.py` owns the one hand-rolled, dependency-free wire
format -- uvarint- and length-prefixed bytes over canonical syntax and proof DAG
tables, reachable only through a versioned `CSPC` certificate; `verify.py`
resolves the artifact's embedded theory,
checks its semantic fingerprint and exact claim, and re-checks the proof in a
fresh process.

## Design rules
- **Proof values stay inert.** Proof nodes are frozen dataclasses with no
  validation or derivation behavior. `checker.py` owns the exact, exhaustive
  proof-type dispatch for both local validation and rule semantics. Syntax
  operations remain guarded methods where their intrinsic structure owns the
  operation. External adapters use exhaustive exact-type dispatch derived from
  the canonical owner sets.
- **One `Node` root** for terms and formulas. `Term`/`Formula` are thin markers
  under it. `Node` carries the generic child-recursion; only `Var` and the binders
  (`Forall`/`Exists`) override.
- **The scope is one concept.** A stack pushed under each binder, indexed by `BVar`.
  Its payload varies by operation — nothing (`validate`), a value (`evaluate`), a
  term (`instantiate`), a **sort** (sort-checking) — but it is one structure. This is
  how sorts and quantifiers coexist: sort-checking threads bound-variable sorts
  through `Forall`/`Exists`.
- **The trust gate rejects before behavior.** `validate` / `validate_proof` must
  reject hostile *subclasses* (a `Var` with a lying `__eq__`, a `str` subclass, a
  forged mutable-args `Fun`). Syntax validates through the exact-type gate before
  invoking canonical syntax methods. Proof validation and derivation remain one
  reject-default dispatch in `checker.py`; no method on an attacker-controlled
  proof object is invoked.
- **Derivation is central; human notation is external.** `check()` validates the
  selected theory, validates the whole exact proof graph, and applies the rule
  semantics in `checker.py`. Proof construction alone claims nothing. Human
  notation lives in `notation.py`, and the Lean and wire representations remain
  downstream adapters. `Sequent` lives in `sequent.py` as an inert result value
  with intrinsic sort validation.

## Process rules
- **Commit after every green step.** Never leave verified work uncommitted — a
  `git reset` must not be able to lose it. (It has, once.)
- **Verify before claiming.** Run the test; quote the summary line. "I didn't run
  it" ⇒ not done. Confidence is not evidence.
- **Delete-first refactors.** No shims (a 1-line function that only forwards to a
  method is a shim — don't add it; migrating a call site to the method is not). No
  unrequested `__init__` re-exports — `cold_start` is a namespace package.
- **Tests are the spec.** Change them only to improve the API while preserving every
  asserted property, and add tests for every new behavior (red-first: see it fail,
  then make it pass).
- `uv` for everything (`uv run pytest|ruff|pyright`); Windows shell.
- **Never use AskUserQuestion** — its UI is inaccessible to Q. Ask in prose, or
  decide from the plan's defaults.
