# cold_start — working rules

A number-theory proof checker built from scratch on the **De Bruijn criterion**:
proof terms are inert, serializable data that claim nothing; one small *trusted*
`check(proof, theory)` re-derives the sequent. Trust is the checking code -- the
exact-type gates plus the `_validate`/`derive`/`sort_check` methods they guard
(in `syntax.py`, `proof.py`, `sequent.py`) driven by `checker.py` -- plus each
theory's axioms. `verify.py` re-checks proofs from hamblin bytes in a fresh process,
trusting nothing but that checking code and the theory.

## Design rules
- **Polymorphism over type-switches.** Operations over the syntax/proof tree are
  *methods*, dispatched by Python on the node's class. An `elif type(x) is A …`
  chain that walks the tree is a *smell to refactor into a method* — not a banned
  keyword. A parser's local conditionals are fine; exact-type `dict` dispatch is the
  right tool at the trust gate.
- **One `Node` root** for terms and formulas. `Term`/`Formula` are thin markers
  under it. `Node` carries the generic child-recursion; only `Var` and the binders
  (`Forall`/`Exists`) override.
- **The scope is one concept.** A stack pushed under each binder, indexed by `BVar`.
  Its payload varies by operation — nothing (`validate`), a value (`evaluate`), a
  term (`instantiate`), a **sort** (sort-checking) — but it is one structure. This is
  how sorts and quantifiers coexist: sort-checking threads bound-variable sorts
  through `Forall`/`Exists`.
- **The trust gate guards the methods; it is not a dispatch table.** `validate` /
  `validate_proof` must reject hostile *subclasses* (a `Var` with a lying `__eq__`, a
  `str` subclass, a forged mutable-args `Fun`). A method can be overridden by exactly
  the subclass it must reject -- so the gate is a one-line **exact-type check**
  (`type(x) in _CANONICAL` / `_PROOF_TYPES`, reject-default) placed *in front of* the
  node's own `_validate` method. The per-type field checks stay polymorphic methods
  (`node._validate(depth)`, `pf._validate()`); the gate just confirms the exact type
  is canonical before any method runs, then each method recurses through the same
  gate. It runs first; everything downstream then sees only canonical nodes. This
  keeps the security property (no hostile method runs) without a pile of per-type
  handler functions -- those were shims; the logic belongs on the node.
- **Derivation is a method; human notation is not.** A proof term checks *itself*:
  `pf.derive(theory)` re-derives its sequent after the gate. "Inert data" means a
  `Pf` carries no pre-made theorem -- you can build nonsense -- not that the class
  has no methods; the methods are trusted code an adversary cannot override past
  the gate. Human notation printing lives in `notation.py`, alongside parsing, so
  presentation state does not leak into syntax nodes. `Sequent` lives in
  `sequent.py` so the proof methods can return/recurse on it without an import
  cycle.

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
