# cold_start — working rules

A number-theory proof checker built from scratch on the **De Bruijn criterion**:
proof terms are inert, serializable data that claim nothing; one small *trusted*
`check(proof, theory)` re-derives the sequent. Trust lives only in `checker.py` +
each theory's axioms. `verify.py` re-checks proofs from JSON in a fresh process,
trusting nothing but the checker and the theory.

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
- **The trust gate is the one non-polymorphic exception.** `validate` /
  `validate_proof` must reject hostile *subclasses* (a `Var` with a lying `__eq__`, a
  `str` subclass, a forged mutable-args `Fun`). A method can be overridden by exactly
  the subclass it must reject, so the gate dispatches on **exact type** via a dict +
  reject-default, reading fields explicitly (never the reflective child-walk). It
  runs first; everything downstream then sees only canonical nodes.

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
